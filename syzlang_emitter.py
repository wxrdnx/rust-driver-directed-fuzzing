import argparse
import json
import os
import sys
import subprocess
import tempfile
import urllib.request

RESULT_SCHEMA = {
    'type': 'object',
    'properties': {
        'analysis': {'type': 'string'},
        'description': {'type': 'string'},
        'enable_syscalls': {'type': 'array', 'minItems': 1, 'items': {'type': 'string'}},
        'limitations': {'type': 'array', 'items': {'type': 'string'}},
    },
    'required': ['analysis', 'description', 'enable_syscalls', 'limitations'],
    'additionalProperties': False,
}

def read_json(path):
    with open(path) as file:
        return json.load(file)

def target_record(report, target_id):
    for record in report['targets']:
        if record['target']['id'] == target_id:
            return record

def build_context(constraints, solutions, target_id, descriptions):

    # The context fed into LLM include
    # - target constraint
    # - solver result
    # - existing Syzlang

    constraint = target_record(constraints, target_id)
    solution = target_record(solutions, target_id)
    if constraint is None or solution is None:
        return None

    context = {
        'target': constraint['target'],
        'constraint': constraint['constraint'],
        'solution': solution['result'],
        'relevant_syzlang': {},
    }

    for path in descriptions:
        with open(path) as file:
            context['relevant_syzlang'][os.path.basename(path)] = file.read()
    return context

def call_llm(prompt, api_base, api_key, model, timeout):
    prompt_path = 'syzlang_system_prompt.txt'

    with open(prompt_path) as file:
        system_prompt = file.read()
    body = {
        'model': model,
        'input': [{'role': 'system', 'content': system_prompt}, {'role': 'user', 'content': prompt}],
        'text': {'format': {'type': 'json_schema', 'name': 'targeted_syzlang', 'strict': True, 'schema': RESULT_SCHEMA}},
    }

    request = urllib.request.Request(api_base.rstrip('/') + '/responses', data=json.dumps(body).encode(), method='POST', headers={'Authorization': 'Bearer ' + api_key, 'Content-Type': 'application/json'})
    try:
        with urllib.request.urlopen(request, timeout=timeout) as response:
            result = json.load(response)
    except Exception as e:
        print(f'OpenAI request failed: {e}')
        return None

    for output in result.get('output', []):
        for content in output.get('content', []):
            if content.get('type') == 'output_text':
                return json.loads(content['text'])

def validate_result(result, syzkaller, target, validator):
    with tempfile.TemporaryDirectory(prefix='syzlang-emitter-') as directory:
        candidate = os.path.join(directory, 'description.txt')
        enabled = os.path.join(directory, 'enable-syscalls.json')
        with open(candidate, 'w') as file:
            file.write(result['description'].strip() + '\n')
        with open(enabled, 'w') as file:
            json.dump(result['enable_syscalls'], file)

        validator = os.path.relpath(validator, syzkaller)

        # TODO: currently the validator is an LLM-generated Golang validator
        process = subprocess.run(['go', 'run', validator, '.', target, candidate, enabled], cwd=syzkaller, capture_output=True, text=True, timeout=120)
    if process.returncode:
        error = process.stderr.strip() or process.stdout.strip()
        return False, error

    return True, None

def generate(context, output_dir, syzkaller, target, validator, api_base, api_key, model, timeout, attempts, llm=call_llm):
    prompt = '## Static analysis context\n\n' + json.dumps(context, indent=2)
    feedback_path = 'syzlang_validator_feedback.txt'
    with open(feedback_path) as file:
        feedback = file.read()
    history = []

    # Validation and repair loop
    for attempt in range(1, attempts + 1):
        result = llm(prompt, api_base, api_key, model, timeout)
        if result is None:
            return False
        valid, error = validate_result(result, syzkaller, target, validator)
        history.append({'attempt': attempt, 'result': result, 'validation_error': error})
        if valid:
            os.makedirs(output_dir, exist_ok=True)
            with open(os.path.join(output_dir, 'generation-context.json'), 'w') as file:
                json.dump(context, file, indent=2)
                file.write('\n')
            with open(os.path.join(output_dir, 'generation.json'), 'w') as file:
                json.dump(result, file, indent=2)
                file.write('\n')
            with open(os.path.join(output_dir, 'restricted-description.txt'), 'w') as file:
                file.write(result['description'].strip() + '\n')
            with open(os.path.join(output_dir, 'enable-syscalls.json'), 'w') as file:
                json.dump(result['enable_syscalls'], file, indent=2)
                file.write('\n')
            with open(os.path.join(output_dir, 'attempts.json'), 'w') as file:
                json.dump(history, file, indent=2)
                file.write('\n')
            return True

        # Construct the feedback prompt
        # Including the original prompt, previous result, and validation error
        prompt = feedback.format(prompt=prompt, result=json.dumps(result, indent=2), error=error)

    os.makedirs(output_dir, exist_ok=True)
    with open(os.path.join(output_dir, 'attempts.json'), 'w') as file:
        json.dump(history, file, indent=2)
        file.write('\n')

    return False

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('constraints')
    parser.add_argument('solutions')
    parser.add_argument('target_id')
    parser.add_argument('output_dir')
    parser.add_argument('--description', action='append', required=True)
    parser.add_argument('--syzkaller', default='syzkaller-src')
    parser.add_argument('--target', default='linux/amd64')
    parser.add_argument('--api-base', default='https://api.openai.com/v1')
    parser.add_argument('--model', default=os.getenv('OPENAI_MODEL', 'gpt-5'))
    parser.add_argument('--timeout', type=int, default=300)
    parser.add_argument('--attempts', type=int, default=3)
    args = parser.parse_args()

    descriptions = []
    for path in args.description:
        descriptions.append(path)

    context = build_context(read_json(args.constraints), read_json(args.solutions), args.target_id, descriptions)

    if context is None:
        print(f'target {args.target_id} missing from the analysis results')
        sys.exit(1)

    api_key = os.getenv('OPENAI_API_KEY')
    if not api_key:
        print('OPENAI_API_KEY not set')
        sys.exit(1)

    success = generate(context, args.output_dir, args.syzkaller, args.target,  'syzlang_validator.go', args.api_base, api_key, args.model, args.timeout, args.attempts)
    if not success:
        sys.exit(1)

if __name__ == '__main__':
    main()
