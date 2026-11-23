import argparse
import json

from backward_slice import build_program_index, read_jsonl
from expression_resolver import expression_impact_report

def analyze(cfg_path, dataflow_path, target_path, output_path):
    functions = read_jsonl(cfg_path)
    dataflows = read_jsonl(dataflow_path)
    with open(target_path) as file:
        target_data = json.load(file)
    targets = target_data.get('targets')
    if targets is None:
        targets = target_data.get('panic_sites', [])
    indexes, _ = build_program_index(functions, dataflows)
    report = expression_impact_report(indexes, targets)
    with open(output_path, 'w') as output:
        json.dump(report, output, indent=2)
        output.write('\n')
    return True

if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('cfg')
    parser.add_argument('dataflow')
    parser.add_argument('targets')
    parser.add_argument('output')
    args = parser.parse_args()
    analyze(args.cfg, args.dataflow, args.targets, args.output)
