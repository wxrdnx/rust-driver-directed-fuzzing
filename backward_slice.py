import argparse

def read_jsonl(path):
    records = []
    with open(path) as file:
        for line in file:
            if line.strip():
                records.append(json.loads(line))
    return records

def slice_function(function, dataflow, target):
    pass

def analyze(cfg_path, dataflow_path, target_path, output_path):
    cfgs = read_jsonl(cfg_path)
    dataflows = read_jsonl(dataflow_path)

    with open(target_path) as file:
        target_data = json.load(file)
    targets = target_data.get('targets', target_data.get('panic_sites', []))

    dataflow_by_function = {}
    for dataflow in dataflows:
        dataflow_by_function[dataflow['function']['id']] = dataflow

    slices = []
    for target in targets:
        for function in cfgs:
            if function['function']['name'] != target['function']:
                continue
            function_id = function['function']['id']
            if function_id not in dataflow_by_function:
                continue
            result = slice_function(function, dataflow_by_function[function_id], target)
            if result:
                slices.append(result)

if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('cfg')
    parser.add_argument('dataflow')
    parser.add_argument('targets')
    parser.add_argument('output')
    args = parser.parse_args()
    analyze(args.cfg, args.dataflow, args.targets, args.output)
