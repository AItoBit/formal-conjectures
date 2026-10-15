"""Build the attributed proof and audit the exact statement bridges and witness."""
from pathlib import Path
import os
import re
import subprocess

ROOT = Path(__file__).resolve().parent
EXPECTED = [
    'Erdos639.SimpleGraph.erdos639',
    'Erdos639FC.frozen_repository_clause',
    'Erdos639FC.bound_ten',
    'Erdos639Six.sixColoring_uncovered_count',
    'Erdos639Six.six_counterexample',
]
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}

def run(command, name):
    env = dict(os.environ)
    env['LEAN_NUM_THREADS'] = '1'
    with (ROOT / name).open('w', encoding='utf8') as log:
        result = subprocess.run(command, cwd=ROOT, env=env, stdout=log, stderr=subprocess.STDOUT)
    if result.returncode:
        raise SystemExit(f'Command failed; inspect {name}')
    return (ROOT / name).read_text(encoding='utf8')

def main():
    output = run(['lake', '--wfail', 'build', 'Bridge639'], 'build.log')
    output += run(['lake', 'env', 'lean', 'SmallSix639.lean'], 'six-axioms.log')
    # A cached Lake build need not replay informational axiom messages.
    output += run(['lake', 'env', 'lean', 'Bridge639.lean'], 'bridge-axioms.log')
    for name in EXPECTED:
        match = re.search(re.escape("'" + name + "' depends on axioms: [") + r'([^]]*)\]', output)
        if not match:
            raise SystemExit('Missing axiom report: ' + name)
        actual = {x.strip() for x in match.group(1).split(',') if x.strip()}
        if not actual <= ALLOWED:
            raise SystemExit('Unexpected axioms for ' + name + ': ' + repr(actual))
    print('PASS: n>=10 bound, exact eventual clause, and six-vertex witness; standard axioms only')

if __name__ == '__main__':
    main()
