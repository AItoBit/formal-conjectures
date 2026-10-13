"""Compile the exact submitted declaration using only its proved shared dependency."""
import hashlib
import json
from pathlib import Path
import re
import sys

names = [
    'SimpleGraph.CliqueFree.mycielski',
    'SimpleGraph.cliqueNum_mycielski',
    'SimpleGraph.chromaticNumber_mycielski',
    'SimpleGraph.exists_cliqueNum_eq_two_chromaticNumber_eq',
    'Erdos627.erdos_627.variants.tutte_zykov',
]
if '--check-log' in sys.argv:
    text = Path('axioms.log').read_text(encoding='utf-8')
    matches = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text)
    assert {name for name, _ in matches} == set(names), matches
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    for name, axioms in matches:
        actual = {a.strip() for a in axioms.split(',') if a.strip()}
        assert actual <= allowed, (name, actual)
    print('PASS: all five principal declarations use only standard axioms.')
else:
    proof_path = Path('FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Mycielski.lean')
    target_path = Path('FormalConjectures/ErdosProblems/627.lean')
    source = target_path.read_text(encoding='utf-8')
    start = source.index('theorem erdos_627.variants.tutte_zykov :')
    end = source.index('\n\n', start)
    declaration = source[start:end]
    assert 'sorry' not in declaration
    text = ('import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Mycielski\n\n'
            'open SimpleGraph\n\nnamespace Erdos627\n\n' + declaration
            + '\n\nend Erdos627\n\n'
            + '\n'.join('#print axioms ' + name for name in names) + '\n')
    Path('ExactTargetAudit.lean').write_text(text, encoding='utf-8')
    manifest = {'exact_declaration': declaration, 'sources': {
        str(p): hashlib.sha256(p.read_bytes()).hexdigest()
        for p in (proof_path, target_path)}}
    Path('audit-manifest.json').write_text(json.dumps(manifest, indent=2), encoding='utf-8')
    print(json.dumps(manifest, indent=2))
