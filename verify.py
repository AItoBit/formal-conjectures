from pathlib import Path
import re, subprocess, sys
p = Path(__file__).resolve().parent
subprocess.run([sys.executable, str(p/'prepare.py')], cwd=p, check=True)
for cmd, logfile in [(['lake', '--wfail', 'build'], 'build.log'),
                     (['lake','env','lean','Audit795.lean'], 'axioms-original.txt'),
                     (['lake','env','lean','AuditBridge795.lean'], 'axioms-bridge.txt')]:
    with (p/logfile).open('w', encoding='utf-8') as out:
        result = subprocess.run(cmd, cwd=p, stdout=out, stderr=subprocess.STDOUT)
    if result.returncode: raise SystemExit('FAILED: '+logfile)
for name in ['axioms-original.txt','axioms-bridge.txt']:
    text=(p/name).read_text(encoding='utf-8')
    reports=re.findall(r'depends on axioms: \[([^]]*)\]', text)
    if len(reports)!=4: raise SystemExit('Missing axiom reports: '+name)
    for report in reports:
        if set(x.strip() for x in report.split(',') if x.strip()) - {'propext','Classical.choice','Quot.sound'}:
            raise SystemExit('Unexpected axiom: '+report)
print('Complete proof and exact-statement bridge verified; standard axioms only.')
