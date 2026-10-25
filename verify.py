from pathlib import Path
import re,subprocess,sys
p=Path(__file__).resolve().parent
subprocess.run([sys.executable,str(p/'prepare.py')],cwd=p,check=True)
for source in p.glob('*.lean'):
    if re.search(r'\b(?:sorry|admit|axiom|unsafe|native_decide)\b',source.read_text(encoding='utf-8')):
        raise SystemExit('Forbidden proof construct in '+source.name)
for cmd,log in [(['lake','--wfail','build'],'build.log'),(['lake','env','lean','Audit797.lean'],'axiom-report.txt')]:
    with (p/log).open('w',encoding='utf-8') as out:
        result=subprocess.run(cmd,cwd=p,stdout=out,stderr=subprocess.STDOUT)
    if result.returncode:raise SystemExit('FAILED: '+log)
text=(p/'axiom-report.txt').read_text(encoding='utf-8')
reports=re.findall(r'depends on axioms: \[([^]]*)\]',text)
if len(reports)!=25:raise SystemExit('Expected25axiomreports, got'+str(len(reports)))
for report in reports:
    if set(x.strip() for x in report.split(',') if x.strip())-{'propext','Classical.choice','Quot.sound'}:
        raise SystemExit('Unexpected axiom: '+report)
print('Complete797proof, bothrealbounds, exact-statementbridge and25axiomaudits PASSED.')
