from pathlib import Path
import re,subprocess,sys
p=Path(__file__).resolve().parent
subprocess.run([sys.executable,str(p/'prepare.py')],cwd=p,check=True)
sources=list(p.glob('*.lean'))+list((p/'ErdosProblems').rglob('*.lean'))+list((p/'Util').rglob('*.lean'))
for source in sources:
    if re.search(r'\b(?:sorry|admit|axiom|unsafe|native_decide)\b',source.read_text(encoding='utf-8')):
        raise SystemExit('Forbidden proof construct: '+str(source))
commands=[(['lake','--wfail','build'],'build.log'),(['lake','env','lean','Audit799.lean'],'axiom-report.txt'),(['lake','env','lean','AuditBridge799.lean'],'bridge-axioms.txt'),(['lake','env','lean','AuditProportion799.lean'],'api-axioms.txt')]
count=0
for cmd,log in commands:
    with (p/log).open('w',encoding='utf-8') as out:
        result=subprocess.run(cmd,cwd=p,stdout=out,stderr=subprocess.STDOUT)
    if result.returncode:raise SystemExit('FAILED: '+log)
    if 'axiom' in log:
        text=(p/log).read_text(encoding='utf-8')
        reports=re.findall(r'depends on axioms: \[([^]]*)\]',text)
        audited=len(reports)+text.count('does not depend on any axioms')
        if not audited:raise SystemExit('Missing axiom reports: '+log)
        count+=audited
        for report in reports:
            if set(x.strip() for x in report.split(',') if x.strip())-{'propext','Classical.choice','Quot.sound'}:
                raise SystemExit('Unexpected axiom: '+report)
if count!=23:raise SystemExit('Expected23axiomreports, got'+str(count))
print('Complete799proof, exactcurrentdefinitionbridge, and',count,'axiom audits PASSED.')
