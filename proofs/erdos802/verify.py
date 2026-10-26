"""Serial, source-pinned Lean verification; --fresh ignores local build receipts."""
from pathlib import Path
import hashlib,json,os,re,subprocess,sys,time
p=Path(__file__).resolve().parent
manifest=json.loads((p/'source-provenance.json').read_text(encoding='utf-8'))
expected_mathlib='d13f23b723b8a846827a245b89c10fc7d3f11612'
version=subprocess.check_output(['lean','--version'],cwd=p,text=True).strip()
if not re.search(r'version\s+4\.34\.1(?:[,\s])',version):raise SystemExit('Wrong Lean: '+version)
actual=subprocess.check_output(['git','rev-parse','HEAD'],cwd=p/'.lake/packages/mathlib',text=True).strip()
if actual!=expected_mathlib:raise SystemExit('Wrong Mathlib: '+actual)
for entry in manifest['sources']:
    source=p/(entry['module'].replace('.','/')+'.lean')
    if hashlib.sha256(source.read_bytes()).hexdigest()!=entry['sha256']:
        raise SystemExit('Original source hash mismatch: '+str(source))
modules=list(manifest['topological_order'])
upstream_only='--upstream-only' in sys.argv
if not upstream_only:modules+=['FCDefinitions802','Variants802','Bridge802','Results802']
lib=p/'.lake/build/lib/lean';lib.mkdir(parents=True,exist_ok=True)
env=os.environ.copy()
env['LEAN_PATH']=os.pathsep.join(map(str,[lib]+[x/'.lake/build/lib/lean'
    for x in sorted((p/'.lake/packages').iterdir()) if x.is_dir()]))
state_file=p/'verification-state.json'
state=json.loads(state_file.read_text(encoding='utf-8')) if state_file.exists() else {}
keys={};results=[];logs=p/'.verify-logs';logs.mkdir(exist_ok=True)
for i,module in enumerate(modules):
    source=p/(module.replace('.','/')+'.lean');data=source.read_bytes();text=data.decode('utf-8')
    if re.search(r'\b(?:sorry|admit|axiom|unsafe|native_decide)\b',text):
        raise SystemExit('Forbidden construct: '+module)
    deps=re.findall(r'^(?:public\s+)?import\s+([\w.]+)',text,re.M)
    local={x:keys[x] for x in deps if not x.startswith(('Mathlib','Lean'))}
    key=hashlib.sha256(json.dumps(dict(source=hashlib.sha256(data).hexdigest(),
        dependencies=local,lean=version,mathlib=actual,autoImplicit=False),sort_keys=True).encode()).hexdigest()
    target=lib/(module.replace('.','/')+'.olean');target.parent.mkdir(parents=True,exist_ok=True)
    old=state.get(module,{});artifacts=old.get('artifacts',{})
    unchanged=old.get('key')==key and artifacts and all((p/x).exists() and
        hashlib.sha256((p/x).read_bytes()).hexdigest()==h for x,h in artifacts.items())
    if unchanged and '--fresh' not in sys.argv:
        print('Checked receipt',i+1,'/',len(modules),module,flush=True)
        row=dict(module=module,key=key,cached=True,exit_code=0)
    else:
        print('Compiling',i+1,'/',len(modules),module,flush=True);start=time.time()
        command=['lean','-DautoImplicit=false','-o',str(target),str(source.relative_to(p))]
        result=subprocess.run(command,cwd=p,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        output=result.stdout.decode('utf-8',errors='replace')
        (logs/(module+'.log')).write_text(output,encoding='utf-8',newline='\n')
        row=dict(module=module,key=key,cached=False,exit_code=result.returncode,
            seconds=round(time.time()-start,2),command=command)
        if result.returncode or 'warning:' in output:
            print(output,flush=True);raise SystemExit('FAILED: '+module)
        artifacts={x.relative_to(p).as_posix():hashlib.sha256(x.read_bytes()).hexdigest()
            for x in target.parent.glob(target.name+'*') if x.is_file()}
        state[module]=dict(key=key,artifacts=artifacts,exit_code=0,source_sha256=hashlib.sha256(data).hexdigest())
        state_file.write_text(json.dumps(state,indent=2)+'\n',encoding='utf-8')
        print('Passed',module,row['seconds'],'seconds',flush=True)
    keys[module]=key;results.append(row)
    (p/'verification-run.json').write_text(json.dumps(results,indent=2)+'\n',encoding='utf-8')
print('All',len(modules),'source modules PASSED.',flush=True)
if upstream_only:raise SystemExit(0)
audit=p/'Audit802.lean'
for candidate in [audit,p/'FCDefinitions802.lean',p/'Variants802.lean',p/'Bridge802.lean',p/'Results802.lean']:
    if re.search(r'\b(?:sorry|admit|axiom|unsafe|native_decide)\b',candidate.read_text(encoding='utf-8')):
        raise SystemExit('Forbidden construct: '+str(candidate))
with (p/'axiom-report.txt').open('wb') as out:
    result=subprocess.run(['lean','-DautoImplicit=false',str(audit.relative_to(p))],cwd=p,env=env,stdout=out,stderr=subprocess.STDOUT)
if result.returncode:raise SystemExit('FAILED: axiom audit')
text=(p/'axiom-report.txt').read_text(encoding='utf-8')
reports=re.findall(r'depends on axioms: \[([^]]*)\]',text)
count=len(reports)+text.count('does not depend on any axioms')
if count!=5:raise SystemExit('Expected5axiomreports, got'+str(count))
for report in reports:
    if set(x.strip() for x in report.split(',') if x.strip())-{'propext','Classical.choice','Quot.sound'}:
        raise SystemExit('Unexpected axiom: '+report)
print('Full802target and all four variants PASSED;5 axiom audits, standard foundations only.',flush=True)

