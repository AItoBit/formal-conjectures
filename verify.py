from pathlib import Path
import subprocess,re
p=Path(__file__).resolve().parent
for name in ['Construction791','Endpoint791','Main791']:
    source=(p/(name+'.lean')).read_text(encoding='utf-8')
    assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',source)
    target=p/'.lake/build/lib/lean'/(name+'.olean')
    target.parent.mkdir(parents=True,exist_ok=True)
    r=subprocess.run(['lake','env','lean',name+'.lean','-o',str(target)],cwd=p,text=True,encoding='utf-8',stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    print(r.stdout)
    assert r.returncode==0 and 'sorryAx' not in r.stdout
