import re,json,sys,importlib.util,subprocess
from collections import Counter
S='/tmp/claude-0/-home-user/7fccf3f9-df17-5321-8bf1-fd7927a2cb04/scratchpad'
spec=importlib.util.spec_from_file_location('plain',S+'/plain/plain.py'); m=importlib.util.module_from_spec(spec); spec.loader.exec_module(m)
def parts(line):
    out,i,n=[],0,len(line)
    while i<n:
        if line[i] in '"\'':
            q=line[i]; i+=1; buf=''
            while True:
                if line[i]=='\\' and i+1<n: buf+=line[i+1]; i+=2; continue
                if line[i]==q:
                    if i+1<n and line[i+1]==q: buf+=q; i+=2; continue
                    i+=1; break
                buf+=line[i]; i+=1
            out.append(('text',buf))
        else:
            j=line.find(', ',i); j=n if j<0 else j
            out.append(('bare',line[i:j])); i=j
        if line.startswith(', ',i): i+=2
    return out
def atom(line):
    ps=parts(line); vals=[v for _,v in ps]
    if len(vals)==1: return vals[0].replace(' ','_')+'()'
    if len(vals)==3 and vals[1]=='is': name,args=vals[2],[ps[0]]
    else: name,args=vals[1],[ps[0]]+ps[2:]
    mv=lambda k,v: v if k=='bare' and re.fullmatch(r'-?[0-9]+',v) else json.dumps(v)
    return name.replace(' ','_')+'('+', '.join(mv(k,v) for k,v in args)+')'
def key(a):
    mm=re.match(r'^([a-z_]+)\((.*)\)$',a)
    return (mm.group(1),tuple(json.loads(x.replace("\\'","'")) if x.startswith('"') else int(x) for x in re.findall(r'"(?:[^"\\]|\\.)*"|-?\d+',mm.group(2))))
lines=open(sys.argv[1]).read().split('\n')
if lines[-1]=='': lines=lines[:-1]
SHOWN={'conforms','broke','answered','explains','breaks'}
keep,shown,facts=[],[],[]
for i,l in enumerate(lines):
    nxt=lines[i+1] if i+1<len(lines) else ''
    if l and not l.startswith(' ') and not nxt.startswith('    ') and not l.startswith('['):
        vals=[v for _,v in parts(l)]
        if (len(vals)>=3 and vals[1] in SHOWN) or l.endswith(', is, a problem'): shown.append(l); continue
        if '"' in l or "'" in l: facts.append(atom(l)+'.'); continue
    keep.append(l)
decls=[]
for l in keep:
    mm=re.match(r'^\S+, creates fact, (.*)$',l)
    if not mm: continue
    ps=[p.strip() for p in re.split(r'(\[[a-z ]+\])',mm.group(1)) if p.strip()]
    slots=[p for p in ps if p.startswith('[')]; words=' '.join(p for p in ps if not p.startswith('['))
    sent = words if not slots else (', '.join([slots[0],'is',words[3:] if words.startswith('is ') else words]) if len(slots)==1 else ', '.join([slots[0],words]+slots[1:]))
    decls.append('Decl '+m.mangle_atom(sent)+'.')
open('replay.mg','w').write('\n'.join(decls+m.to_mangle(keep)+facts)+'\n')
out=subprocess.run([S+'/mgcheck/mgcheck','replay.mg','conforms','broke','answered','explains','breaks','a_problem'],capture_output=True,text=True).stdout
print(out.split('\n')[0])
got={key(a) for a in out.split('\n') if re.match(r'^[a-z_]+\(',a)}
want={key(atom(l)) for l in shown}
print('shown facts removed:',len(want),dict(Counter(p for p,_ in want)),'| derived again:',len(got))
print('missing:',sorted(want-got)[:4]); print('extra:',sorted(got-want)[:4])
