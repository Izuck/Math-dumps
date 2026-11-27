import json
from model import *
N="UDRLFB"
def vec(t): return "![" + ",".join(map(str,t)) + "]"
for f in range(6):
    cp,co,ep,eo = G[f]; icp,_,iep,_ = inv(G[f])
    print(f"def turn{N[f]} : Cube := ⟨mkPerm {vec(cp)} {vec(icp)} (by decide) (by decide), {vec(co)},\n  mkPerm {vec(ep)} {vec(iep)} (by decide) (by decide), {vec(eo)}⟩")
T = json.load(open('table.json'))
with open('tables.lean','w') as o:
    for n, ws in enumerate(T):
        o.write(f"def T{n} : List (List Face) := [" + ", ".join("[" + ",".join("."+N[f] for f in w) + "]" for w in ws) + "]\n")
    for n, ws in enumerate(T):
        o.write(f"theorem T{n}_ok : checkLevel (fixedL {n}) (bpt {n}) T{n} = true := by decide +kernel\n")
