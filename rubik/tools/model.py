# Cubie model (Kociemba conventions). corners URF UFL ULB UBR DFR DLF DBL DRB ; edges UR UF UL UB DR DF DL DB FR FL BL BR
# faces: 0 U,1 D,2 R,3 L,4 F,5 B
G = {
 0: ([3,0,1,2,4,5,6,7],[0]*8,[3,0,1,2,4,5,6,7,8,9,10,11],[0]*12),
 1: ([0,1,2,3,5,6,7,4],[0]*8,[0,1,2,3,5,6,7,4,8,9,10,11],[0]*12),
 2: ([4,1,2,0,7,5,6,3],[2,0,0,1,1,0,0,2],[8,1,2,3,11,5,6,7,4,9,10,0],[0]*12),
 3: ([0,2,6,3,4,1,5,7],[0,1,2,0,0,2,1,0],[0,1,10,3,4,5,9,7,8,2,6,11],[0]*12),
 4: ([1,5,2,3,0,4,6,7],[1,2,0,0,2,1,0,0],[0,9,2,3,4,8,6,7,1,5,10,11],[0,1,0,0,0,1,0,0,1,1,0,0]),
 5: ([0,1,3,7,4,5,2,6],[0,0,1,2,0,0,2,1],[0,1,2,11,4,5,6,10,8,9,3,7],[0,0,0,1,0,0,0,1,0,0,1,1]),
}
G = {k: tuple(tuple(x) for x in v) for k, v in G.items()}
ID = (tuple(range(8)), (0,)*8, tuple(range(12)), (0,)*12)
def mul(a, b):
    acp, aco, aep, aeo = a; bcp, bco, bep, beo = b
    return (tuple(acp[i] for i in bcp), tuple((aco[bcp[i]] + bco[i]) % 3 for i in range(8)),
            tuple(aep[i] for i in bep), tuple((aeo[bep[i]] + beo[i]) % 2 for i in range(12)))
def inv(a):
    cp, co, ep, eo = a
    icp = [0]*8; ico = [0]*8; iep = [0]*12; ieo = [0]*12
    for i in range(8): icp[cp[i]] = i
    for i in range(8): ico[i] = (-co[icp[i]]) % 3
    for i in range(12): iep[ep[i]] = i
    for i in range(12): ieo[i] = (-eo[iep[i]]) % 2
    return (tuple(icp), tuple(ico), tuple(iep), tuple(ieo))
def ev(word):
    s = ID
    for f in word: s = mul(s, G[f])
    return s
def invw(word): return tuple(f for f in reversed(word) for _ in range(3))
NAMES = "UDRLFB"
def parse(s):
    out = []
    for t in s.split():
        f = NAMES.index(t[0]); k = 1 if len(t) == 1 else (2 if t[1] == '2' else 3)
        out += [f]*k
    return tuple(out)
if __name__ == "__main__":
    for f in range(6):
        assert ev((f,)*4) == ID and ev((f,)*2) != ID
        assert mul(G[f], inv(G[f])) == ID
    assert ev(parse("R U R' U'")*6) == ID
    sf = ev(parse("U R2 F B R B2 R U2 L B2 R U' D' R2 F R' L B2 U2 F2"))
    print(sf)
    assert sf == (ID[0], ID[1], ID[2], (1,)*12)
    for a, b in ((0,1),(2,3),(4,5)): assert mul(G[a],G[b]) == mul(G[b],G[a])
    # canonical counts
    n, a, b = 1, 0, 0; tot = 0
    for k in range(0, 20):
        tot += n + 3*a + 3*b
        print(k, n + 3*a + 3*b, tot, tot < 43252003274489856000)
        n, a, b = 0, 3*(n + 2*a + 2*b), 3*(n + 3*a + 2*b)
