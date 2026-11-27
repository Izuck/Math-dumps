# Thistlethwaite-style subgroup chain: BFS-optimal coset representatives for six levels.
# Output: thistle.json  {level: {"d": radius, "words": [[move indices]] sorted by key, "keys": [...]}}
import sys, json, itertools
from collections import deque
from model import *
MOVES = [ev((f,)*(k+1)) for f in range(6) for k in range(3)]      # index 3f+k
def minv(m): return 3*(m//3) + (2 - m % 3)
def evm(word):
    s = ID
    for m in word: s = mul(s, MOVES[m])
    return s
# tetrad / slices from half-turn orbits
def orbit(start, perms):
    o = {start}; ch = True
    while ch:
        ch = False
        for p in perms:
            for x in list(o):
                if p[x] not in o: o.add(p[x]); ch = True
    return o
H2 = [MOVES[3*f+1] for f in range(6)]
TET = orbit(0, [h[0] for h in H2]); MS = orbit(1, [h[2] for h in H2])
assert TET == {0,2,5,7} and MS == {1,3,5,7}, (TET, MS)
# ---- mirrors of the Lean code-level functions
def prof(s): return [3*s[0][i] + s[1][i] for i in range(8)] + [24 + 2*s[2][j] + s[3][j] for j in range(12)]
BC = [3*i for i in range(8)] + [24 + 2*j for j in range(12)]
tetN = lambda y: (165 >> (y//3)) % 2 == 1
msN = lambda y: (170 >> ((y-24)//2)) % 2 == 1
cNA = lambda b, y: (not 24 <= y) or y % 2 == 0
cNS = lambda b, y: cNA(b, y) and ((not 24 <= y) or ((40 <= y) == (40 <= b)))
cNC = lambda b, y: cNS(b, y) and (24 <= y or y % 3 == 0)
cND = lambda b, y: cNC(b, y) and ((msN(y) == msN(b)) if 24 <= y else (tetN(y) == tetN(b)))
cNE = lambda b, y: cND(b, y) and (24 <= y or y == b)
cTrue = lambda b, y: True
gN1 = lambda b, y: (y % 2) * 2**((y-24)//2) if 24 <= y else 0
gN2a = lambda b, y: 0 if 24 <= y else (y % 3) * 4**(y//3)
gN2b = lambda b, y: 2**((y-24)//2) if 40 <= b else 0
gN3 = lambda b, y: ((256 * 2**((y-24)//2) if msN(b) else 0) if 24 <= b else (2**(y//3) if tetN(b) else 0))
gN4 = lambda b, y: 0 if 24 <= b else (y//3) * 8**(b//3)
gN5 = lambda b, y: ((y-24)//2) * 16**((b-24)//2) if 24 <= b else 0
def key(g, s): return sum(g(b, y) for b, y in zip(BC, prof(s)))
def mem(c, s): return all(c(b, y) for b, y in zip(BC, prof(s)))
ALL18 = list(range(18))
G1M = [m for m in range(18) if m//3 in (0,1,2,3) or m % 3 == 1]       # U D R L any, F2 B2
G2M = [m for m in range(18) if m//3 in (0,1) or m % 3 == 1]           # U D any, R2 L2 F2 B2
G3M = [m for m in range(18) if m % 3 == 1]
def bfs_states(moves, keyfn):
    tab = {keyfn(ID): (ID, ())}
    dq = deque([ID_K := keyfn(ID)])
    while dq:
        k = dq.popleft(); s, w = tab[k]
        for m in moves:
            t = mul(MOVES[m], s); kt = keyfn(t)
            if kt not in tab:
                tab[kt] = (t, (m,) + w); dq.append(kt)
    return tab
out = {}
def finish(name, words, cH, g, expect, kf=None):
    ks = []
    for w in words:
        s = evm(w); assert mem(cH, s), name
        ks.append(kf(s) if kf else key(g, s))
    assert len(set(ks)) == len(ks) == expect, (name, len(ks), len(set(ks)), expect)
    order = sorted(range(len(ks)), key=lambda i: ks[i])
    d = max(len(w) for w in words)
    out[name] = {"d": d, "words": [list(words[i]) for i in order], "keys": [ks[i] for i in order]}
    print(name, len(words), "radius", d, "letters", sum(len(w) for w in words), file=sys.stderr, flush=True)
# L1: G / {eo=0}
t = bfs_states(ALL18, lambda s: key(gN1, s))
finish("L1", [w for (_, w) in t.values()], cTrue, gN1, 2048)
# L2s: {eo=0} / {eo=0, E-slice preserved}
t = bfs_states(G1M, lambda s: key(gN2b, s))
finish("L2s", [w for (_, w) in t.values()], cNA, gN2b, 495)
# L5: G3 with cp = id
def bfs_full(moves):
    tab = {ID: ()}
    dq = deque([ID])
    while dq:
        s = dq.popleft(); w = tab[s]
        for m in moves:
            t = mul(MOVES[m], s)
            if t not in tab: tab[t] = (m,) + w; dq.append(t)
    return tab
t = bfs_full(G3M); assert len(t) == 663552
finish("L5", [w for s, w in t.items() if s[0] == ID[0]], cNE, gN5, 6912)
best = {}
for s_, w in t.items():
    if s_[0] not in best or len(w) < len(best[s_[0]]): best[s_[0]] = w
C96 = list(best.keys()); assert len(C96) == 96
A = sorted(TET); B = sorted(set(range(8)) - TET)
quads0 = [frozenset(p) | frozenset(q) for p in itertools.combinations(A, 2) for q in itertools.combinations(B, 2)]
def qorbit(S):
    o = set()
    for p in C96: o.add(frozenset(p[i] for i in S))
    return o
orbs = []
seen = set()
for S in quads0:
    if S not in seen:
        o = qorbit(S); orbs.append(o); seen |= o
print("quad orbit sizes", [len(o) for o in orbs], file=sys.stderr)
QUADS = sorted(sorted(S) for S in min(orbs, key=len)); assert len(QUADS) == 12
def qkey(s): return sum(2**sum(2**s[0][i] for i in S) for S in QUADS)
def PQ(s): return sorted(sorted(s[0][i] for i in S) for S in QUADS) == QUADS
for p in C96: assert PQ((p,))
K3 = lambda s: key(gN3, s) + 65536 * qkey(s)
# L4: corners inside the squares group
ws4 = list(best.values())
for w in ws4: assert PQ(evm(w))
finish("L4", ws4, cND, gN4, 96)
del t
# L2b: coordinate BFS on (twist by position, slice mask) under G1 moves
def coord_bfs(moves, nA, amove, nB, bmove, a0, b0):
    N = nA * nB
    par = bytearray([255]) * N
    c0 = a0 * nB + b0; par[c0] = 254
    cur = [c0]
    while cur:
        nxt = []
        for c in cur:
            a, b = divmod(c, nB)
            for m in moves:
                c2 = amove[m][a] * nB + bmove[m][b]
                if par[c2] == 255: par[c2] = m; nxt.append(c2)
        cur = nxt
    def word(c):
        w = []
        while par[c] != 254:
            m = par[c]; w.append(m); a, b = divmod(c, nB); mi = minv(m)
            c = amove[mi][a] * nB + bmove[mi][b]
        return tuple(w)
    return par, word
twmove = []
for m in range(18):
    mcp, mco = MOVES[m][0], MOVES[m][1]; row = []
    for t in range(6561):
        tw = [(t // 3**p) % 3 for p in range(8)]; n = [0]*8
        for p in range(8): n[mcp[p]] = (tw[p] + mco[p]) % 3
        row.append(sum(n[p] * 3**p for p in range(8)))
    twmove.append(row)
maskmove = []
for m in range(18):
    mep = MOVES[m][2]
    maskmove.append([sum(1 << mep[p] for p in range(12) if (mask >> p) & 1) for mask in range(4096)])
par, word = coord_bfs(G1M, 6561, twmove, 4096, maskmove, 0, 0xF00)
print("L2b coords", sum(1 for x in par if x != 255), file=sys.stderr, flush=True)
finish("L2c", [word(t*4096 + 0xF00) for t in range(6561) if par[t*4096 + 0xF00] != 255], cNS, gN2a, 2187)
del par
# L3: G2 / G3 (29400 cosets)
t3 = bfs_states(G2M, K3)
finish("L3", [w for (_, w) in t3.values()], cNC, gN3, 29400, kf=K3)
out["quads"] = QUADS
out["total"] = sum(out[k]["d"] for k in ("L1", "L2s", "L2c", "L3", "L4", "L5"))
print("TOTAL BOUND", out["total"], file=sys.stderr)
json.dump(out, open("thistle.json", "w"))
