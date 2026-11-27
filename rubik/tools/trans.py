import sys, random, itertools, json
from model import *
random.seed(1)
BASE = [('c', i) for i in range(7)] + [('e', j) for j in range(10)]
EXP = [24-3*i for i in range(7)] + [24-2*j for j in range(10)]
def img(s, b):
    return (s[0][b[1]], s[1][b[1]]) if b[0] == 'c' else (s[2][b[1]], s[3][b[1]])
def simp(w):
    # reduce runs mod 4
    out = []
    for f in w:
        out.append(f)
        if len(out) >= 4 and out[-1] == out[-2] == out[-3] == out[-4]: del out[-4:]
    return tuple(out)
table = [dict() for _ in BASE]
for n, b in enumerate(BASE): table[n][(b[1], 0)] = (ID, ())
LIM = 10**9
def sift(g, w, start=0):
    changed = False
    for n in range(start, len(BASE)):
        pt = img(g, BASE[n])
        if pt in table[n]:
            t, tw = table[n][pt]
            if len(w) < len(tw):
                table[n][pt] = (g, w); changed = True
                g, w, t, tw = t, tw, g, w   # continue with old (still in stab n)
            g = mul(inv(t), g); w = simp(invw(tw) + w)
        else:
            table[n][pt] = (g, w); return True
        if len(w) > 400: return changed
    return changed
def full(): return all(len(table[n]) == EXP[n] for n in range(len(BASE)))
# feed short words
moves = [(f,)*k for f in range(6) for k in (1,2,3)]
frontier = [()]
cnt = 0
for L in range(1, 5):
    nf = []
    for w in frontier:
        for m in moves:
            if w and w[-1] == m[0]: continue
            w2 = w + m; nf.append(w2); sift(ev(w2), w2)
    frontier = nf
    print(L, [len(t) for t in table], file=sys.stderr)
rounds = 0
while rounds < 60:
    rounds += 1
    # combine random pairs of table entries
    ents = [(n, v) for n in range(len(BASE)) for v in table[n].values() if v[1]]
    for _ in range(20000):
        (n1, (g1, w1)), (n2, (g2, w2)) = random.choice(ents), random.choice(ents)
        if len(w1) + len(w2) > 120: continue
        sift(mul(g1, g2), simp(w1 + w2))
    print(rounds, [len(t) for t in table], max(len(v[1]) for t in table for v in t.values()), sum(len(v[1]) for t in table for v in t.values()), file=sys.stderr)
    if full() and rounds >= int(sys.argv[1]): break
assert full()
# verify
out = []
for n, b in enumerate(BASE):
    ws = []
    for pt, (g, w) in sorted(table[n].items()):
        assert ev(w) == g and img(g, b) == pt
        for m in range(n): assert img(g, BASE[m]) == (BASE[m][1], 0)
        ws.append(list(w))
    out.append(ws)
json.dump(out, open('table.json', 'w'))
