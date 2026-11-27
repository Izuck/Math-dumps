# Minkwitz-style search for a short-word stabilizer chain.  usage: trans2.py <order> <seed> <rounds> <out.json>
import sys, random, json
from model import *
order, seed, maxr, outf = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
random.seed(seed)
ORD = {'C': [('c', i) for i in range(8)] + [('e', j) for j in range(12)],
       'E': [('e', j) for j in range(12)] + [('c', i) for i in range(8)],
       'M': [('e', j) for j in (8,9,10,11)] + [('c', i) for i in (4,5,6,7)] + [('e', j) for j in (4,5,6,7)] + [('c', i) for i in (0,1,2,3)] + [('e', j) for j in (0,1,2,3)],
       'L': [('c', i) for i in (4,5,6,7)] + [('e', j) for j in (4,5,6,7,8,9,10,11)] + [('c', i) for i in (0,1,2,3)] + [('e', j) for j in (0,1,2,3)],
       }
BASE = ORD[order]
GSIZE = 43252003274489856000
def img(s, b):
    return (s[0][b[1]], s[1][b[1]]) if b[0] == 'c' else (s[2][b[1]], s[3][b[1]])
def simp(w):
    out = []
    for f in w:
        out.append(f)
        if len(out) >= 4 and out[-1] == out[-2] == out[-3] == out[-4]: del out[-4:]
    return tuple(out)
def htm(w):
    return sum(1 for i in range(len(w)) if i == 0 or w[i] != w[i-1])
table = [dict() for _ in BASE]
for n, b in enumerate(BASE): table[n][(b[1], 0)] = (ID, ())
def sift(g, w):
    for n in range(len(BASE)):
        pt = img(g, BASE[n])
        if pt in table[n]:
            t, tw = table[n][pt]
            if htm(w) < htm(tw):
                table[n][pt] = (g, w)
                g, w, t, tw = t, tw, g, w
            g = mul(inv(t), g); w = simp(invw(tw) + w)
        else:
            table[n][pt] = (g, w); return
        if htm(w) > 60: return
def size():
    p = 1
    for t in table: p *= len(t)
    return p
moves = [(f,)*k for f in range(6) for k in (1,2,3)]
frontier = [()]
for L in range(1, 5):
    nf = []
    for w in frontier:
        for m in moves:
            if w and w[-1] == m[0]: continue
            w2 = w + m; nf.append(w2); sift(ev(w2), w2)
    frontier = nf
rounds = 0
while rounds < maxr or size() != GSIZE:
    rounds += 1
    ents = [(n, v) for n in range(len(BASE)) for v in table[n].values() if v[1]]
    for _ in range(20000):
        (n1, (g1, w1)), (n2, (g2, w2)) = random.choice(ents), random.choice(ents)
        if htm(w1) + htm(w2) > 40: continue
        sift(mul(g1, g2), simp(w1 + w2))
    mx = [max(htm(v[1]) for v in t.values()) for t in table]
    print(order, seed, rounds, size() == GSIZE, mx, sum(mx), file=sys.stderr, flush=True)
assert size() == GSIZE
out = []
for n, b in enumerate(BASE):
    ws = []
    for pt, (g, w) in sorted(table[n].items()):
        assert ev(w) == g and img(g, b) == pt
        for m in range(n): assert img(g, BASE[m]) == (BASE[m][1], 0)
        ws.append(list(w))
    out.append(ws)
json.dump({'base': BASE, 'tables': out, 'bound': sum(mx)}, open(outf, 'w'))
