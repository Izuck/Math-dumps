# usage: gen_thistle.py <thistle.json> <chunk> <out.lean> <header>
import json, sys
from model import *
J = json.load(open(sys.argv[1])); CH = int(sys.argv[2]); outf = sys.argv[3]; header = sys.argv[4]
MOVES = [ev((f,)*(k+1)) for f in range(6) for k in range(3)]
def code_img(s, c):
    if c < 24:
        p, o = divmod(c, 3); return 3*s[0][p] + (s[1][p] + o) % 3
    p, o = divmod(c - 24, 2); return 24 + 2*s[2][p] + (s[3][p] + o) % 2
alltab = sum(code_img(MOVES[m], c) << (6*(48*m + c)) for m in range(18) for c in range(48))
src = lambda f: open('src/' + f).read()
if header == 'CUBE':
    c = open('../Cube.lean').read()
    header = c[:c.index('#print axioms')]
    header = header.replace('namespace Rubik', '-- Sequential elaboration keeps the peak memory of the kernel checks low.\nset_option Elab.async false\n\nnamespace Rubik', 1).replace('# The 3x3x3 Rubik', '# (Self-contained: `Cube.lean` followed by stage 4.)  The 3x3x3 Rubik')
o = [header, src('t1_generic.lean').replace("@ALLTAB@", f"def allTab : ℕ := {alltab}"), src('t2_levels.lean'), src('t3_quads.lean').replace('@QUADL@', '[' + ', '.join('[' + ','.join(map(str, S)) + ']' for S in J['quads']) + ']').replace('@QUADLN@', '[' + ', '.join('[' + ','.join(str(3*i) for i in S) + ']' for S in J['quads']) + ']')]
LV = [("L1", "cTrue", "gN1"), ("L2s", "cNA", "gN2b"), ("L2c", "cNS", "gN2a"), ("L3", "cNC", "K3"), ("L4", "cND", "gN4"), ("L5", "cNE", "gN5")]
KX = lambda g: ("K3", "K3T_spec", "K3T") if g == "K3" else (f"(keyG {g})", f"(keyW_spec {g})", f"(keyT {g})")
enc = lambda w: sum((m + 1) << (5*i) for i, m in enumerate(w))
o.append("\n/-! ### The tables (packed words, see `wordOf`; move numbers are `3 * face + k`) and their kernel checks -/\n\n")
info = {}
ONLY = sys.argv[5].split(',') if len(sys.argv) > 5 and sys.argv[5] != 'SORRY' else None
SORRY = len(sys.argv) > 5 and sys.argv[5] == 'SORRY'
for name, cN, gN in LV:
    if ONLY and name not in ONLY: continue
    L = J[name]; ws, ks, d = L["words"], L["keys"], L["d"]
    chunks = [(i, min(i + CH, len(ws))) for i in range(0, len(ws), CH)]
    bounds = [0] + [ks[a] for (a, b) in chunks[1:]] + [ks[-1] + 1]
    for n, (a, b) in enumerate(chunks):
        o.append(f"def {name}_c{n} : List ℕ := [" + ", ".join(str(enc(w)) for w in ws[a:b]) + "]\n")
        o.append(f"theorem {name}_c{n}_ok : ChunkP {cN} {KX(gN)[0]} {d} {bounds[n]} {bounds[n+1]} ({name}_c{n}.map wordOf) :=\n  chunkCheckP_spec (KT := {KX(gN)[2]}) {KX(gN)[1]} (by {'sorry' if SORRY else 'decide +kernel'})\n")
    tab = f"{name}_c{len(chunks)-1}.map wordOf"
    for n in range(len(chunks)-2, -1, -1): tab = f"{name}_c{n}.map wordOf ++ ({tab})"
    # right-nested appends: c0 ++ (c1 ++ (c2 ++ ...))
    o.append(f"\n/-- Coset representatives for level {name}. -/\ndef {name}_tab : List (List ℕ) := {tab}\n")
    pf = f"{name}_c{len(chunks)-1}_ok"
    for n in range(len(chunks)-2, -1, -1): pf = f"{name}_c{n}_ok.append ({pf})"
    o.append(f"theorem {name}_ok : ChunkP {cN} {KX(gN)[0]} {d} 0 {bounds[-1]} {name}_tab := {pf}\n")
    o.append(f"theorem {name}_len : {name}_tab.length = {len(ws)} := by decide +kernel\n\n")
    info[name] = (d, bounds[-1], len(ws))
    if name == "L4":
        o.append("theorem L4_PQ : ∀ w ∈ L4_tab, PQ (evalW w) := by decide +kernel\n\n")
if ONLY:
    open(outf, 'w').write(''.join(o) + 'end Rubik\n'); sys.exit()
UB = sum(info[n][0] for n, _, _ in LV)
o.append(f"""/-- The chain exhibits `43252003274489856000` distinct reachable states, each at distance
at most `{UB}`. -/
theorem exists_reachable_finset_thistle :
    ∃ P : Finset Cube, (∀ s ∈ P, Reachable s ∧ dist s ≤ {UB}) ∧ P.card = 43252003274489856000 := by
  have h6 : ∀ s ∈ ({{1}} : Finset Cube), (Reachable s ∧ dist s ≤ 0) ∧ s = 1 := by
    intro s hs; rw [Finset.mem_singleton] at hs; subst hs
    exact ⟨⟨reachable_one, (dist_le []).trans (by simp)⟩, rfl⟩
  obtain ⟨P5, h5, c5⟩ := level_step cNE (keyG gN5) {info['L5'][0]} {info['L5'][1]} HE (· = 1)
    (fun x y hx hy => by rw [hy, mul_one]; exact hx) (fun x y hy => by rw [hy, mul_one]) _ L5_ok
    (fun _ _ => memE) _ _ h6
  obtain ⟨P4, h4, c4⟩ := level_step cND (keyG gN4) {info['L4'][0]} {info['L4'][1]} HD3 HE
    (fun x y hx hy => hx.mul_HE hy) inv4 _ L4_ok (fun w hw hm => ⟨memD hm, L4_PQ w hw⟩) _ _ h5
  obtain ⟨P3, h3, c3⟩ := level_step cNC K3 {info['L3'][0]} {info['L3'][1]} HC HD3
    (fun x y hx hy => hx.mul hy.1.1) inv3' _ L3_ok (fun _ _ => memC) _ _ h4
  obtain ⟨P2, h2, c2⟩ := level_step cNS (keyG gN2a) {info['L2c'][0]} {info['L2c'][1]} HS HC
    (fun x y hx hy => hx.mul hy.1) inv2c _ L2c_ok (fun _ _ => memS) _ _ h3
  obtain ⟨P1, h1, c1⟩ := level_step cNA (keyG gN2b) {info['L2s'][0]} {info['L2s'][1]} HA HS
    (fun x y hx hy => hx.mul hy.1) inv2s _ L2s_ok (fun _ _ => memA) _ _ h2
  obtain ⟨P0, h0, c0⟩ := level_step cTrue (keyG gN1) {info['L1'][0]} {info['L1'][1]} (fun _ => True) HA
    (fun _ _ _ _ => trivial) inv1 _ L1_ok (fun _ _ _ => trivial) _ _ h1
  refine ⟨P0, fun s hs => (h0 s hs).1, ?_⟩
  rw [c0, c1, c2, c3, c4, c5, L1_len, L2s_len, L2c_len, L3_len, L4_len, L5_len, Finset.card_singleton]

/-- **Every reachable state can be solved in at most {UB} half-turn-metric moves.** -/
theorem dist_le_{UB} {{s : Cube}} (hs : Reachable s) : dist s ≤ {UB} :=
  dist_le_of_finset exists_reachable_finset_thistle hs

/-- **God's number is at most {UB}.** -/
theorem godsNumber_le_{UB} : godsNumber ≤ {UB} :=
  (godsNumber_le_iff _).mpr fun _ hs => dist_le_{UB} hs

/-- **God's number of the 3x3x3 cube in the half-turn metric lies in `[18, {UB}]`.** -/
theorem godsNumber_mem_Icc : 18 ≤ godsNumber ∧ godsNumber ≤ {UB} :=
  ⟨eighteen_le_godsNumber, godsNumber_le_{UB}⟩

end Rubik

#print axioms Rubik.godsNumber_mem_Icc
""")
open(outf, 'w').write("".join(o))
print("UB", UB, info)
