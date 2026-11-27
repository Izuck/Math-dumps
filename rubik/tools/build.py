# usage: build.py <table.json>  -> writes ../Cube.lean
import json, sys
J = json.load(open(sys.argv[1])); BASE = J['base']; T = J['tables']
N = "UDRLFB"
def htm(w): return sum(1 for i in range(len(w)) if i == 0 or w[i] != w[i-1])
d = [max(htm(w) for w in ws) for ws in T]
UB = sum(d); L = len(T)
o = []
o.append("/-- Base of the stabilizer chain. -/\ndef basePts : List Pt := [" + ", ".join((".inl " if k == 'c' else ".inr ") + str(i) for k, i in BASE) + "]\n\n")
for n, ws in enumerate(T):
    o.append(f"def T{n} : List (List Face) := [" + ", ".join("[" + ",".join("."+N[f] for f in w) + "]" for w in ws) + "]\n")
o.append("\n")
for n, ws in enumerate(T):
    o.append(f"theorem T{n}_ok : checkLevel (fixedL basePts {n}) (basePts.getD {n} (.inl 0)) {d[n]} T{n} = true := by decide +kernel\n")
for n, ws in enumerate(T):
    o.append(f"theorem T{n}_len : T{n}.length = {len(ws)} := by decide\n")
o.append(f"""
/-- The stabilizer chain `T0 … T{L-1}` exhibits `43252003274489856000` distinct reachable states,
each at distance at most `{UB}`. -/
theorem exists_reachable_finset :
    ∃ P : Finset Cube, (∀ s ∈ P, Reachable s ∧ dist s ≤ {UB}) ∧ P.card = 43252003274489856000 := by
  have h{L} : ∀ s ∈ ({{1}} : Finset Cube), (Reachable s ∧ dist s ≤ 0) ∧ ∀ p ∈ fixedL basePts {L}, Fix s p := by
    intro s hs; rw [Finset.mem_singleton] at hs; subst hs
    exact ⟨⟨reachable_one, (dist_le []).trans (by simp)⟩, fun p _ => fix_one p⟩
""")
for n in range(L-1, -1, -1):
    o.append(f"  obtain ⟨P{n}, h{n}, c{n}⟩ := chain_step (fixedL basePts {n}) (basePts.getD {n} (.inl 0)) {d[n]} T{n} T{n}_ok _ _ h{n+1}\n")
o.append("  refine ⟨P0, fun s hs => (h0 s hs).1, ?_⟩\n  rw [" + ", ".join(f"c{n}, T{n}_len" for n in range(L)) + ", Finset.card_singleton]\n\n")
src = lambda f: open('src/' + f).read()
s = src('1_head.lean') + src('2_chain.lean') + "".join(o) + src('4_valid.lean') + src('5_count.lean').replace("@UB@", str(UB))
s += '''
#print axioms Rubik.godsNumber_spec
#print axioms Rubik.Reachable.valid
#print axioms Rubik.reachable_iff_valid
#print axioms Rubik.card_reachable
#print axioms Rubik.card_ball_17
#print axioms Rubik.eighteen_le_godsNumber
#print axioms Rubik.godsNumber_bounds
#print axioms Rubik.superflip_eq
'''
open('../Cube.lean', 'w').write(s)
print("UB", UB, d)
