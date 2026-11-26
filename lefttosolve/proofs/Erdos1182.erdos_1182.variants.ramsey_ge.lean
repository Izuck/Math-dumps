import FormalConjectures.ErdosProblems.«1182»

-- Problem: Erdős Problem 1182 — ramsey ge
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/1182.lean:158 (declaration Erdos1182.erdos_1182.variants.ramsey_ge)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA

/-- Two-sided split graph. -/
def splitGraph (N k : ℕ) : SimpleGraph (Fin N) where
  Adj a b := ¬ ((a.val < k) ↔ (b.val < k))
  symm := ⟨fun _ _ h h' => h h'.symm⟩
  loopless := ⟨fun _ h => h Iff.rfl⟩

lemma splitGraph_triangle_free (N k : ℕ) :
    ¬ (⊤ : SimpleGraph (Fin 3)).IsContained (splitGraph N k) := by
  rintro ⟨f⟩
  have h01 : (splitGraph N k).Adj (f.toHom 0) (f.toHom 1) := f.toHom.map_adj (by decide)
  have h12 : (splitGraph N k).Adj (f.toHom 1) (f.toHom 2) := f.toHom.map_adj (by decide)
  have h02 : (splitGraph N k).Adj (f.toHom 0) (f.toHom 2) := f.toHom.map_adj (by decide)
  simp only [splitGraph] at h01 h12 h02
  tauto

lemma splitGraph_compl_not (n N : ℕ) (hN : N < 2 * n - 1) (G : SimpleGraph (Fin n))
    (hG : G.Connected) : ¬ G.IsContained (splitGraph N (n - 1))ᶜ := by
  rintro ⟨f⟩
  have hn : 1 ≤ n := by
    obtain ⟨v⟩ := hG.nonempty
    exact Nat.one_le_iff_ne_zero.mpr (by rintro rfl; exact v.elim0)
  have hadj : ∀ u v, G.Adj u v → (((f.toHom u).val < n - 1) ↔ ((f.toHom v).val < n - 1)) := by
    intro u v h
    have := f.toHom.map_adj h
    rw [SimpleGraph.compl_adj] at this
    simp only [splitGraph, not_not] at this
    exact this.2
  have key : ∀ u v (w : G.Walk u v),
      (((f.toHom u).val < n - 1) ↔ ((f.toHom v).val < n - 1)) := by
    intro u v w
    induction w with
    | nil => exact Iff.rfl
    | cons h p ih => exact (hadj _ _ h).trans ih
  let v0 : Fin n := ⟨0, by omega⟩
  have hall : ∀ v, (((f.toHom v0).val < n - 1) ↔ ((f.toHom v).val < n - 1)) := by
    intro v
    obtain ⟨w⟩ := hG.preconnected v0 v
    exact key _ _ w
  have hinj := f.injective
  by_cases h0 : (f.toHom v0).val < n - 1
  · let g : Fin n → Fin (n - 1) := fun v => ⟨(f.toHom v).val, (hall v).mp h0⟩
    have hg : Function.Injective g := by
      intro a b hab
      apply hinj
      apply Fin.ext
      have := congrArg Fin.val hab
      simpa [g] using this
    have := Fintype.card_le_of_injective g hg
    simp at this
    omega
  · let g : Fin n → Fin (n - 1) := fun v => ⟨(f.toHom v).val - (n - 1), by
      have h1 := (f.toHom v).isLt
      have h2 : ¬ (f.toHom v).val < n - 1 := fun h => h0 ((hall v).mpr h)
      omega⟩
    have hg : Function.Injective g := by
      intro a b hab
      apply hinj
      apply Fin.ext
      have := congrArg Fin.val hab
      have ha : ¬ (f.toHom a).val < n - 1 := fun h => h0 ((hall a).mpr h)
      have hb : ¬ (f.toHom b).val < n - 1 := fun h => h0 ((hall b).mpr h)
      simp only [g] at this
      omega
    have := Fintype.card_le_of_injective g hg
    simp at this
    omega

lemma ramsey_nonempty (n : ℕ) (G : SimpleGraph (Fin n)) :
    { N : ℕ | ∀ (C : SimpleGraph (Fin N)),
      (⊤ : SimpleGraph (Fin 3)).IsContained C ∨ G.IsContained Cᶜ }.Nonempty := by
  classical
  refine ⟨Nat.choose (3 + n) 3, ?_⟩
  intro C
  let c : Finset (Fin (Nat.choose (3 + n) 3)) → Bool := fun e =>
    if (∀ a ∈ e, ∀ b ∈ e, a ≠ b → C.Adj a b) then false else true
  have hpair : ∀ (S : Finset (Fin (Nat.choose (3 + n) 3))) a b, a ∈ S → b ∈ S → a ≠ b →
      ({a, b} : Finset _) ⊆ S ∧ ({a, b} : Finset _).card = 2 := by
    intro S a b ha hb hab
    refine ⟨?_, Finset.card_pair hab⟩
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have := Combinatorics.Diagonal.hasRamseyProperty_choose 3 n c Finset.univ (by simp)
  rcases this with ⟨S, -, hS, hmono⟩ | ⟨S, -, hS, hmono⟩
  · left
    have hcl : C.IsNClique 3 S := by
      rw [SimpleGraph.isNClique_iff]
      refine ⟨?_, hS⟩
      intro a ha b hb hab
      obtain ⟨h1, h2⟩ := hpair S a b ha hb hab
      have := hmono _ h1 h2
      simp only [c] at this
      split_ifs at this with hh
      · exact hh a (by simp) b (by simp) hab
    have : ¬ C.CliqueFree 3 := fun hf => hf S hcl
    rw [SimpleGraph.not_cliqueFree_iff_top_isContained] at this
    exact this
  · right
    have hcl : Cᶜ.IsNClique n S := by
      rw [SimpleGraph.isNClique_iff]
      refine ⟨?_, hS⟩
      intro a ha b hb hab
      obtain ⟨h1, h2⟩ := hpair S a b ha hb hab
      have := hmono _ h1 h2
      simp only [c] at this
      split_ifs at this with hh
      rw [SimpleGraph.compl_adj]
      refine ⟨hab, fun hadj => hh ?_⟩
      intro x hx y hy hxy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact absurd rfl hxy
      · exact hadj
      · exact hadj.symm
      · exact absurd rfl hxy
    have : ¬ Cᶜ.CliqueFree n := fun hf => hf S hcl
    rw [SimpleGraph.not_cliqueFree_iff_top_isContained] at this
    exact (SimpleGraph.IsContained.of_le le_top).trans this

end OMA

theorem OMA.solution : type_of% @Erdos1182.erdos_1182.variants.ramsey_ge := by
  intro n G hG
  unfold SimpleGraph.graphRamsey
  apply le_csInf (OMA.ramsey_nonempty n G)
  intro N hN
  by_contra hlt'
  have hlt : N < 2 * n - 1 := Nat.lt_of_not_le hlt'
  rcases hN (OMA.splitGraph N (n - 1)) with h | h
  · exact OMA.splitGraph_triangle_free N (n - 1) h
  · exact OMA.splitGraph_compl_not n N hlt G hG h

