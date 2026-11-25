import OrdinaryRepresentatives

/-! Restricting the original coloring to the auxiliary set in Appendix A, §4. -/

namespace Erdos617.ColoredLists

open Finset PruningOverlap
open scoped Classical
noncomputable section
variable {V : Type*} {r : ℕ}

/-- Read the original label of an edge whose endpoints lie in B. -/
def inducedColor (color : {e : Sym2 V // ¬e.IsDiag} → Fin r) (B : Finset V)
    (e : {e : Sym2 B // ¬e.IsDiag}) : Fin r :=
  color ⟨e.1.map Subtype.val, fun diag ↦ e.2 ((Sym2.isDiag_map Subtype.val_injective).mp diag)⟩

theorem induced_target_graph (color : {e : Sym2 V // ¬e.IsDiag} → Fin r)
    (B : Finset V) (j : Fin r) :
    targetGraph (inducedColor color B) j = (targetGraph color j).induce (B:Set V) := by
  ext x y
  constructor
  · rintro ⟨hne,label⟩
    exact ⟨fun eq ↦ hne (Subtype.ext eq),label⟩
  · rintro ⟨hne,label⟩
    exact ⟨fun eq ↦ hne (congrArg Subtype.val eq),label⟩

/-- A missing-color witness in an induced coloring lifts along the inclusion. -/
theorem no_witness_induced (color : {e : Sym2 V // ¬e.IsDiag} → Fin r)
    (no : ¬Witness color) (B : Finset V) : ¬Witness (inducedColor color B) := by
  rintro ⟨U,j,card,missing⟩
  let emb : B ↪ V := Function.Embedding.subtype _
  refine no ⟨U.map emb,j,by simpa using card,?_⟩
  intro x hx y hy ne
  obtain ⟨u,hu,rfl⟩ := mem_map.mp hx
  obtain ⟨v,hv,rfl⟩ := mem_map.mp hy
  exact missing u hu v hv (fun h ↦ ne (congrArg emb h))

/-- All color classes keep their independence cap after restriction. -/
theorem induced_color_cap (color : {e : Sym2 V // ¬e.IsDiag} → Fin r)
    (no : ¬Witness color) (B : Finset V) (hr : 2 ≤ r) (j : Fin r) (A : Finset B)
    (ind : (targetGraph (inducedColor color B) j).IsIndepSet (A:Set B)) : A.card ≤ r :=
  (caps_of_no_witness _ j hr (no_witness_induced color no B)).1 A ind

variable [Fintype V] (T : Trace V r) {E : Finset V} {rows : Finset ℕ}
  {e n : ℕ} {α β M Y b : ℝ}
  (S : WidthIntegral.Selection rows (rowDeficit T E) (rowIncidence T E) e n α β M)

/-- The smaller target independence cap comes from the exterior extension
argument on the original graph. -/
theorem induced_exterior_cap (hr : 2 ≤ r) (no : ¬Witness T.color)
    (band : RetainedWidth.Band Y b α β) (slots : e+rows.card = r)
    (B : Finset V) (sub : B ⊆ lowExterior T E S.retained S.s)
    (A : Finset B) (ind : (targetGraph (inducedColor T.color B) T.target).IsIndepSet (A:Set B)) :
    A.card ≤ S.s-1 := by
  let emb : B ↪ V := Function.Embedding.subtype _
  have inside : A.map emb ⊆ lowExterior T E S.retained S.s := by
    intro v hv
    obtain ⟨u,_,rfl⟩ := mem_map.mp hv
    exact sub u.property
  have independently : (targetGraph T.color T.target).IsIndepSet ((A.map emb:Finset V):Set V) := by
    rw [induced_target_graph] at ind
    intro u hu v hv hne hedge
    obtain ⟨x,hx,rfl⟩ := mem_map.mp hu
    obtain ⟨y,hy,rfl⟩ := mem_map.mp hv
    exact ind hx hy (fun he ↦ hne (congrArg emb he)) hedge
  simpa using exterior_independence_cap T S hr no band slots _ inside independently

/-- If the claimed shortage fails, choose the auxiliary vertices and their
induced coloring. Its signed order excess is between −3r/20 and one. -/
theorem exists_auxiliary_coloring (hr : 2 ≤ r) (no : ¬Witness T.color)
    (band : RetainedWidth.Band Y b α β) (slots : e+rows.card = r)
    (fail : ((S.s-1:ℕ):ℝ)*r - ((lowExterior T E S.retained S.s).card:ℝ) ≤ (3/20:ℝ)*r) :
    ∃ B ⊆ lowExterior T E S.retained S.s,
      B.card = min (lowExterior T E S.retained S.s).card ((S.s-1)*r+1) ∧
      (-(3/20:ℝ)*r ≤ (B.card:ℝ)-((S.s-1:ℕ):ℝ)*r ∧ (B.card:ℝ)-((S.s-1:ℕ):ℝ)*r ≤ 1) ∧
      ¬Witness (inducedColor T.color B) ∧
      ∀ A : Finset B, (targetGraph (inducedColor T.color B) T.target).IsIndepSet (A:Set B) →
        A.card ≤ S.s-1 := by
  let X := lowExterior T E S.retained S.s
  let h := S.s-1
  obtain ⟨B,sub,size⟩ := Finset.exists_subset_card_eq (min_le_left X.card (h*r+1))
  refine ⟨B,sub,size,?_,no_witness_induced _ no B,induced_exterior_cap T S hr no band slots B sub⟩
  have cap : B.card ≤ h*r+1 := size.trans_le (min_le_right ..)
  have up : (B.card:ℝ) ≤ (h:ℝ)*r+1 := by exact_mod_cast cap
  change (h:ℝ)*r-(X.card:ℝ) ≤ _ at fail
  change _ ≤ (B.card:ℝ)-(h:ℝ)*r ∧ (B.card:ℝ)-(h:ℝ)*r ≤ 1
  refine ⟨?_,by linarith only [up]⟩
  by_cases fits : X.card ≤ h*r+1
  · rw [min_eq_left fits] at size
    rw [size]
    linarith only [fail]
  · rw [min_eq_right (le_of_not_ge fits)] at size
    have eq : (B.card:ℝ) = (h:ℝ)*r+1 := by exact_mod_cast size
    linarith only [eq,Nat.cast_nonneg (α := ℝ) r]

end
end Erdos617.ColoredLists
