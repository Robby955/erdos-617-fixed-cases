import AuxiliaryExtension

/-! The original target edges excluded by the prescribed exterior vertices and
the previously fixed representatives in Appendix A, §4. -/

namespace Erdos617.ColoredLists

open Finset PruningOverlap RowExtraction PackingLists PrescribedLists Transversal
open scoped Classical
noncomputable section

private theorem union_cost {X W : Type*} [DecidableEq W] (P : Finset X) (N : X → Finset W) (t : ℝ)
    (each : ∀ x ∈ P, ((N x).card:ℝ) ≤ t) : ((P.biUnion N).card:ℝ) ≤ P.card*t := by
  have bound := sum_le_sum each
  simp only [sum_const,nsmul_eq_mul] at bound
  apply le_trans _ bound
  exact_mod_cast card_biUnion_le (s := P) (t := N)

variable {V : Type*} {r : ℕ} [Fintype V] (T : Trace V r)

/-- In the induced auxiliary coloring, fill all requested rows and avoid
every target neighbor of a prescribed vertex in the original coloring. -/
theorem colored_auxiliary_representatives (prep : Prepared T) (hr : 0 < r)
    {E : Finset V} {e n : ℕ} {α β M Y b : ℝ}
    (S : WidthIntegral.Selection (ordinaryLists T E) (rowDeficit T E) (rowIncidence T E)
      e n α β M) (band : RetainedWidth.Band Y b α β)
    (B : Finset V) (sub : B ⊆ lowExterior T E S.retained S.s)
    (row : B → ℕ) (part : AuxiliaryPartition T S.s B row)
    (A : Finset B) (survivors : AuxiliarySurvivors
      (targetGraph (inducedColor T.color B) T.target) row (S.s-1) r A)
    (parts : Finset ℕ) (indices : parts ⊆ range (S.s-1))
    (P : Finset V) (Q : Finset B) (D : Finset V)
    (small : ∀ v ∈ P, ∀ i ∈ parts,
      (((fiber A row i).filter fun y ↦ (targetGraph T.color T.target).Adj v y.1).card:ℝ) ≤
        (81/200:ℝ)*r)
    (qaux : ∀ q ∈ Q, q ∈ A ∧ row q ∉ parts)
    (dord : ∀ v ∈ D, ∃ j ∈ S.retained, v ∈ temporaryRow T E j)
    (cases : (P.card ≤ 2 ∧ Q = ∅ ∧ D = ∅) ∨ (P.card ≤ 1 ∧ Q.card+D.card ≤ 2)) :
    ∃ R ⊆ A, Partial (targetGraph (inducedColor T.color B) T.target) row R ∧
      R.image row = parts ∧ ∀ x ∈ R, ∀ v ∈ P ∪ Q.image Subtype.val ∪ D,
        ¬(targetGraph T.color T.target).Adj v x.1 := by
  let : DecidableEq B := Classical.decEq _
  let G := targetGraph T.color T.target
  let H := targetGraph (inducedColor T.color B) T.target
  let allowed := A.filter fun x ↦ row x ∈ parts
  let F := P.biUnion fun v ↦ A.filter (fun x ↦ G.Adj v x.1)
  let N := fun v : V ↦ allowed.filter (fun x ↦ G.Adj v x.1)
  let U := Q.biUnion (fun q ↦ N q.1) ∪ D.biUnion N
  have pcost (i : ℕ) (hi : i ∈ parts) :
      ((fiber (A ∩ F) row i).card:ℝ) ≤ P.card*((81/200:ℝ)*r) := by
    let Ni := fun v : V ↦ (fiber A row i).filter (fun y ↦ G.Adj v y.1)
    have cover : fiber (A ∩ F) row i ⊆ P.biUnion Ni := by
      intro x hx
      obtain ⟨af,xi⟩ := mem_filter.mp hx
      obtain ⟨ax,fx⟩ := mem_inter.mp af
      obtain ⟨v,vp,hvx⟩ := mem_biUnion.mp fx
      exact mem_biUnion.mpr ⟨v,vp,mem_filter.mpr ⟨mem_filter.mpr ⟨ax,xi⟩,(mem_filter.mp hvx).2⟩⟩
    exact (Nat.cast_le.mpr (card_le_card cover)).trans (union_cost P Ni _ fun v hv ↦ small v hv i hi)
  have adj {x y : B} : H.Adj x y ↔ G.Adj x.1 y.1 := by
    simp only [H,G,induced_target_graph,SimpleGraph.induce_adj]
  have qcost (q) (hq : q ∈ Q) : ((N q.1).card:ℝ) ≤ (43/200:ℝ)*r := by
    apply le_trans _ (survivors.degree q (qaux q hq).1)
    apply Nat.cast_le.mpr (card_le_card ?_)
    intro x hx
    obtain ⟨hxallowed,ex⟩ := mem_filter.mp hx
    obtain ⟨xA,xi⟩ := mem_filter.mp hxallowed
    exact mem_filter.mpr ⟨xA,fun eq ↦ (qaux q hq).2 (eq ▸ xi),adj.mpr ex⟩
  have dcost (v) (hv : v ∈ D) : ((N v).card:ℝ) ≤ (43/200:ℝ)*r := by
    obtain ⟨j,hj,vj⟩ := dord v hv
    have bound := (temporary_row_bounds T prep hr E band S hj).2 v vj
    have embed : (N v).card ≤ (outsideClique T E j v).card := by
      apply card_le_card_of_injOn Subtype.val _ (fun _ _ _ _ eq ↦ Subtype.ext eq)
      intro x hx
      refine mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hx).2,?_⟩
      intro xj
      exact (mem_filter.mp (sub x.2)).2.1 (mem_biUnion.mpr ⟨j,hj,xj⟩)
    have cap : ((N v).card:ℝ) ≤ (outsideClique T E j v).card := by exact_mod_cast embed
    have less := cap.trans_lt bound
    linarith only [less,Nat.cast_nonneg (α := ℝ) r]
  have totalCost : (U.card:ℝ) ≤ ((Q.card:ℝ)+D.card)*((43/200:ℝ)*r) := by
    have union : (U.card:ℝ) ≤ (Q.biUnion fun q ↦ N q.1).card + ((D.biUnion N).card:ℝ) := by
      exact_mod_cast card_union_le (Q.biUnion fun q ↦ N q.1) (D.biUnion N)
    rw [add_mul]
    exact union.trans (add_le_add (union_cost Q _ _ qcost) (union_cost D N _ dcost))
  have reps : ∃ R ⊆ candidates A F U, Partial H row R ∧ R.image row = parts := by
    rcases cases with ⟨p,q,d⟩ | ⟨p,qd⟩
    · apply auxiliary_representatives H row hr survivors parts indices part.normalized F U (81/100) 0 (Or.inl ⟨rfl,rfl⟩)
      · intro i hi
        have bound := (pcost i hi).trans (mul_le_mul_of_nonneg_right
          (show (P.card:ℝ) ≤ 2 by exact_mod_cast p) (show 0 ≤ (81/200:ℝ)*r by positivity))
        linarith only [bound]
      · simp [U,q,d]
    · apply auxiliary_representatives H row hr survivors parts indices part.normalized F U (81/200) (43/100) (Or.inr ⟨rfl,rfl⟩)
      · intro i hi
        simpa using (pcost i hi).trans (mul_le_mul_of_nonneg_right
          (show (P.card:ℝ) ≤ 1 by exact_mod_cast p) (show 0 ≤ (81/200:ℝ)*r by positivity))
      · have bound := totalCost.trans (mul_le_mul_of_nonneg_right
          (show (Q.card:ℝ)+D.card ≤ 2 by exact_mod_cast qd) (show 0 ≤ (43/200:ℝ)*r by positivity))
        linarith only [bound]
  obtain ⟨R,hR,ind,im⟩ := reps
  refine ⟨R,hR.trans sdiff_subset,ind,im,?_⟩
  intro x hx v hv edge
  obtain ⟨xA,out⟩ := mem_sdiff.mp (hR hx)
  have xin : x ∈ allowed := mem_filter.mpr ⟨xA,im ▸ mem_image_of_mem row hx⟩
  have member : x ∈ N v := mem_filter.mpr ⟨xin,edge⟩
  rcases mem_union.mp hv with pq | d
  · rcases mem_union.mp pq with p | q
    · exact out (mem_union_left _ (mem_biUnion.mpr ⟨v,p,mem_filter.mpr ⟨xA,edge⟩⟩))
    · obtain ⟨u,hu,rfl⟩ := mem_image.mp q
      exact out (mem_union_right _ (mem_union_left _ (mem_biUnion.mpr ⟨u,hu,member⟩)))
  · exact out (mem_union_right _ (mem_union_right _ (mem_biUnion.mpr ⟨v,d,member⟩)))

end
end Erdos617.ColoredLists
