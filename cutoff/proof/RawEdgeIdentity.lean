import RawColorRows

/-! Edge accounting on the full ordered raw partition, Appendix A (1). -/

namespace Erdos617.ColoredLists

open Finset PackingLists PruningOverlap
open scoped Classical
noncomputable section

variable {V : Type*} {r : ℕ}

/-- The ordered end at x of the edge joining x and y. -/
private def edgeEnd (G : SimpleGraph V) (x y : V) : ℝ := if G.Adj x y then 1 else 0

private theorem end_sum [Fintype V] (G : SimpleGraph V) :
    (∑ x, ∑ y, edgeEnd G x y) = 2*(G.edgeFinset.card:ℝ) := by
  have per (x : V) : (∑ y, edgeEnd G x y) = (G.degree x:ℝ) := by
    simp [edgeEnd, ← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter]
  simp_rw [per]
  exact_mod_cast G.sum_degrees_eq_twice_card_edges

private theorem part_sum (G : SimpleGraph V) (A : Finset V) :
    (∑ x ∈ A, ∑ y ∈ A, edgeEnd G x y) = 2*((G.induce (A:Set V)).edgeFinset.card:ℝ) := by
  have per (x y : A) : edgeEnd (G.induce (A:Set V)) x y = edgeEnd G x y := by
    simp [edgeEnd]
  have h := end_sum (G.induce (A:Set V))
  simp_rw [per] at h
  calc (∑ x ∈ A, ∑ y ∈ A, edgeEnd G x y) = ∑ x : A, ∑ y ∈ A, edgeEnd G x y :=
         (Finset.sum_coe_sort A _).symm
       _ = ∑ x : A, ∑ y : A, edgeEnd G x y := by
         exact sum_congr rfl fun x _ ↦ (Finset.sum_coe_sort A (edgeEnd G x)).symm
       _ = _ := by convert h using 2; congr 4

/-- Count both ends of every edge in the induced graph. -/
theorem internal_end_sum (G : SimpleGraph V) (A : Finset V) :
    (∑ x ∈ A, ∑ y ∈ A, if G.Adj x y then (1:ℝ) else 0) =
      2*((G.induce (A:Set V)).edgeFinset.card:ℝ) := part_sum G A

variable [Fintype V] (T : Trace V r)

/-- In each raw row count every ordered pair of distinct vertices. Removing
the two ends of each internal nontarget edge leaves the internal target ends.
The cross graph contributes all remaining target ends. -/
theorem raw_edge_identity (rows : ∀ x, T.row x < r) :
    2*((targetGraph T.color T.target).edgeFinset.card:ℝ) =
      (∑ i ∈ range r, (T.rowSize i:ℝ)*((T.rowSize i:ℝ)-1)) -
      2*(∑ i ∈ range r, (internalMissing T i:ℝ)) + 2*(T.crossGraph.edgeFinset.card:ℝ) := by
  let G := targetGraph T.color T.target
  let part := fun i ↦ univ.filter (fun x ↦ T.row x = i)
  have tally (i : ℕ) (x : V) (hx : x ∈ part i) :
      (∑ y, edgeEnd G x y) + (∑ y ∈ part i, edgeEnd Gᶜ x y) + 1 =
        T.rowSize i + ∑ y, edgeEnd T.crossGraph x y := by
    have rowx : T.row x = i := (mem_filter.mp hx).2
    have entry (y : V) : edgeEnd G x y + (if T.row y = i then edgeEnd Gᶜ x y else 0) +
        (if y = x then (1:ℝ) else 0) =
        (if T.row y = i then (1:ℝ) else 0) + edgeEnd T.crossGraph x y := by
      have test : T.crossGraph.Adj x y ↔ T.row x ≠ T.row y ∧ G.Adj x y := by
        rw [← cross_target T]; rfl
      simp only [edgeEnd, test, SimpleGraph.compl_adj, rowx]
      by_cases he : x = y
      · subst y; simp [rowx]
      · by_cases hy : T.row y = i <;> by_cases h : G.Adj x y <;> simp_all [eq_comm]
    have h := sum_congr (s₁ := (univ:Finset V)) rfl (fun y _ ↦ entry y)
    simp only [sum_add_distrib,sum_ite_eq',mem_univ,ite_true] at h
    simpa only [part, sum_filter, Trace.rowSize, ← Finset.sum_boole] using h
  have row_count (i : ℕ) :
      (∑ x ∈ part i, ∑ y, edgeEnd G x y) + 2*(internalMissing T i:ℝ) =
        (T.rowSize i:ℝ)*((T.rowSize i:ℝ)-1) + ∑ x ∈ part i, ∑ y, edgeEnd T.crossGraph x y := by
    have h := sum_congr (s₁ := part i) rfl (tally i)
    simp only [sum_add_distrib,sum_const,nsmul_eq_mul,mul_one] at h
    have hin : (∑ x ∈ part i, ∑ y ∈ part i, edgeEnd Gᶜ x y) = 2*(internalMissing T i:ℝ) := by
      convert part_sum Gᶜ (part i) using 2
      dsimp only [G,part,internalMissing]
      congr 4
      exact Subsingleton.elim _ _
    rw [hin] at h
    have size : (part i).card = T.rowSize i := rfl
    rw [size] at h
    linarith only [h]
  have gather (H : SimpleGraph V) : (∑ i ∈ range r, ∑ x ∈ part i, ∑ y, edgeEnd H x y) =
      2*(H.edgeFinset.card:ℝ) :=
    (sum_fiberwise_of_maps_to (fun x _ ↦ mem_range.mpr (rows x)) (fun x ↦ ∑ y, edgeEnd H x y)).trans
      (end_sum H)
  have h := sum_congr (s₁ := range r) rfl (fun i _ ↦ row_count i)
  simp only [sum_add_distrib, ← mul_sum, gather] at h
  change 2*(G.edgeFinset.card:ℝ) = _
  linarith only [h]

end
end Erdos617.ColoredLists
