import RawColorRows

/-! The sum of the pivot bounds in Appendix A (1). -/

namespace Erdos617.ColoredLists

open Finset RowExtraction PruningOverlap
open scoped Classical
noncomputable section

variable {V : Type*} {r : ℕ} [Fintype V] (T : Trace V r)

/-- On each unordered cross-row target edge, exactly one orientation goes from
the earlier row to the later row. -/
theorem sum_forwardDegree (rows : ∀ x, T.row x < r) :
    (∑ i ∈ range r, ∑ x ∈ fiber univ T.row i, (forwardDegree T i x : ℝ)) =
      (T.crossGraph.edgeFinset.card : ℝ) := by
  let f (x y : V) : ℝ := if T.row x < T.row y ∧ T.crossGraph.Adj x y then 1 else 0
  have earlier (x y : V) : (T.row x < T.row y ∧ T.crossGraph.Adj x y) ↔
      (T.row x < T.row y ∧ (targetGraph T.color T.target).Adj x y) := by
    rw [← cross_target T]
    exact ⟨fun ⟨h,_,e⟩ ↦ ⟨h,e⟩, fun ⟨h,e⟩ ↦ ⟨h,h.ne,e⟩⟩
  have rowSum (x : V) : (forwardDegree T (T.row x) x : ℝ) = ∑ y, f x y := by
    simp [f, earlier, forwardDegree, laterRows, Finset.filter_filter]
  have replace (i : ℕ) : (∑ x ∈ fiber univ T.row i, (forwardDegree T i x : ℝ)) =
      ∑ x ∈ fiber univ T.row i, (forwardDegree T (T.row x) x : ℝ) :=
    sum_congr rfl fun x hx ↦ by rw [(mem_filter.mp hx).2]
  have both (x y : V) : f x y + f y x = if T.crossGraph.Adj x y then 1 else 0 := by
    by_cases h : T.crossGraph.Adj x y
    · have ne : T.row x ≠ T.row y := h.choose
      have rev := T.crossGraph.adj_symm h
      rcases lt_or_gt_of_ne ne with lt | gt
      · simp [f,h,rev,lt,not_lt.mpr lt.le]
      · simp [f,h,rev,gt,not_lt.mpr gt.le]
    · have rev : ¬ T.crossGraph.Adj y x := fun e ↦ h (T.crossGraph.adj_symm e)
      simp [f,h,rev]
  have twice : (∑ x, ∑ y, (f x y + f y x)) = 2*(T.crossGraph.edgeFinset.card : ℝ) := by
    simp_rw [both]
    have deg (x : V) :
        (∑ y, if T.crossGraph.Adj x y then (1:ℝ) else 0) = T.crossGraph.degree x := by
      simp [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter]
    simp_rw [deg]
    exact_mod_cast T.crossGraph.sum_degrees_eq_twice_card_edges
  simp only [Finset.sum_add_distrib] at twice
  rw [Finset.sum_comm (f := fun x y ↦ f y x)] at twice
  simp_rw [replace]
  unfold fiber
  rw [sum_fiberwise_of_maps_to (fun x _ ↦ mem_range.mpr (rows x))]
  simp_rw [rowSum]
  linarith

/-- Twice the internal nontarget edge count is paid for by the inter-row
target edges of the same coloring. -/
theorem pivot_cross_count (rows : ∀ x, T.row x < r) (pivots : PivotRows T.color T.target T.row) :
    2*(∑ i ∈ range r, (internalMissing T i : ℝ)) ≤ (T.crossGraph.edgeFinset.card : ℝ) := by
  rw [← sum_forwardDegree T rows, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have step := (pivots i (mem_range.mp hi)).forward
  have count : 2*internalMissing T i ≤ ∑ x ∈ fiber univ T.row i, forwardDegree T i x := by
    convert step using 1
    · unfold internalMissing
      dsimp only [fiber]
      congr 5
      exact Subsingleton.elim _ _
    · apply Finset.sum_congr rfl
      intro x _
      apply congrArg Finset.card
      refine @Finset.filter_congr V _ _ ?_ ?_ _ ?_
      intro y _
      rw [compl_compl]
  exact_mod_cast count

end
end Erdos617.ColoredLists
