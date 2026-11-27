import RawColorRows

/-! The full-graph row moments in Appendix A, equation (1). -/

namespace Erdos617.ColoredLists

open Finset PackingLists PruningOverlap
open scoped Classical
noncomputable section

variable {V : Type*} {r : ℕ} [Fintype V] (T : Trace V r)

private theorem sum_row_sizes (rows : ∀ x, T.row x < r) :
    ∑ i ∈ range r, (T.rowSize i:ℝ) = Fintype.card V := by
  have h := Finset.card_eq_sum_card_fiberwise (s := (univ:Finset V)) (t := range r)
    (f := T.row) (fun x _ ↦ mem_range.mpr (rows x))
  simpa only [← Nat.cast_sum, Trace.rowSize, card_univ] using
    (congrArg (Nat.cast (R := ℝ)) h.symm)

private theorem sum_deviations (order : Fintype.card V = r^2+1) (rows : ∀ x, T.row x < r) :
    ∑ i ∈ range r, ((T.rowSize i:ℝ)-r) = 1 := by
  rw [Finset.sum_sub_distrib,sum_row_sizes T rows,order]
  simp
  ring

private theorem square_mass (order : Fintype.card V = r^2+1) (rows : ∀ x, T.row x < r) :
    1 ≤ ∑ i ∈ range r, ((T.rowSize i:ℝ)-r)^2 := by
  rw [← sum_deviations T order rows]
  apply sum_le_sum
  intro i _
  by_cases h : T.rowSize i ≤ r
  · exact le_trans (sub_nonpos.mpr (by exact_mod_cast h)) (sq_nonneg _)
  · have h' : (r:ℝ)+1 ≤ T.rowSize i := by exact_mod_cast (show r+1 ≤ T.rowSize i by omega)
    nlinarith only [mul_nonneg (sub_nonneg.mpr h') (show (0:ℝ) ≤ T.rowSize i-r by linarith)]

private theorem pair_mass (order : Fintype.card V = r^2+1) (rows : ∀ x, T.row x < r) :
    (∑ i ∈ range r, (T.rowSize i:ℝ)*((T.rowSize i:ℝ)-1)) =
      (∑ i ∈ range r, ((T.rowSize i:ℝ)-r)^2) + (r:ℝ)^3-r^2+2*r-1 := by
  have h (i : ℕ) : (T.rowSize i:ℝ)*((T.rowSize i:ℝ)-1) =
      ((T.rowSize i:ℝ)-r)^2+(2*(r:ℝ)-1)*((T.rowSize i:ℝ)-r)+((r:ℝ)^2-r) := by ring
  simp_rw [h,Finset.sum_add_distrib, ← Finset.mul_sum, sum_deviations T order rows]
  simp
  ring

/-- The extra vertex supplies the unit correction in the full-graph form of
(1). Both the cross count and twice the internal missing count pay the square mass. -/
theorem raw_stability_of_counts (hr : 2 ≤ r) (order : Fintype.card V = r^2+1)
    (rows : ∀ x, T.row x < r)
    (identity : 2*((targetGraph T.color T.target).edgeFinset.card:ℝ) =
      (∑ i ∈ range r, (T.rowSize i:ℝ)*((T.rowSize i:ℝ)-1)) -
      2*(∑ i ∈ range r, (internalMissing T i:ℝ)) + 2*(T.crossGraph.edgeFinset.card:ℝ))
    (pivot : 2*(∑ i ∈ range r, (internalMissing T i:ℝ)) ≤ (T.crossGraph.edgeFinset.card:ℝ))
    (sparse : (r:ℝ)*2*((targetGraph T.color T.target).edgeFinset.card:ℝ) ≤
      (Fintype.card V:ℝ)*((Fintype.card V:ℝ)-1)) :
    let B := (r:ℝ)^2-r+1-∑ i ∈ range r, ((T.rowSize i:ℝ)-r)^2
    (T.crossGraph.edgeFinset.card:ℝ) ≤ B ∧
      2*(∑ i ∈ range r, (internalMissing T i:ℝ)) ≤ B := by
  have pos : (0:ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  rw [order] at sparse
  push_cast at sparse
  have cap : 2*((targetGraph T.color T.target).edgeFinset.card:ℝ) ≤ (r:ℝ)^3+r := by
    apply le_of_mul_le_mul_left _ pos
    nlinarith only [sparse]
  rw [pair_mass T order rows] at identity
  dsimp only
  constructor <;> linarith only [cap,identity,pivot]

/-- Sparsity and the extra vertex force this many missing edges within the
raw rows, before any pruning or choice of representatives. -/
theorem missing_floor_of_counts (hr : 0 < r) (order : Fintype.card V = r^2+1)
    (rows : ∀ x, T.row x < r)
    (identity : 2*((targetGraph T.color T.target).edgeFinset.card:ℝ) =
      (∑ i ∈ range r, (T.rowSize i:ℝ)*((T.rowSize i:ℝ)-1)) -
      2*(∑ i ∈ range r, (internalMissing T i:ℝ)) + 2*(T.crossGraph.edgeFinset.card:ℝ))
    (sparse : (r:ℝ)*2*((targetGraph T.color T.target).edgeFinset.card:ℝ) ≤
      (Fintype.card V:ℝ)*((Fintype.card V:ℝ)-1)) :
    (T.crossGraph.edgeFinset.card:ℝ) - (r:ℝ)^2/2 ≤
      ∑ i ∈ range r, (internalMissing T i:ℝ) := by
  have pos : (0:ℝ) < r := by exact_mod_cast hr
  rw [order] at sparse
  push_cast at sparse
  have cap : 2*((targetGraph T.color T.target).edgeFinset.card:ℝ) ≤ (r:ℝ)^3+r := by
    apply le_of_mul_le_mul_left _ pos
    nlinarith only [sparse]
  rw [pair_mass T order rows] at identity
  linarith only [cap,identity,square_mass T order rows,pos]

/-- The three normalized raw budgets, retaining the variance rebate in the
total unused allowance. -/
theorem budgets_of_stability (hr : 2 ≤ r) (order : Fintype.card V = r^2+1)
    (rows : ∀ x, T.row x < r) (no : ¬Witness T.color)
    (cross : (T.crossGraph.edgeFinset.card:ℝ) ≤ (r:ℝ)^2-r+1-∑ i ∈ range r, ((T.rowSize i:ℝ)-r)^2)
    (missing : 2*(∑ i ∈ range r, (internalMissing T i:ℝ)) ≤
      (r:ℝ)^2-r+1-∑ i ∈ range r, ((T.rowSize i:ℝ)-r)^2) :
    (∑ i ∈ range r, rawSurplus T i) ≤ 1/2 ∧
      (∑ i ∈ range r, unused T i) ≤ (1-variance T)/2 ∧
      (T.crossGraph.edgeFinset.card:ℝ) ≤ (1-variance T)*(r:ℝ)^2 := by
  have hr' : (2:ℝ) ≤ r := by exact_mod_cast hr
  have pos : (0:ℝ) < r := by linarith
  have square := square_mass T order rows
  have normalize : (1-variance T)*(r:ℝ)^2 =
      (r:ℝ)^2 - ∑ i ∈ range r, ((T.rowSize i:ℝ)-r)^2 := by
    unfold variance
    field_simp
  have per (i : ℕ) : ((r:ℝ)-1)*r*rawSurplus T i ≤ internalMissing T i := by
    have hu := unused_nonneg_of_no_witness T hr no i
    unfold unused at hu
    have base := (le_div_iff₀ (sq_pos_of_pos pos)).mp hu
    simp only [zero_mul] at base
    change ((r:ℝ)-1)*r*max ((T.rowSize i:ℝ)/r-1) 0 ≤ _
    by_cases h : 0 ≤ (T.rowSize i:ℝ)/r-1
    · rw [max_eq_left h]
      calc _ = ((r:ℝ)-1)*((T.rowSize i:ℝ)-r) := by field_simp
           _ ≤ _ := by linarith only [base]
    · rw [max_eq_right (le_of_not_ge h),mul_zero]
      exact Nat.cast_nonneg _
  have surplus := Finset.sum_le_sum (s := range r) (fun i _ ↦ per i)
  rw [← Finset.mul_sum] at surplus
  refine ⟨?_,?_,?_⟩
  · apply le_of_mul_le_mul_left _ (mul_pos (show (0:ℝ) < r-1 by linarith) pos)
    nlinarith only [missing,square,surplus]
  · have used : (∑ i ∈ range r, unused T i) =
        ((∑ i ∈ range r, (internalMissing T i:ℝ))-((r:ℝ)-1))/(r:ℝ)^2 := by
      simp only [unused, ← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum,
        sum_deviations T order rows, mul_one]
    rw [used]
    apply (div_le_iff₀ (sq_pos_of_pos pos)).2
    rw [show (1-variance T)/2*(r:ℝ)^2 = (1-variance T)*(r:ℝ)^2/2 by ring, normalize]
    linarith only [missing,hr']
  · rw [normalize]
    linarith only [cross,hr']

end
end Erdos617.ColoredLists
