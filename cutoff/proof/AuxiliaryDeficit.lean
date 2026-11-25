import GraphPartitionCount

/-! Total positive deficit of an auxiliary pivot partition on hr+b vertices. -/

namespace Erdos617.GraphPartitionCount

open Finset ColoredLists RowExtraction PackingLists
open scoped Classical
noncomputable section

variable {V : Type*} {r : ℕ} [Fintype V]

/-- Every excess vertex in an overfull row costs one edge of each other
color. The pivot budget pays for these internal edges, and the signed
sum of the row sizes then bounds all underfull rows together. -/
theorem auxiliary_deficit (color : {e : Sym2 V // ¬e.IsDiag} → Fin r) (j : Fin r)
    (row : V → ℕ) (h : ℕ) (b : ℝ) (hr : 2 ≤ r) (no : ¬Witness color)
    (order : (Fintype.card V:ℝ) = (h:ℝ)*r+b) (covers : ∀ x, row x < h)
    (pivots : ∀ i < h, RowStep (targetGraph color j)ᶜ (fiber univ row i) (laterRows univ row i)) :
    (∑ i ∈ range h, max ((r:ℝ)-size row i) 0) ≤ -b +
      ((cross (targetGraph color j) row).edgeFinset.card:ℝ)/(2*((r:ℝ)-1)) := by
  let G := targetGraph color j
  have per (i : ℕ) : ((r:ℝ)-1)*max ((size row i:ℝ)-r) 0 ≤
      ((Gᶜ.induce (fiber univ row i:Set V)).edgeFinset.card:ℝ) := by
    by_cases hs : r ≤ size row i
    · rw [max_eq_left (sub_nonneg.mpr (by exact_mod_cast hs))]
      have raw := other_color_floor color j (fiber univ row i) hr no
      have converted : (((r-1)*(size row i-r):ℕ):ℝ) ≤
          ((Gᶜ.induce (fiber univ row i:Set V)).edgeFinset.card:ℝ) := by
        apply Nat.cast_le.mpr
        convert raw using 2
        rfl
      simpa only [Nat.cast_mul,Nat.cast_sub (show 1 ≤ r by omega),Nat.cast_sub hs,Nat.cast_one]
        using converted
    · rw [max_eq_right (sub_nonpos.mpr (by exact_mod_cast (le_of_not_ge hs))), mul_zero]
      exact Nat.cast_nonneg _
  have charge := sum_le_sum (s := range h) (fun i _ ↦ per i)
  rw [← mul_sum] at charge
  have cross := pivot_missing_budget G row h covers pivots
  have total : (∑ i ∈ range h, (size row i:ℝ)) = (h:ℝ)*r+b := by
    rw [← Nat.cast_sum, sum_sizes row h covers, order]
  have difference (i : ℕ) : max ((size row i:ℝ)-r) 0 - max ((r:ℝ)-size row i) 0 =
      (size row i:ℝ)-r := by
    by_cases hx : (r:ℝ) ≤ size row i
    · rw [max_eq_left (sub_nonneg.mpr hx),max_eq_right (sub_nonpos.mpr hx),sub_zero]
    · rw [max_eq_right (sub_nonpos.mpr (le_of_not_ge hx)),max_eq_left (sub_nonneg.mpr (le_of_not_ge hx))]
      ring
  have net := sum_congr (s₁ := range h) rfl (fun i _ ↦ difference i)
  simp only [sum_sub_distrib,sum_const,card_range,nsmul_eq_mul,total] at net
  have positive : 0 < 2*((r:ℝ)-1) := by
    have rr : (2:ℝ) ≤ r := by exact_mod_cast hr
    linarith
  have paid : (∑ i ∈ range h, max ((size row i:ℝ)-r) 0) ≤
      ((PackingLists.cross G row).edgeFinset.card:ℝ)/(2*((r:ℝ)-1)) := by
    apply (le_div_iff₀ positive).mpr
    nlinarith only [charge,cross]
  change _ ≤ -b + ((PackingLists.cross G row).edgeFinset.card:ℝ)/_
  linarith only [net,paid]

end
end Erdos617.GraphPartitionCount
