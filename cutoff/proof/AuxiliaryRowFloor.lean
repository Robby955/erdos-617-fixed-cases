import AuxiliaryMoments

/-! The cost of the second, auxiliary pruning in Appendix A §4. -/

namespace Erdos617.AuxiliaryMoments

open Finset PackingLists RowExtraction GraphPartitionCount
open scoped Classical
noncomputable section

/-- Completing the square gives a joint bound on one raw row deficit and
all subsequent deletions. Both are measured in units of r. -/
theorem deficit_plus_deletions {u z x : ℝ}
    (budget : x+u^2 ≤ (3/20:ℝ)^2+1/2^20) (paid : (43/200:ℝ)*z ≤ x) :
    u+z ≤ ((3/20:ℝ)^2+1/2^20)/(43/200)+(43/200)/4 := by
  nlinarith only [budget,paid,sq_nonneg (u-43/400)]

/-- Every auxiliary row retains at least 21r/25 actual vertices. -/
theorem live_row_floor {W : Type*} [Fintype W] (G : SimpleGraph W) (row : W → ℕ)
    (A : Finset W) (h r : ℕ) (pos : 0 < r)
    (budget : ((cross G row).edgeFinset.card:ℝ)/(r:ℝ)^2 +
      (∑ i ∈ range h, (max (1-(size row i:ℝ)/r) 0)^2) ≤ (3/20:ℝ)^2+1/2^20)
    (paid : (43/200:ℝ)*r*((Fintype.card W:ℝ)-A.card) ≤ (cross G row).edgeFinset.card)
    (i : ℕ) (hi : i < h) : (21/25:ℝ)*r ≤ (fiber A row i).card := by
  let u := max (1-(size row i:ℝ)/r) 0
  let z := ((Fintype.card W:ℝ)-A.card)/r
  let x := ((cross G row).edgeFinset.card:ℝ)/(r:ℝ)^2
  have rp : (0:ℝ)<r := by exact_mod_cast pos
  have part : u^2 ≤ ∑ j ∈ range h, (max (1-(size row j:ℝ)/r) 0)^2 :=
    single_le_sum (fun j _ ↦ sq_nonneg (max (1-(size row j:ℝ)/r) 0)) (mem_range.mpr hi)
  have b : x+u^2 ≤ (3/20:ℝ)^2+1/2^20 := (add_le_add_right part x).trans budget
  have pay : (43/200:ℝ)*z ≤ x := by
    apply (le_div_iff₀ (sq_pos_of_pos rp)).2
    convert paid using 1
    dsimp [z]
    field_simp
  have loss := deficit_plus_deletions b pay
  have floor : 1-(size row i:ℝ)/r+z ≤ 4/25 := by
    have h := le_max_left (1-(size row i:ℝ)/r) 0
    change _ ≤ u at h
    linarith only [loss,h]
  have survive : size row i ≤ (fiber A row i).card+(univ \ A).card := by
    have cov : fiber univ row i ⊆ fiber A row i ∪ (univ \ A) := by
      intro v hv
      by_cases mem : v ∈ A
      · exact mem_union_left _ (mem_filter.mpr ⟨mem,(mem_filter.mp hv).2⟩)
      · exact mem_union_right _ (mem_sdiff.mpr ⟨mem_univ _,mem⟩)
    exact (card_le_card cov).trans (card_union_le ..)
  have del := card_sdiff_add_card_eq_card (subset_univ A)
  rw [card_univ] at del
  have lo : (size row i:ℝ) ≤ (fiber A row i).card+(Fintype.card W-A.card:ℕ) := by
    exact_mod_cast (show size row i ≤ (fiber A row i).card+(Fintype.card W-A.card) by omega)
  rw [Nat.cast_sub (card_le_univ _)] at lo
  change 1-_/ (r:ℝ) + ((Fintype.card W:ℝ)-A.card)/r ≤ 4/25 at floor
  field_simp at floor
  linarith only [floor,lo]

end
end Erdos617.AuxiliaryMoments
