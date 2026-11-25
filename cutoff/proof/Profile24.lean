import Mathlib.Tactic

/-! Local real inequalities for the smaller mixed profile in Erdős problem 617. -/

namespace Erdos617.Profile24

/-- With a fixed total loss, charging both lists against the longer list
gives a lower bound for their surviving product. -/
theorem surviving_product {a b s t : ℝ} (hab : a ≤ b) (hs : 0 ≤ s)
    (ht : 0 ≤ t) :
    b * (a - s - t) ≤ (a - s) * (b - t) := by
  nlinarith only [mul_nonneg (sub_nonneg.mpr hab) ht, mul_nonneg hs ht]

/-- The two-small-attachment test uses the sum of the two raw deficits. -/
theorem two_list_margin {w d e D T : ℝ} (hs : d + e ≤ D) (hw : D ≤ w)
    (hT : T < w ^ 2 + (w - D) ^ 2) :
    T < 2 * (w - d) * (w - e) + d ^ 2 + e ^ 2 := by
  have hp : 0 ≤ (D - (d + e)) * ((w - d - e) + (w - D)) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith only [hp, hT]

/-- The remaining edge budget and the lower bound on a list product are
affine in the number pruned. Positivity at both ends suffices. -/
theorem affine_margin {A B x u : ℝ} (hu : 0 ≤ u) (hx : u ≤ x)
    (h0 : 0 < A) (h1 : 0 < A + B * x) : 0 < A + B * u := by
  by_cases hB : 0 ≤ B
  · linarith [mul_nonneg hB hu]
  · linarith [mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hB) (sub_nonneg.mpr hx)]

/-- An upper bound on the missing-neighbor charge and one on oversampling
combine into an upper bound for the deficit-weighted number of unique senders. -/
theorem unique_charge {W D M g L Z : ℝ} (hg : 0 ≤ g)
    (hW : W ≤ D + g * M) (hM : 37 * M ≤ L + Z) :
    W ≤ D + g * (L + Z) / 37 := by
  nlinarith only [hW, mul_nonneg hg (sub_nonneg.mpr hM)]

end Erdos617.Profile24
