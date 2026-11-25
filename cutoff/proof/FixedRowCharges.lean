import Mathlib.Tactic

/-! Local inequalities for the fixed-row and untrimmed arguments in Erdős 617. -/

namespace Erdos617.FixedRowCharges

/-- The surplus on the chosen parts is covered by their number and squared
size deviations whenever their coefficients have product at least one quarter. -/
theorem chosen_surplus {u v q s t : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hq : 0 ≤ q) (hs : 0 ≤ s)
    (ht : t ^ 2 ≤ q * s) (hc : 1 ≤ 4 * u * v) :
    t ≤ u * q + v * s := by
  have hqs : 0 ≤ q * s := mul_nonneg hq hs
  have hmul := mul_nonneg (sub_nonneg.mpr hc) hqs
  have hdiff := sq_nonneg (u * q - v * s)
  have hsq : t ^ 2 ≤ (u * q + v * s) ^ 2 := by
    nlinarith only [ht, hmul, hdiff]
  have hpos : 0 ≤ u * q + v * s := add_nonneg (mul_nonneg hu hq) (mul_nonneg hv hs)
  by_contra! h
  nlinarith only [hsq, mul_pos (sub_pos.mpr h) (by linarith : 0 < t + (u*q+v*s))]

/-- Completing the square after reserving the baseline part of each heavy load. -/
theorem excess_square {a t x z : ℝ} (ha : 0 ≤ a) (hd : 0 < 2 - a * t ^ 2) :
    (a * t * x + z) ^ 2 / 2 - a * x ^ 2 ≤ z ^ 2 / (2 - a * t ^ 2) := by
  apply (le_div_iff₀ hd).2
  nlinarith only [mul_nonneg ha (sq_nonneg ((2-a*t^2)*x-t*z))]

/-- Short rows and residual interpart edges pay the cost of omitted destinations. -/
theorem fixed_pair_charge {D C k A B E f w z q L : ℝ}
    (hD : D ≤ C + k*q - A*f - B*w - E*z)
    (hfw : w ≤ f) (hA : 0 ≤ A) (hab : 0 ≤ A + B)
    (hz : 0 ≤ z) (he : (A+B)*L ≤ E) (hq : q ≤ w + L*z) :
    D ≤ C - (A+B-k)*q := by
  nlinarith only [hD, mul_nonneg hA (sub_nonneg.mpr hfw),
    mul_nonneg hab (sub_nonneg.mpr hq), mul_nonneg hz (sub_nonneg.mpr he)]

end Erdos617.FixedRowCharges
