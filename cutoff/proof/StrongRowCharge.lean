import Mathlib.Tactic

/-! The two row inequalities used in §3 of the cutoff supplement. -/

namespace Erdos617.StrongRowCharge

/-- A second draw on a fraction of first-draw failures pays the charge for a success
and the row's surplus. Degrees and deficits are normalized by the order parameter. -/
theorem retry_charge {x q ρ : ℝ} (hq : 1 / 2 ≤ q) (hq' : q ≤ 1)
    (hρ : 0 ≤ ρ) (hρ' : ρ ≤ 1) (hx : x ≤ (3 * (1 - ρ) - 1) * ρ) :
    let v := (1 - q) * (1 + 6 * ρ * q)
    1 - v + ρ * v + 2 * x * (1 - q) ≤ (1 - x) * q + x := by
  dsimp
  have hfactor : 0 ≤ ρ * (6 * q * (1 - ρ) - 1) - x := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hq) (mul_nonneg hρ (sub_nonneg.mpr hρ'))]
  nlinarith [mul_nonneg (sub_nonneg.mpr hq') hfactor]

/-- Equation (5), with the numerical rounding in its stated hypothesis.
Here b counts strong assignments, d is the deficit, v is the mean moderate
assignment count, x is the normalized deficit, and j is the strong surplus. -/
theorem row_charge {b d v x j : ℝ} (hb : 0 ≤ b) (hd : 0 ≤ d) (hv : 0 ≤ v)
    (hbd : b ≤ 2 * d) (hj : 0 ≤ j) (hx : x < 1)
    (hsmall : 2 * x / (1 - x) ≤ 1 / 1000)
    (hsurplus : 2 * d * (b - d / (1 - x)) ≤ j) :
    b ^ 2 / 2 + (b - d) * v - j ≤ (501 / 1000) * d ^ 2 + v ^ 2 / 2 := by
  by_cases h : b ≤ d
  · nlinarith [mul_nonneg (sub_nonneg.mpr h) (add_nonneg hd hb),
      mul_nonneg (sub_nonneg.mpr h) hv, sq_nonneg v, sq_nonneg d]
  · have hsplit : 2 * d * (b - d) =
          2 * d * (b - d / (1 - x)) + (2 * x / (1 - x)) * d ^ 2 := by
      field_simp [ne_of_gt (sub_pos.mpr hx)]
      ring
    have hbudget : 2 * d * (b - d) ≤ j + (1 / 1000) * d ^ 2 := by
      rw [hsplit]
      exact add_le_add hsurplus (mul_le_mul_of_nonneg_right hsmall (sq_nonneg d))
    have hproduct := mul_nonneg (sub_nonneg.mpr (le_of_not_ge h)) (sub_nonneg.mpr hbd)
    nlinarith [hbudget, hproduct, sq_nonneg (v - (b - d))]

end Erdos617.StrongRowCharge
