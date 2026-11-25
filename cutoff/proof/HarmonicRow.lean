import Mathlib.Tactic

/-! Local inequalities for the harmonic-row supplement to Erdős problem 617. -/

namespace Erdos617.HarmonicRow

/-- Minimum residual degree forces enough forward neighbors to pay for all
missing neighbors in a pivot's closed neighborhood. -/
theorem forward_neighbors {part withinCount later : ℕ}
    (hmin : part - 1 ≤ withinCount + later) : part - 1 - withinCount ≤ later := by omega

/-- The other colors' requirements bound the excess of an overfull original part
in terms of the core's foreign edge count and its squared deficit. -/
theorem excess_of_part {r d b y : ℝ} (hr : 0 < r) (hb : 0 ≤ b) (hholes : 0 ≤ d + b)
    (hspace : r / 2 ≤ r - 1 - d - b / 2)
    (hcap : (r - 1) * b ≤ y * r ^ 2 + (d + b) * (d + b - 1) / 2) :
    b ≤ 2 * r * y + d ^ 2 / r := by
  apply (mul_le_mul_iff_of_pos_right hr).mp
  rw [add_mul, div_mul_cancel₀ _ hr.ne']
  nlinarith [mul_nonneg hb (sub_nonneg.mpr hspace)]

/-- The retry at probability 80ρ pays an additional tρ per unit nonneighbor
fraction. The proof uses the actual neighbor fraction q of this sender. -/
theorem retry_with_surplus {ρ x q g t : ℝ} (hρ : 0 ≤ ρ) (hρ' : ρ ≤ 1)
    (hq : 1 / 2 ≤ q) (hq' : q ≤ 1) (hx : x ≤ g * ρ)
    (hbudget : g + 1 + t ≤ 40 * (1 - ρ)) :
    let v := (1 - q) * (1 + 80 * ρ * q)
    1 - v + ρ * v + 2 * x * (1 - q) + t * ρ * (1 - q) ≤ (1 - x) * q + x := by
  dsimp
  have hgain : g ≤ 80 * q * (1 - ρ) - 1 - t := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hq) (sub_nonneg.mpr hρ')]
  have hfactor : 0 ≤ ρ * (80 * q * (1 - ρ) - 1 - t) - x := by
    nlinarith [mul_nonneg hρ (sub_nonneg.mpr hgain)]
  nlinarith only [mul_nonneg (sub_nonneg.mpr hq') hfactor]

end Erdos617.HarmonicRow
