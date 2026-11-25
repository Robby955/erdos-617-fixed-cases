import Mathlib.Tactic

/-! Local inequalities for the mixed harmonic row proof of Erdős problem 617. -/

namespace Erdos617.MixedRowCut

/-- A short list pays for its missed selection even when the cutoff is above
half a row. Sizes are expressed as fractions of a row. -/
theorem short_list {m L τ : ℝ} (hm : 0 ≤ m) (hL : 0 < L) (hL' : L ≤ 1)
    (hmL : m ≤ L) (hτ : 2 * τ ≤ 1) :
    2 * τ * (1 - m / L) ≤ 1 - m := by
  have hprob : m / L ≤ 1 := (div_le_one hL).2 hmL
  have hmass : m ≤ m / L := (le_div_iff₀ hL).2 (by nlinarith [mul_nonneg hm (sub_nonneg.mpr hL')])
  calc
    2 * τ * (1 - m / L) ≤ 1 * (1 - m / L) :=
      mul_le_mul_of_nonneg_right hτ (sub_nonneg.mpr hprob)
    _ ≤ 1 - m := by linarith

/-- Per actual edge between tested rows, its testing weight pays for the two
possible directions of representative loads and a representative-pair term. -/
theorem tested_edge {a b j n m p q : ℝ} (ha : 0 ≤ a) (hb : j ≤ b)
    (hn : 0 ≤ n) (hm : 0 ≤ m) (hp : 0 ≤ p) (hq : 0 ≤ q) :
    a * j * (n * q + m * p) + b ^ 2 * p * q ≤
      (a * n + b * p) * (a * m + b * q) := by
  have hload : 0 ≤ n * q + m * p := by positivity
  have hcross := mul_nonneg (mul_nonneg ha (sub_nonneg.mpr hb)) hload
  nlinarith only [hcross, mul_nonneg (sq_nonneg a) (mul_nonneg hn hm)]

/-- The capacity comparison for arrivals is weakest at the largest allowed
deficit after charging each arrival for its own row's deficit. -/
theorem arrival_price {θ d δ p : ℝ} (hd : d ≤ δ) (hθ : 2 * (θ - p) ≤ 1) :
    2 * (θ - p) * (δ + p) - δ ≤
      θ * (2 * (d + p)) - (1 - 2 * (d + p)) * d - (2 * (d + p)) ^ 2 / 2 := by
  nlinarith only [mul_nonneg (sub_nonneg.mpr hd) (sub_nonneg.mpr hθ)]

end Erdos617.MixedRowCut
