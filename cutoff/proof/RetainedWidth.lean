import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-! The five continuous width comparisons in Section 3 of the cutoff paper. -/

namespace Erdos617.RetainedWidth

/-- Each interval for the incidence budget determines a choice of cut parameters. -/
inductive Band : ℝ → ℝ → ℝ → ℝ → Prop where
  | first {y} (lo : 0 ≤ y) (hi : y ≤ 1/2) : Band y 14 (656/4000) (924/4000)
  | second {y} (lo : 1/2 ≤ y) (hi : y ≤ 55/100) : Band y 14 (656/4000) (922/4000)
  | third {y} (lo : 55/100 ≤ y) (hi : y ≤ 68/100) : Band y 14 (652/4000) (916/4000)
  | fourth {y} (lo : 68/100 ≤ y) (hi : y ≤ 1) : Band y 15 (652/4000) (916/4000)
  | fifth {y} (lo : 1 ≤ y) (hi : y ≤ 2) : Band y 17 (654/4000) (918/4000)

private theorem log_normalizer :
    Real.log 1120 ≤ 10 * Real.log 2 + 8963/100000 := by
  have h : Real.log (35/32) ≤ 8963/100000 := by
    apply (Real.log_le_iff_le_exp (by norm_num)).2
    have hexp := Real.sum_le_exp_of_nonneg (x := (8963:ℝ)/100000) (by norm_num) 4
    norm_num [Finset.sum_range_succ, Nat.factorial] at hexp
    linarith
  have heq : (1120:ℝ) = 2^10 * (35/32) := by norm_num
  rw [heq, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  linarith only [h]

/-- The lower bound holds on the whole pruning polygon, including all shared
band endpoints. The cost and both possible savings appear in the conclusion. -/
theorem five_width_comparisons {p t y b α β : ℝ}
    (hp' : p ≤ 125/61) (hpt : p/4 + (199/400)*t ≤ 1)
    (hy : y = 2 - p/2 - (199/400)*t) (band : Band y b α β) :
    7/10000 < Real.log ((2:ℝ)^((144-b)/4) / 1120) - (y/α + (p+t)/β) +
      min ((391 + (1464/5)*p)/1120) ((4333+737*p)/10000) := by
  have hlog := Real.log_two_gt_d9
  have hnorm := log_normalizer
  rw [Real.log_div (by positivity) (by norm_num), Real.log_rpow (by norm_num), add_min]
  cases band <;> apply lt_min <;> linarith

/-- Every feasible pair of pruning parameters falls in a band with positive
width margin at exponent 144. -/
theorem width_for_every_pruning_pair {p t : ℝ}
    (hp : 0 ≤ p) (hp' : p ≤ 125/61) (ht : 0 ≤ t) (hpt : p/4 + (199/400)*t ≤ 1) :
    let y := 2 - p/2 - (199/400)*t
    ∃ b α β, Band y b α β ∧
      7/10000 < Real.log ((2:ℝ)^((144-b)/4) / 1120) - (y/α + (p+t)/β) +
        min ((391 + (1464/5)*p)/1120) ((4333+737*p)/10000) := by
  dsimp only
  let y := 2 - p/2 - (199/400)*t
  have h₀ : 0 ≤ y := by dsimp [y]; linarith
  have h₂ : y ≤ 2 := by dsimp [y]; linarith
  obtain ⟨b, α, β, band⟩ : ∃ b α β, Band y b α β := by
    by_cases h₁ : y ≤ 1/2
    · exact ⟨_, _, _, .first h₀ h₁⟩
    by_cases h₂' : y ≤ 55/100
    · exact ⟨_, _, _, .second (le_of_not_ge h₁) h₂'⟩
    by_cases h₃ : y ≤ 68/100
    · exact ⟨_, _, _, .third (le_of_not_ge h₂') h₃⟩
    by_cases h₄ : y ≤ 1
    · exact ⟨_, _, _, .fourth (le_of_not_ge h₃) h₄⟩
    exact ⟨_, _, _, .fifth (le_of_not_ge h₄) h₂⟩
  exact ⟨b, α, β, band, five_width_comparisons hp' hpt rfl band⟩

/-- Accounting for the loss from replacing the number of retained rows by its
initial value gives the high-weight endpoint rebate. Here x is n/K. -/
theorem reserved_endpoint {lam kept x rebate : ℝ}
    (hhalf : 1/2 ≤ kept) (hretained : lam - x ≤ kept) (hcost : 3/5*x ≤ rebate) :
    1/2 + 3/5*(lam-1/2) ≤ kept + rebate := by
  linarith


/-- Width remains positive after replacing the required order by 255 / 256 of
the power-of-two cutoff and taking the fourth root in the scale parameter. -/
theorem reduced_width_for_every_pruning_pair {p t : ℝ}
    (hp : 0 ≤ p) (hp' : p ≤ 125/61) (ht : 0 ≤ t) (hpt : p/4 + (199/400)*t ≤ 1) :
    let y := 2 - p/2 - (199/400)*t
    ∃ b α β, Band y b α β ∧
      1/10000 < Real.log ((2:ℝ)^((144-b)/4) / (1120 * ((256:ℝ)/255)^(1/4:ℝ)))
        - (y/α + (p+t)/β) + min ((391 + (1464/5)*p)/1120) ((4333+737*p)/10000) := by
  obtain ⟨b, α, β, band, _⟩ := width_for_every_pruning_pair hp hp' ht hpt
  refine ⟨b, α, β, band, ?_⟩
  have hlog := Real.log_two_gt_d9
  have hnorm := log_normalizer
  have hratio : Real.log ((256:ℝ)/255) ≤ 1/255 := by
    exact (Real.log_le_sub_one_of_pos (by norm_num : 0 < (256:ℝ)/255)).trans (by norm_num)
  rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity),
    Real.log_rpow (by norm_num : 0 < (256:ℝ)/255), Real.log_rpow (by norm_num), add_min]
  cases band <;> apply lt_min <;> linarith

/-- The fourth power of the reduced width scale gives exactly the stated
integer cutoff in each band. -/
theorem fourth_power_of_reduced_scale (b : ℝ) :
    (2:ℝ)^b * ((2:ℝ)^((144-b)/4) / ((256:ℝ)/255)^(1/4:ℝ))^4 = 255*(2:ℝ)^136 := by
  have hnum : ((2:ℝ)^((144-b)/4))^(4:ℕ) = (2:ℝ)^(144-b) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
    congr 1
    ring
  have hden : (((256:ℝ)/255)^(1/4:ℝ))^(4:ℕ) = (256:ℝ)/255 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : 0 ≤ (256:ℝ)/255)]
    norm_num
  rw [div_pow, hnum, hden, ← mul_div_assoc, ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
  rw [show b + (144-b) = 144 by ring]
  norm_num

end Erdos617.RetainedWidth
