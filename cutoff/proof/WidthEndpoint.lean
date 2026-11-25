import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-! The upper endpoint of the width integral for the five bands at 2^144. -/

open Set
namespace Erdos617.WidthEndpoint

noncomputable def fraction (p : ℝ) : ℝ := (391+(1464/5)*p)/1120
noncomputable def affine (p : ℝ) : ℝ := (4333+737*p)/10000
noncomputable def saving (p : ℝ) := min (fraction p) (affine p)

/-- A rational lower bound c for the square root of the reserved fraction
suffices. The derivative changes sign at z = 1/(2(1+c)). -/
private theorem minimum {c u : ℝ} (hc : 0 ≤ c) (hu : 0 < u) (hu' : u ≤ 1/2) :
    1+c - Real.log (2*(1+c)) ≤ 1-u + 1/(4*u) + Real.log u + c^2*u := by
  let z : ℝ := 1 / (2*(1+c))
  let g := fun x : ℝ ↦ 1-x + (1/4)/x + Real.log x + c^2*x
  let d := fun x : ℝ ↦ ((2*(1+c)*x-1)*(1-2*(1-c)*x))/(4*x^2)
  have hz : 0 < z := by dsimp [z]; positivity
  have hz' : z ≤ 1/2 := by dsimp [z]; apply (div_le_iff₀ (by positivity)).2; linarith
  have hdz : 2*(1+c)*z = 1 := by dsimp [z]; field_simp
  have hd (x : ℝ) (hx : 0 < x) : HasDerivAt g (d x) x := by
    have H := ((((hasDerivAt_const x (1:ℝ)).sub (hasDerivAt_id x)).add
      ((hasDerivAt_const x (1/4:ℝ)).div (hasDerivAt_id x) hx.ne')).add
      (Real.hasDerivAt_log hx.ne')).add ((hasDerivAt_id x).const_mul (c^2))
    convert! H using 1; dsimp [g,d]; field_simp; ring
  have comp {v w : ℝ} (hv : 0 < v) (hvw : v < w) :
      ∃ x ∈ Ioo v w, d x * (w-v) = g w - g v := by
    obtain ⟨x, hx, he⟩ := exists_deriv_eq_slope g hvw
      (fun y hy ↦ (hd y (hv.trans_le hy.1)).continuousAt.continuousWithinAt)
      (fun y hy ↦ (hd y (hv.trans hy.1)).differentiableAt.differentiableWithinAt)
    rw [(hd x (hv.trans hx.1)).deriv] at he
    exact ⟨x, hx, (eq_div_iff (sub_ne_zero.mpr hvw.ne')).1 he⟩
  have posfactor {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1/2) : 0 ≤ 1-2*(1-c)*x := by
    nlinarith [mul_nonneg hc hx]
  have hmin : g z ≤ g u := by
    rcases lt_trichotomy u z with h | rfl | h
    · obtain ⟨x, hx, he⟩ := comp hu h
      have h₁ : 2*(1+c)*x-1 ≤ 0 := by linarith only [hdz, mul_le_mul_of_nonneg_left hx.2.le (show 0 ≤ 2*(1+c) by positivity)]
      have h₂ := posfactor (hu.trans hx.1).le (hx.2.le.trans hz')
      have h₃ : d x ≤ 0 := div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg h₁ h₂) (by positivity)
      linarith [mul_nonpos_of_nonpos_of_nonneg h₃ (sub_nonneg.mpr h.le)]
    · rfl
    · obtain ⟨x, hx, he⟩ := comp hz h
      have h₁ : 0 ≤ 2*(1+c)*x-1 := by linarith only [hdz, mul_le_mul_of_nonneg_left hx.1.le (show 0 ≤ 2*(1+c) by positivity)]
      have h₂ := posfactor (hz.trans hx.1).le (hx.2.le.trans hu')
      have h₃ : 0 ≤ d x := div_nonneg (mul_nonneg h₁ h₂) (by positivity)
      linarith [mul_nonneg h₃ (sub_nonneg.mpr h.le)]
  have gz : g z = 1+c - Real.log (2*(1+c)) := by
    dsimp [g,z]
    rw [one_div, Real.log_inv]
    field_simp; ring
  rw [← gz]
  convert! hmin using 1; ring

private theorem small_at_zero {u : ℝ} (hu : 0 < u) (hu' : u ≤ 1/2) :
    affine 0 ≤ 1-u+1/(4*u)+Real.log u+fraction 0*u := by
  let c : ℝ := 147713/250000
  have hl : Real.log (2*(1+c)) ≤ 1+c-affine 0 := by
    apply (Real.log_le_iff_le_exp (by dsimp [c]; norm_num)).2
    refine le_trans ?_ (Real.sum_le_exp_of_nonneg (by norm_num [c, affine]) 8)
    norm_num [c, affine, Finset.sum_range_succ, Nat.factorial]
  have h := minimum (c := c) (by norm_num [c]) hu hu'
  have hc : c^2 ≤ fraction 0 := by norm_num [c,fraction]
  exact (show _ ≤ 1+c-Real.log (2*(1+c)) by linarith only [hl]).trans
    (h.trans (add_le_add_right (mul_le_mul_of_nonneg_right hc hu.le) _))

private theorem small_at_max {u : ℝ} (hu : 0 < u) (hu' : u ≤ 1/2) :
    affine (125/61) ≤ 1-u+1/(4*u)+Real.log u+fraction (125/61)*u := by
  let c : ℝ := 940649/1000000
  have hl : Real.log (2*(1+c)) ≤ 1+c-affine (125/61) := by
    apply (Real.log_le_iff_le_exp (by dsimp [c]; norm_num)).2
    refine le_trans ?_ (Real.sum_le_exp_of_nonneg (by norm_num [c, affine]) 8)
    norm_num [c, affine, Finset.sum_range_succ, Nat.factorial]
  have h := minimum (c := c) (by norm_num [c]) hu hu'
  have hc : c^2 ≤ fraction (125/61) := by norm_num [c,fraction]
  exact (show _ ≤ 1+c-Real.log (2*(1+c)) by linarith only [hl]).trans
    (h.trans (add_le_add_right (mul_le_mul_of_nonneg_right hc hu.le) _))

/-- Interpolate in the pruning parameter at each fixed threshold. -/
theorem small {u p : ℝ} (hu : 0 < u) (hu' : u ≤ 1/2) (hp : 0 ≤ p) (hp' : p ≤ 125/61) :
    affine p ≤ 1-u+1/(4*u)+Real.log u+fraction p*u := by
  have h₀ := small_at_zero hu hu'
  have h₁ := small_at_max hu hu'
  let v := 1-u+1/(4*u)+Real.log u
  change affine 0 ≤ v + fraction 0*u at h₀
  change affine (125/61) ≤ v + fraction (125/61)*u at h₁
  change affine p ≤ v+fraction p*u
  have h := add_nonneg (mul_nonneg hp (sub_nonneg.mpr h₁))
    (mul_nonneg (sub_nonneg.mpr hp') (sub_nonneg.mpr h₀))
  dsimp [affine,fraction] at h ⊢
  linarith only [h]

/-- Secant of the logarithm between one half and one. -/
theorem log_secant {u : ℝ} (hu : 1/2 ≤ u) (hu' : u ≤ 1) :
    (2*(1-u))*Real.log (1/2) ≤ Real.log u := by
  have h := strictConcaveOn_log_Ioi.concaveOn.2
    (show (1/2:ℝ) ∈ Ioi 0 by norm_num) (show (1:ℝ) ∈ Ioi 0 by norm_num)
    (show 0 ≤ 2*(1-u) by linarith) (show 0 ≤ 2*u-1 by linarith)
    (show 2*(1-u)+(2*u-1)=1 by ring)
  simp only [smul_eq_mul, Real.log_one, mul_zero, add_zero] at h
  convert! h using 2; ring

end Erdos617.WidthEndpoint
