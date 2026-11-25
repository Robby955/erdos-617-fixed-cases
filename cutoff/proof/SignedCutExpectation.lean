import JointSenderLaw

/-! Averaging the signed cut. The original sender law and the circle starts
are separate finite sums. Both signs of the shortage remain in the estimate. -/

namespace Erdos617.FiniteLaw

open Finset
open scoped Classical
noncomputable section
variable {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]

theorem Law.expect_mono_on_support (μ : Law Ω) {f g : Ω → ℝ}
    (h : ∀ w, 0 < μ.weight w → f w ≤ g w) : μ.expect f ≤ μ.expect g := by
  apply sum_le_sum
  intro w _
  rcases (μ.nonneg w).eq_or_lt with zero|pos
  · simp [← zero]
  · exact mul_le_mul_of_nonneg_left (h w pos) pos.le

/-- For a fixed family of tested rows, average over the genuine mark and
start laws. The term -u is valid even when the mean shortage is negative. -/
theorem expected_signed_cut (μ : Law Ω) (ν : Law Ξ) (cut v : Ω → ℝ)
    (repair : Ω → Ξ → ℝ) (B D u m : ℝ)
    (point : ∀ w, 0 < μ.weight w → ∀ z,
      2*cut w ≤ 2*repair w z+B+2*v w*D+v w*(v w-1))
    (mean : μ.expect v = u) (second : μ.expect (fun w ↦ (v w)^2) ≤ u^2+m) :
    2*μ.expect cut ≤ 2*μ.expect (fun w ↦ ν.expect (repair w))+B+2*u*D+u^2+m-u := by
  have conditional (w : Ω) (pos : 0 < μ.weight w) :
      2*cut w ≤ 2*ν.expect (repair w)+(B+v w*(2*D))+((v w)^2+v w*(-1)) := by
    let a := B+v w*(2*D)+((v w)^2+v w*(-1))
    have h (z : Ξ) : 2*cut w ≤ 2*repair w z+a := by
      dsimp only [a]
      linarith only [point w pos z]
    have integrated := ν.expect_mono h
    rw [Law.expect_const,Law.expect_add,Law.expect_const_mul,Law.expect_const] at integrated
    dsimp only [a] at integrated
    linarith only [integrated]
  have result := μ.expect_mono_on_support conditional
  rw [Law.expect_const_mul,Law.expect_add,Law.expect_add,Law.expect_const_mul,
      Law.expect_add,Law.expect_add,Law.expect_const,Law.expect_mul_const,Law.expect_mul_const,mean] at result
  linarith only [result,second]

end
end Erdos617.FiniteLaw
