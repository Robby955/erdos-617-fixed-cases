import MarkedSenderLaw

/-! Mean and variance of the marked-sender population, including every chosen subfamily. -/

namespace Erdos617.MarkedSender

open Finset FiniteLaw
open scoped Classical
noncomputable section

variable {V I : Type*} [Fintype V] [Fintype I]

/-- Count actual marked coordinates of a sample on S. -/
def markCount (S : Finset I) (w : I → State V) : ℝ := ∑ i ∈ S, marked (w i)

/-- Make one independent, thinned trial per sender, reading its outcomes
from the original target graph and its assigned original row. -/
def sample (G : SimpleGraph V) (y : I → V) (kind : I → Kind V) (ρ p : ℝ)
    (hρ : 0 ≤ ρ) (rate : 100*ρ ≤ 1) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    Law (I → State V) := product fun i ↦ law G (y i) (kind i) ρ p hρ rate hp hp1

theorem mark_count_mean (G : SimpleGraph V) (y : I → V) (kind : I → Kind V)
    (ρ p : ℝ) (hρ : 0 ≤ ρ) (rate : 100*ρ ≤ 1) (hp : 0 ≤ p) (hp1 : p ≤ 1) (S : Finset I) :
    (sample G y kind ρ p hρ rate hp hp1).expect (markCount S) =
      ∑ i ∈ S, p*eligible G (y i) (kind i) ρ := by
  unfold sample markCount
  rw [Law.expect_sum]
  simp_rw [expect_coord,mark_mean]

omit [Fintype I] in
private theorem centered_moments (μ : Law (State V)) {m : ℝ} (mean : μ.expect marked = m) :
    μ.expect (fun v ↦ marked v-m) = 0 ∧
      μ.expect (fun v ↦ (marked v-m)*(marked v-m)) = m*(1-m) := by
  have zero : (fun v : State V ↦ marked v-m) = (fun v ↦ marked v+(-m)) := by
    funext v; ring
  have eq : (fun v : State V ↦ (marked v-m)*(marked v-m)) =
      (fun v ↦ marked v*(1-2*m)+m*m) := by
    funext v
    cases v <;> simp [marked]; ring
  constructor
  · rw [zero,μ.expect_add marked (fun _ ↦ -m),mean,μ.expect_const]; ring
  · rw [eq,μ.expect_add _ (fun _ ↦ m*m),μ.expect_const,μ.expect_mul_const,mean]; ring

/-- The variance is exactly the sum of the Bernoulli variances. The diagonal
uses the single mark indicator twice. Distinct senders factor under the
constructed finite product even when they are assigned the same row. -/
theorem mark_count_variance (G : SimpleGraph V) (y : I → V) (kind : I → Kind V)
    (ρ p : ℝ) (hρ : 0 ≤ ρ) (rate : 100*ρ ≤ 1) (hp : 0 ≤ p) (hp1 : p ≤ 1) (S : Finset I) :
    let t := fun i ↦ p*eligible G (y i) (kind i) ρ
    (sample G y kind ρ p hρ rate hp hp1).expect (fun w ↦ (markCount S w-∑ i ∈ S, t i)^2) =
      ∑ i ∈ S, t i*(1-t i) := by
  let μ := fun i ↦ law G (y i) (kind i) ρ p hρ rate hp hp1
  let t := fun i ↦ p*eligible G (y i) (kind i) ρ
  let z := fun i (a : State V) ↦ marked a-t i
  have mean (i) : (μ i).expect marked = t i := mark_mean ..
  have cov (i j : I) : (product μ).expect (fun w ↦ z i (w i)*z j (w j)) =
      if i=j then t i*(1-t i) else 0 := by
    by_cases h : i=j
    · subst j
      rw [ite_eq_left rfl,expect_coord μ i (fun a ↦ z i a*z i a)]
      exact (centered_moments _ (mean i)).2
    · rw [ite_eq_right h,expect_pair μ h (z i) (z j)]
      rw [show (μ i).expect (z i) = 0 from (centered_moments _ (mean i)).1,zero_mul]
  have square (w : I → State V) : (markCount S w-∑ i ∈ S, t i)^2 =
      ∑ i ∈ S, ∑ j ∈ S, z i (w i)*z j (w j) := by
    change ((∑ i ∈ S, marked (w i))-∑ i ∈ S, t i)^2 = _
    rw [← sum_sub_distrib,pow_two]
    simp only [z,sum_mul,mul_sum]
    rw [sum_comm]
  change (product μ).expect (fun w ↦ (markCount S w-∑ i ∈ S, t i)^2) = _
  simp_rw [square,Law.expect_sum,cov]
  simp [t]

theorem mark_count_variance_le_mean (G : SimpleGraph V) (y : I → V) (kind : I → Kind V)
    (ρ p : ℝ) (hρ : 0 ≤ ρ) (rate : 100*ρ ≤ 1) (hp : 0 ≤ p) (hp1 : p ≤ 1) (S : Finset I) :
    let μ := sample G y kind ρ p hρ rate hp hp1
    μ.expect (fun w ↦ (markCount S w-μ.expect (markCount S))^2) ≤ μ.expect (markCount S) := by
  dsimp only
  rw [mark_count_mean,mark_count_variance]
  exact sum_le_sum fun i _ ↦ by nlinarith only [sq_nonneg (p*eligible G (y i) (kind i) ρ)]

end
end Erdos617.MarkedSender
