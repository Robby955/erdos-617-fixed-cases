import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-! Finite product sampling for the marked-sender construction in Appendix A, §5. -/

namespace Erdos617.FiniteLaw

open Finset
open scoped Classical
noncomputable section

structure Law (Ω : Type*) [Fintype Ω] where
  weight : Ω → ℝ
  nonneg : ∀ a, 0 ≤ weight a
  total : ∑ a, weight a = 1

variable {Ω I κ : Type*} [Fintype Ω]

def Law.expect (μ : Law Ω) (f : Ω → ℝ) : ℝ := ∑ a, μ.weight a * f a

theorem Law.expect_const (μ : Law Ω) (c : ℝ) : μ.expect (fun _ ↦ c) = c := by
  simp [Law.expect,← sum_mul,μ.total]

theorem Law.expect_sum (μ : Law Ω) (S : Finset κ) (f : κ → Ω → ℝ) :
    μ.expect (fun w ↦ ∑ i ∈ S, f i w) = ∑ i ∈ S, μ.expect (f i) := by
  unfold Law.expect
  simp_rw [mul_sum]
  rw [sum_comm]

theorem Law.expect_mono (μ : Law Ω) {f g : Ω → ℝ} (h : ∀ a, f a ≤ g a) :
    μ.expect f ≤ μ.expect g := sum_le_sum fun a _ ↦ mul_le_mul_of_nonneg_left (h a) (μ.nonneg a)

theorem Law.expect_add (μ : Law Ω) (f g : Ω → ℝ) :
    μ.expect (fun a ↦ f a+g a) = μ.expect f+μ.expect g := by simp [Law.expect,mul_add,sum_add_distrib]

theorem Law.expect_mul_const (μ : Law Ω) (f : Ω → ℝ) (c : ℝ) :
    μ.expect (fun a ↦ f a*c) = μ.expect f*c := by simp [Law.expect,← mul_assoc,sum_mul]

theorem Law.expect_const_mul (μ : Law Ω) (c : ℝ) (f : Ω → ℝ) :
    μ.expect (fun a ↦ c*f a) = c*μ.expect f := by
  simpa only [mul_comm c] using μ.expect_mul_const f c

theorem Law.expect_atom (μ : Law Ω) (a : Ω) :
    μ.expect (fun v ↦ if v=a then (1:ℝ) else 0) = μ.weight a := by
  simp [Law.expect,mul_ite]

variable [Fintype I]

/-- Choose each coordinate independently according to its own finite law. -/
def product (μ : I → Law Ω) : Law (I → Ω) where
  weight w := ∏ i, (μ i).weight (w i)
  nonneg w := prod_nonneg fun i _ ↦ (μ i).nonneg (w i)
  total := by rw [← Fintype.prod_sum]; simp [Law.total]

/-- Factor the actual mass sum, including when the index type is empty. -/
theorem expect_prod (μ : I → Law Ω) (f : I → Ω → ℝ) :
    (product μ).expect (fun w ↦ ∏ i, f i (w i)) = ∏ i, (μ i).expect (f i) := by
  simp only [Law.expect,product,← prod_mul_distrib]
  exact (Fintype.prod_sum (fun i a ↦ (μ i).weight a*f i a)).symm

private def atCoord (i k : I) (f : Ω → ℝ) (v : Ω) : ℝ := if k=i then f v else 1

omit [Fintype Ω] in
private theorem coord_apply (w : I → Ω) (i : I) (f : Ω → ℝ) :
    (∏ k, atCoord i k f (w k)) = f (w i) := by simp [atCoord]

omit [Fintype I] in
private theorem coord_mean (μ : I → Law Ω) (i k : I) (f : Ω → ℝ) :
    (μ k).expect (atCoord i k f) = if k=i then (μ i).expect f else 1 := by
  by_cases h : k=i
  · subst k; simp [Law.expect,atCoord]
  · simp [Law.expect,atCoord,h,Law.total]

theorem expect_coord (μ : I → Law Ω) (i : I) (f : Ω → ℝ) :
    (product μ).expect (fun w ↦ f (w i)) = (μ i).expect f := by
  simp_rw [← coord_apply _ i f,expect_prod,coord_mean]
  simp

theorem expect_pair (μ : I → Law Ω) {i j : I} (ne : i ≠ j) (f g : Ω → ℝ) :
    (product μ).expect (fun w ↦ f (w i)*g (w j)) = (μ i).expect f*(μ j).expect g := by
  have point (w : I → Ω) : f (w i)*g (w j) =
      ∏ k, atCoord i k f (w k)*atCoord j k g (w k) := by
    rw [prod_mul_distrib,coord_apply,coord_apply]
  have each (k : I) : (μ k).expect (fun v ↦ atCoord i k f v*atCoord j k g v) =
      (if k=i then (μ i).expect f else 1)*(if k=j then (μ j).expect g else 1) := by
    by_cases hi : k=i
    · subst k; simp [atCoord,ne]
    · by_cases hj : k=j
      · subst k; simp [atCoord,hi]
      · simp [atCoord,hi,hj,Law.expect_const]
  rw [show (fun w : I → Ω ↦ f (w i)*g (w j)) = _ from funext point]
  rw [expect_prod μ (fun k a ↦ atCoord i k f a * atCoord j k g a)]
  simp_rw [each,prod_mul_distrib]
  simp

theorem expect_pair_function (μ : I → Law Ω) {i j : I} (ne : i ≠ j) (f : Ω → Ω → ℝ) :
    (product μ).expect (fun w ↦ f (w i) (w j)) =
      ∑ a, ∑ b, (μ i).weight a*(μ j).weight b*f a b := by
  let hit (a v : Ω) : ℝ := if v=a then 1 else 0
  have atom (k) (a : Ω) : (μ k).expect (hit a) = (μ k).weight a := by
    simp [Law.expect,hit,mul_ite]
  have decomp (w : I → Ω) : f (w i) (w j) =
      ∑ a, ∑ b, (hit a (w i)*hit b (w j))*f a b := by
    simp [hit,ite_mul,mul_ite]
  have entry (a b : Ω) : (product μ).expect (fun w ↦ (hit a (w i)*hit b (w j))*f a b) =
      (μ i).weight a*(μ j).weight b*f a b := by
    rw [(product μ).expect_mul_const _ _,expect_pair μ ne,atom,atom]
  simp_rw [decomp,Law.expect_sum,entry]

end
end Erdos617.FiniteLaw
