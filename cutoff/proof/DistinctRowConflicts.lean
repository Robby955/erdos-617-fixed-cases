import JointSenderLaw
import Mathlib.Combinatorics.SimpleGraph.Finite

/-! An edge between two representatives from different rows, with the row cut
read directly from the target graph. -/

namespace Erdos617.RepresentativeCut

open Finset FiniteLaw
open scoped Classical
noncomputable section

variable {V : Type*} [Fintype V]

def cut (G : SimpleGraph V) (C D : Finset V) :=
  (C ×ˢ D).filter fun e ↦ G.Adj e.1 e.2

/-- A single sender can select at most one endpoint of the cut. -/
def atom (v : V) (state : Option (Option V)) : ℝ := if state=some (some v) then 1 else 0

def collision (G : SimpleGraph V) (C D : Finset V) (a b : Option (Option V)) : ℝ :=
  ∑ e ∈ cut G C D, atom e.1 a * atom e.2 b

omit [Fintype V] in
/-- On a sample with outputs x and y the cost is exactly the indicator of
the original target edge between them, counted in the given orientation. -/
theorem collision_selected (G : SimpleGraph V) (C D : Finset V) (x y : V) :
    collision G C D (some (some x)) (some (some y)) =
      if (x,y) ∈ cut G C D then 1 else 0 := by
  unfold collision
  have each (e : V × V) : atom e.1 (some (some x))*atom e.2 (some (some y)) =
      if e=(x,y) then 1 else 0 := by
    obtain ⟨u,v⟩ := e
    by_cases a : x=u <;> by_cases b : y=v <;> simp_all [atom,eq_comm]
  simp_rw [each]
  simp

/-- The probability per distinct pair is at most c² times the actual cut size. -/
theorem collision_mean (G : SimpleGraph V) (C D : Finset V)
    (μ : V → Law (Option (Option V))) {x y : V} (ne : x ≠ y) {c : ℝ}
    (left : ∀ u ∈ C, (μ x).expect (atom u) ≤ c)
    (right : ∀ v ∈ D, (μ y).expect (atom v) ≤ c) :
    (product μ).expect (fun w ↦ collision G C D (w x) (w y)) ≤
      ((cut G C D).card:ℝ)*c^2 := by
  unfold collision
  rw [Law.expect_sum]
  have each (e : V × V) (he : e ∈ cut G C D) :
      (product μ).expect (fun w ↦ atom e.1 (w x)*atom e.2 (w y)) ≤ c^2 := by
    obtain ⟨hu,hv⟩ := mem_product.mp (mem_filter.mp he).1
    have pos (i v : V) : 0 ≤ (μ i).expect (atom v) := by
      apply sum_nonneg
      intro a _
      exact mul_nonneg ((μ i).nonneg a) (by unfold atom; split <;> norm_num)
    rw [expect_pair μ ne,sq]
    exact mul_le_mul (left _ hu) (right _ hv) (pos y e.2) ((pos x e.1).trans (left _ hu))
  simpa only [sum_const,nsmul_eq_mul] using sum_le_sum each

/-- Group by distinct destination rows. Disjoint sender sets guarantee that
only two different coordinates of the finite product law are factored. -/
theorem between_row_groups (G : SimpleGraph V) (C D U W : Finset V)
    (μ : V → Law (Option (Option V))) (dis : Disjoint U W) {c : ℝ}
    (left : ∀ x ∈ U, ∀ u ∈ C, (μ x).expect (atom u) ≤ c)
    (right : ∀ y ∈ W, ∀ v ∈ D, (μ y).expect (atom v) ≤ c) :
    (product μ).expect (fun w ↦ ∑ x ∈ U, ∑ y ∈ W, collision G C D (w x) (w y)) ≤
      (U.card:ℝ)*W.card*((cut G C D).card:ℝ)*c^2 := by
  simp_rw [Law.expect_sum]
  have e (x) (hx : x ∈ U) (y) (hy : y ∈ W) := collision_mean G C D μ
    (show x ≠ y from fun eq ↦ disjoint_left.mp dis hx (eq ▸ hy)) (left x hx) (right y hy)
  have bound := sum_le_sum (s := U) fun x hx ↦ sum_le_sum (s := W) (e x hx)
  simpa only [sum_const,nsmul_eq_mul,← mul_assoc] using bound

end
end Erdos617.RepresentativeCut
