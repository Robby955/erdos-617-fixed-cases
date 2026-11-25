import ExcessCircle
import JointSenderLaw
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-! Count genuine unordered arc collisions on independently uniform circle starts. -/

namespace Erdos617.ArcRepair

open Finset FiniteLaw ExcessCircle
open scoped Classical
noncomputable section

variable {I : Type*} {N : ℕ} [NeZero N]

def graph (start : I → ZMod N) (len : I → ℕ) : SimpleGraph I where
  Adj x y := x ≠ y ∧ ¬Disjoint (arc (start x) (len x)) (arc (start y) (len y))
  symm := ⟨fun _ _ ⟨ne,notDis⟩ ↦ ⟨ne.symm,fun h ↦ notDis h.symm⟩⟩
  loopless := ⟨fun _ h ↦ h.1 rfl⟩

/-- Uniform random start at one of the N lattice sites. -/
def uniform (N : ℕ) [NeZero N] : Law (ZMod N) where
  weight _ := 1/(N:ℝ)
  nonneg _ := by positivity
  total := by have pos : (0:ℝ)<N := by exact_mod_cast NeZero.pos N
              simp [ZMod.card,pos.ne']

variable [Fintype I]

def starts (I : Type*) [Fintype I] (N : ℕ) [NeZero N] : Law (I → ZMod N) :=
  product fun _ ↦ uniform N

/-- One independent start in each coordinate. A zero-length arc never
meets another arc, including at an identical start. -/
theorem starts_pair_bound (x y : I) (ne : x ≠ y) (a b : ℕ) :
    (starts I N).expect (fun z ↦ if ¬Disjoint (arc (z x) a) (arc (z y) b) then (1:ℝ) else 0) ≤
      ((if 0<a then (b:ℝ) else 0)+(if 0<b then (a:ℝ) else 0))/N := by
  have pos : (0:ℝ)<N := by exact_mod_cast NeZero.pos N
  by_cases ha : a=0
  · subst a; simp [arc,Law.expect]
  by_cases hb : b=0
  · subst b; simp [arc,Law.expect]
  rw [ite_eq_left (Nat.pos_of_ne_zero ha),ite_eq_left (Nat.pos_of_ne_zero hb)]
  unfold starts
  rw [expect_pair_function (fun _ : I ↦ uniform N) ne
    (fun u v ↦ if ¬Disjoint (arc u a) (arc v b) then (1:ℝ) else 0)]
  let f := fun u v : ZMod N ↦ ¬Disjoint (arc u a) (arc v b)
  have per (u : ZMod N) : (∑ v, (uniform N).weight u*(uniform N).weight v*
      (if f u v then (1:ℝ) else 0)) ≤ (1/(N:ℝ))^2*((a:ℝ)+b) := by
    change (∑ v, (1/(N:ℝ))*(1/(N:ℝ))*(if f u v then 1 else 0)) ≤ _
    rw [← mul_sum,← sq]
    have count : (∑ v, if f u v then (1:ℝ) else 0) =
        ((univ.filter (f u)).card:ℝ) := by rw [← sum_filter]; simp
    rw [count]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast colliding_starts u a b) (sq_nonneg _)
  have all := sum_le_sum (s := univ) fun u _ ↦ per u
  simp only [sum_const,card_univ,ZMod.card,nsmul_eq_mul] at all
  apply all.trans_eq
  field_simp
  ring

theorem edge_mass (G : SimpleGraph I) :
    (G.edgeFinset.card:ℝ) = (∑ x, ∑ y, if G.Adj x y then (1:ℝ) else 0)/2 := by
  have count := G.sum_degrees_eq_twice_card_edges
  have per (x : I) : (∑ y, if G.Adj x y then (1:ℝ) else 0) = (G.degree x:ℝ) := by
    simp [← SimpleGraph.card_neighborFinset_eq_degree,SimpleGraph.neighborFinset_eq_filter]
  simp_rw [per]
  have realCount : (∑ x, (G.degree x:ℝ)) = 2*(G.edgeFinset.card:ℝ) := by exact_mod_cast count
  linarith

end
end Erdos617.ArcRepair
