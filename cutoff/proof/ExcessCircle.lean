import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-! Finite circular arcs for the positive excess over the baseline load.
With ρ=9/(40s), a circle of 30sr positions represents circumference 3r/4
exactly, with 40s lattice positions per vertex. -/

namespace Erdos617.ExcessCircle

open Finset
open scoped Classical
noncomputable section
variable {N : ℕ} [NeZero N]

def arc (start : ZMod N) (len : ℕ) : Finset (ZMod N) :=
  (range len).image fun k : ℕ ↦ start+(k:ZMod N)

omit [NeZero N] in
theorem arc_card (start : ZMod N) {len : ℕ} (fits : len ≤ N) :
    (arc start len).card = len := by
  unfold arc
  rw [card_image_of_injOn,card_range]
  intro i hi j hj eq
  have same : (i:ZMod N) = (j:ZMod N) := add_left_cancel eq
  have h := congrArg ZMod.val same
  simpa only [ZMod.val_natCast_of_lt ((mem_range.mp hi).trans_le fits),
    ZMod.val_natCast_of_lt ((mem_range.mp hj).trans_le fits)] using h

/-- Conditional on the first start, at most a+b other starts cause
intersection. The result includes zero-length arcs and circular wraparound. -/
theorem colliding_starts (x : ZMod N) (a b : ℕ) :
    (univ.filter fun y ↦ ¬Disjoint (arc x a) (arc y b)).card ≤ a+b := by
  let front := arc x a
  let back := (range b).image fun k : ℕ ↦ x-((k:ZMod N)+1)
  have sub : (univ.filter fun y ↦ ¬Disjoint (arc x a) (arc y b)) ⊆ front ∪ back := by
    intro y hy
    obtain ⟨v,hx,hy⟩ := not_disjoint_iff.mp (mem_filter.mp hy).2
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hx
    obtain ⟨j,hj,eq⟩ := mem_image.mp hy
    by_cases h : j ≤ i
    · apply mem_union_left
      apply mem_image.mpr
      refine ⟨i-j,mem_range.mpr ((Nat.sub_le i j).trans_lt (mem_range.mp hi)),?_⟩
      rw [Nat.cast_sub h]
      linear_combination -eq
    · apply mem_union_right
      apply mem_image.mpr
      have ij : i < j := by omega
      refine ⟨j-i-1,mem_range.mpr (by have := mem_range.mp hj; omega),?_⟩
      rw [Nat.cast_sub (show 1 ≤ j-i by omega),Nat.cast_sub (by omega : i ≤ j),Nat.cast_one]
      linear_combination -eq
  have sum := (card_le_card sub).trans (card_union_le front back)
  apply sum.trans
  apply Nat.add_le_add
  · exact card_image_le.trans_eq (card_range _)
  · exact card_image_le.trans_eq (card_range _)

/-- Independent exterior representatives have disjoint arcs in an
unrepresented row, hence their combined lengths fit on one circle. -/
theorem packing {I : Type*} (parts : Finset I) (start : I → ZMod N) (len : I → ℕ)
    (fits : ∀ i ∈ parts, len i ≤ N)
    (dis : (parts:Set I).PairwiseDisjoint fun i ↦ arc (start i) (len i)) :
    ∑ i ∈ parts, len i ≤ N := by
  have size := card_le_univ (parts.biUnion fun i ↦ arc (start i) (len i))
  rw [card_biUnion dis,ZMod.card] at size
  simpa only [← sum_congr rfl (fun i hi ↦ arc_card (start i) (fits i hi))] using size

/-- Integer excess length for the actual load t, measured in lattice positions. -/
def excess (s r t : ℕ) : ℕ := 40*s*t-9*r

theorem excess_fits {s r t : ℕ} (bound : 4*t ≤ 3*r) : excess s r t ≤ 30*s*r := by
  apply (Nat.sub_le ..).trans
  nlinarith only [Nat.mul_le_mul_left (10*s) bound]

theorem excess_units {s r t : ℕ} (hs : 0 < s) :
    (excess s r t:ℝ) = (40*(s:ℝ))*max ((t:ℝ)-(9/40:ℝ)/s*r) 0 := by
  have sp : (0:ℝ)<s := by exact_mod_cast hs
  have scale : 0 ≤ 40*(s:ℝ) := by positivity
  rw [mul_max_of_nonneg _ _ scale,mul_zero,mul_sub]
  have exactBase : 40*(s:ℝ)*((9/40:ℝ)/s*r) = 9*(r:ℝ) := by field_simp
  rw [exactBase]
  by_cases h : 9*r ≤ 40*s*t
  · have h' : (9:ℝ)*r ≤ 40*(s:ℝ)*t := by exact_mod_cast h
    simp only [excess,Nat.cast_sub h,Nat.cast_mul,Nat.cast_ofNat,max_eq_left (sub_nonneg.mpr h')]
  · have h' : 40*(s:ℝ)*t ≤ 9*r := by exact_mod_cast le_of_not_ge h
    rw [max_eq_right (sub_nonpos.mpr h')]
    simp [excess,Nat.sub_eq_zero_of_le (le_of_not_ge h)]

end
end Erdos617.ExcessCircle
