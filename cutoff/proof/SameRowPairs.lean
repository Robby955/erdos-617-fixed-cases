import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Sym.Card
import Mathlib.Tactic

/-! The unordered repair edges involving representatives of a single row. -/

namespace Erdos617.SameRowConflicts

open Finset
open scoped Classical
noncomputable section
variable {V : Type*}

/-- A mark can carry a representative or just the exterior point. -/
def marked (o : Option (Option V)) : ℝ := if o.isSome then 1 else 0

/-- A representative conflict with vertex y uses an actual edge into C. -/
def hit (G : SimpleGraph V) (C : Finset V) (y : V) (o : Option (Option V)) : ℝ :=
  if ∃ v ∈ C, o = some (some v) ∧ G.Adj y v then 1 else 0

def degree (G : SimpleGraph V) (C : Finset V) (y : V) : ℝ := (C.filter (G.Adj y)).card

theorem marked_nonneg (o : Option (Option V)) : 0 ≤ marked o := by
  unfold marked; split <;> norm_num

theorem marked_le_one (o : Option (Option V)) : marked o ≤ 1 := by
  unfold marked; split <;> norm_num

theorem hit_as_atoms (G : SimpleGraph V) (C : Finset V) (y : V) (o : Option (Option V)) :
    hit G C y o = ∑ v ∈ C.filter (G.Adj y), if o=some (some v) then (1:ℝ) else 0 := by
  cases o with
  | none => simp [hit]
  | some o =>
    cases o with
    | none => simp [hit]
    | some v => simp [hit]

/-- First charge one unordered pair per pair of marks in U. The remaining
charges count representative hits to fixed vertices L and marked vertices O. -/
def cost (G : SimpleGraph V) (C U O L : Finset V) (w : V → Option (Option V)) : ℝ :=
  (∑ p ∈ U.offDiag, marked (w p.1)*marked (w p.2))/2 +
    ∑ x ∈ U, ((∑ y ∈ L, hit G C y (w x)) +
      ∑ y ∈ O, hit G C y (w x)*marked (w y))

/-- Distinct unordered edges charged at this row. Pairs of marked unique
senders are included once, whatever their representatives. -/
def edges (G : SimpleGraph V) (C U O L : Finset V) (w : V → Option (Option V)) :
    Finset (Sym2 V) :=
  let chosen := U.filter fun x ↦ (w x).isSome
  let blocked (x y : V) := ∃ v ∈ C, w x = some (some v) ∧ G.Adj y v
  chosen.offDiag.image Sym2.mk.uncurry ∪ U.biUnion fun x ↦
    ((L.filter (blocked x)).image (Sym2.mk x) ∪
      (O.filter fun y ↦ blocked x y ∧ (w y).isSome).image (Sym2.mk x))

/-- The ordered sum charges each distinct same-row pair twice, once in each orientation. -/
theorem pair_count (U : Finset V) (w : V → Option (Option V)) :
    (((U.filter fun x ↦ (w x).isSome).offDiag.image Sym2.mk.uncurry).card:ℝ) =
      (∑ p ∈ U.offDiag, marked (w p.1)*marked (w p.2))/2 := by
  let S := U.filter fun x ↦ (w x).isSome
  have sub : S.offDiag = U.offDiag.filter fun p ↦ (w p.1).isSome ∧ (w p.2).isSome := by
    ext p
    simp only [S,mem_offDiag,mem_filter]; aesop
  have inds (p : V × V) : marked (w p.1)*marked (w p.2) =
      if (w p.1).isSome ∧ (w p.2).isSome then (1:ℝ) else 0 := by
    by_cases a : (w p.1).isSome <;> by_cases b : (w p.2).isSome <;> simp [marked,a,b]
  have d : 2*((S.offDiag.image Sym2.mk.uncurry).card:ℝ) = S.offDiag.card := by
    exact_mod_cast Sym2.two_mul_card_image_offDiag S
  have count : (S.offDiag.card:ℝ) = ∑ p ∈ U.offDiag, marked (w p.1)*marked (w p.2) := by
    rw [sub]; simp_rw [inds]; simp
  exact (eq_div_iff (by norm_num : (2:ℝ) ≠ 0)).mpr (by linarith only [d,count])

/-- Taking a union of repair edges can only lower their charge, even when
several representatives point to the same exterior vertex. -/
theorem edges_le_cost (G : SimpleGraph V) (C U O L : Finset V) (w : V → Option (Option V)) :
    ((edges G C U O L w).card:ℝ) ≤ cost G C U O L w := by
  let B := fun x y ↦ ∃ v ∈ C, w x=some (some v) ∧ G.Adj y v
  let A := fun x ↦ (L.filter (B x)).image (Sym2.mk x)
  let D := fun x ↦ (O.filter fun y ↦ B x y ∧ (w y).isSome).image (Sym2.mk x)
  let S := U.filter fun x ↦ (w x).isSome
  have each (x : V) (_hx : x ∈ U) :
      (((A x ∪ D x).card):ℝ) ≤ (∑ y ∈ L, hit G C y (w x))+
          ∑ y ∈ O, hit G C y (w x)*marked (w y) := by
    have first : ((A x).card:ℝ) ≤ ∑ y ∈ L, hit G C y (w x) := by
      have n : (A x).card ≤ (L.filter (B x)).card := card_image_le
      simpa [hit,B] using (Nat.cast_le (α := ℝ)).mpr n
    have term (y) : hit G C y (w x)*marked (w y) =
        if B x y ∧ (w y).isSome then (1:ℝ) else 0 := by
      by_cases b : B x y <;> by_cases a : (w y).isSome <;> simp [hit,marked,B] at b ⊢ <;> simp_all [B]
    have second : ((D x).card:ℝ) ≤ ∑ y ∈ O, hit G C y (w x)*marked (w y) := by
      have n : (D x).card ≤ (O.filter fun y ↦ B x y ∧ (w y).isSome).card := card_image_le
      simp_rw [term]
      have cast := (Nat.cast_le (α := ℝ)).mpr n
      rw [card_filter,Nat.cast_sum] at cast
      simpa only [Nat.cast_ite,Nat.cast_one,Nat.cast_zero] using cast
    exact (show (((A x ∪ D x).card):ℝ) ≤ (A x).card+((D x).card:ℝ) by exact_mod_cast card_union_le ..).trans
      (add_le_add first second)
  have outer : (edges G C U O L w).card ≤ (S.offDiag.image Sym2.mk.uncurry).card+
      ∑ x ∈ U, (A x ∪ D x).card :=
    (card_union_le ..).trans (Nat.add_le_add_left (card_biUnion_le ..) _)
  have out := (Nat.cast_le (α := ℝ)).mpr outer
  rw [Nat.cast_add,Nat.cast_sum] at out
  have pair : ((S.offDiag.image Sym2.mk.uncurry).card:ℝ) = _ := pair_count U w
  rw [pair] at out
  exact out.trans (add_le_add_right (sum_le_sum each) _)

end
end Erdos617.SameRowConflicts
