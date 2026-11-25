import MarkedSenderLaw

/-! Domination of statistics determined by the two endpoints of an unordered
pair under two product laws on the same vertices. -/

namespace Erdos617.FiniteLaw

open Finset
open scoped Classical
noncomputable section
variable {V Ω : Type*} [Fintype V] [Fintype Ω]

/-- The other coordinates can be integrated out. The equal-endpoint case
only needs one marginal bound, and is included for arbitrary pair sets. -/
theorem expect_two_coordinates_le (μ ν : V → Law Ω) {k : ℝ} (hk : 1 ≤ k)
    (dom : ∀ v o, (ν v).weight o ≤ k*(μ v).weight o) (x y : V)
    (f : (V → Ω) → ℝ) (nonneg : ∀ w, 0 ≤ f w)
    (locality : ∀ w v, w x = v x → w y = v y → f w = f v) :
    (product ν).expect f ≤ k^2*(product μ).expect f := by
  have k0 : 0 ≤ k := zero_le_one.trans hk
  by_cases eq : x=y
  · subst y
    let g (a : Ω) := f (fun _ ↦ a)
    have actual : f = fun w ↦ g (w x) := funext fun w ↦ locality w _ rfl rfl
    rw [actual,expect_coord,expect_coord]
    have one : (ν x).expect g ≤ k*(μ x).expect g := by
      unfold Law.expect
      rw [mul_sum]
      exact sum_le_sum fun a _ ↦ (mul_le_mul_of_nonneg_right (dom x a) (nonneg _)).trans_eq (mul_assoc ..)
    have base : 0 ≤ (μ x).expect g := sum_nonneg fun a _ ↦ mul_nonneg ((μ x).nonneg a) (nonneg _)
    exact one.trans (mul_le_mul_of_nonneg_right (by nlinarith only [mul_nonneg k0 (sub_nonneg.mpr hk)] : k ≤ k^2) base)
  · let g (a b : Ω) := f (fun i ↦ if i=x then a else b)
    have actual : f = fun w ↦ g (w x) (w y) := by
      funext w
      exact locality w _ (by simp) (by simp [Ne.symm eq])
    rw [actual,expect_pair_function ν eq,expect_pair_function μ eq,mul_sum]
    apply sum_le_sum
    intro a _
    rw [mul_sum]
    apply sum_le_sum
    intro b _
    have joint := mul_le_mul (dom x a) (dom y b) ((ν y).nonneg b) (mul_nonneg k0 ((μ x).nonneg a))
    calc
      _ ≤ (k*(μ x).weight a*(k*(μ y).weight b))*g a b :=
        mul_le_mul_of_nonneg_right joint (nonneg _)
      _ = _ := by ring

/-- Count each unordered pair once, even if several rows or repair mechanisms
give reasons to add it. Only membership of that pair must be local. -/
theorem expect_pair_set_card_le (μ ν : V → Law Ω) {k : ℝ} (hk : 1 ≤ k)
    (dom : ∀ v o, (ν v).weight o ≤ k*(μ v).weight o)
    (P : (V → Ω) → Finset (Sym2 V))
    (locality : ∀ x y w v, w x = v x → w y = v y → (s(x,y) ∈ P w ↔ s(x,y) ∈ P v)) :
    (product ν).expect (fun w ↦ ((P w).card:ℝ)) ≤
      k^2*(product μ).expect (fun w ↦ ((P w).card:ℝ)) := by
  let hit (e : Sym2 V) (w : V → Ω) : ℝ := if e ∈ P w then 1 else 0
  have expand (w) : ((P w).card:ℝ) = ∑ e, hit e w := by simp [hit]
  simp_rw [expand,Law.expect_sum]
  rw [mul_sum]
  apply sum_le_sum
  intro e _
  induction e using Sym2.inductionOn with
  | _ x y =>
    apply expect_two_coordinates_le μ ν hk dom x y
    · intro w
      dsimp [hit]
      split <;> norm_num
    · intro w v hx hy
      simp only [hit,locality x y w v hx hy]

end
end Erdos617.FiniteLaw
