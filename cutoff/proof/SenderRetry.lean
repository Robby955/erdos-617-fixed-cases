import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic

/-! The single-sender trial of Appendix A, §5. Both draws are made uniformly
from the actual row. A successful output is a target nonneighbor of the sender. -/

namespace Erdos617.SenderRetry

open Finset
open scoped Classical
noncomputable section

variable {V : Type*}

/-- Keep the first nonneighbor. Upon a first hit, the retry coin decides
whether to use the second draw. -/
def output (G : SimpleGraph V) (y first second : V) (retry : Bool) : Option V :=
  if G.Adj y first then
    if retry = true ∧ ¬G.Adj y second then some second else none
  else some first

/-- A uniform pair of independent draws, averaged over both retry coin
outcomes. The coin has weight λ on true and 1−λ on false. -/
def mass (G : SimpleGraph V) (C : Finset V) (y : V) (rate : ℝ) (test : Option V → ℝ) : ℝ :=
  (∑ a ∈ C, ∑ b ∈ C, ((1-rate)*test (output G y a b false) +
    rate*test (output G y a b true)))/(C.card:ℝ)^2

theorem mass_one (G : SimpleGraph V) (C : Finset V) (y : V) (rate : ℝ)
    (nonempty : C.Nonempty) : mass G C y rate (fun _ ↦ 1) = 1 := by
  have pos : (0:ℝ)<C.card := by exact_mod_cast card_pos.mpr nonempty
  simp [mass,sub_add_cancel,pow_two, pos.ne']

theorem mass_nonnegative (G : SimpleGraph V) (C : Finset V) (y : V) (rate : ℝ)
    (lower : 0 ≤ rate) (upper : rate ≤ 1) (test : Option V → ℝ) (h : ∀ a, 0 ≤ test a) :
    0 ≤ mass G C y rate test :=
  div_nonneg (sum_nonneg fun _ _ ↦ sum_nonneg fun _ _ ↦
    add_nonneg (mul_nonneg (sub_nonneg.mpr upper) (h _)) (mul_nonneg lower (h _))) (sq_nonneg _)

/-- Probability of a successful draw satisfying hit. A failure contributes zero. -/
def successIn (G : SimpleGraph V) (C : Finset V) (y : V) (rate : ℝ) (hit : V → Prop) : ℝ :=
  mass G C y rate (fun v ↦ v.elim 0 (fun x ↦ if hit x then 1 else 0))

def neighborFraction (G : SimpleGraph V) (C : Finset V) (y : V) : ℝ :=
  ((C.filter (G.Adj y)).card:ℝ)/C.card

/-- Every eligible output contributes one branch for the first draw and
one branch for each neighbor that can trigger a retry on the second draw. -/
theorem successIn_eq (G : SimpleGraph V) (C : Finset V) (y : V) (rate : ℝ)
    (hit : V → Prop) (nonempty : C.Nonempty) :
    successIn G C y rate hit = (((C.filter (fun x ↦ ¬G.Adj y x ∧ hit x)).card:ℝ)/C.card)*
      (1+rate*neighborFraction G C y) := by
  let eligible (v : V) : ℝ := if ¬G.Adj y v ∧ hit v then 1 else 0
  let near (v : V) : ℝ := if G.Adj y v then 1 else 0
  let test (v : Option V) : ℝ := v.elim 0 (fun x ↦ if hit x then 1 else 0)
  have trial (a b : V) :
      (1-rate)*test (output G y a b false) + rate*test (output G y a b true) =
        eligible a + near a*rate*eligible b := by
    by_cases ha : G.Adj y a <;> by_cases hb : G.Adj y b <;> by_cases h : hit a <;>
      simp [output,ha,hb,h,test,eligible,near]
  have hitCount : ∑ b ∈ C, eligible b = ((C.filter (fun x ↦ ¬G.Adj y x ∧ hit x)).card:ℝ) := by
    simp [eligible]
  have nearCount : ∑ a ∈ C, near a = ((C.filter (G.Adj y)).card:ℝ) := by simp [near]
  change ((∑ a ∈ C, ∑ b ∈ C, ((1-rate)*test (output G y a b false) +
    rate*test (output G y a b true)))/_) = _
  simp_rw [trial,sum_add_distrib,← mul_sum]
  simp only [sum_const,nsmul_eq_mul]
  rw [← mul_sum,← sum_mul,← sum_mul,hitCount,nearCount]
  have pos : (0:ℝ)<C.card := by exact_mod_cast card_pos.mpr nonempty
  unfold neighborFraction
  field_simp

/-- The success probability for a retry of probability 100ρ at the actual
neighbor fraction q. -/
theorem success_probability (G : SimpleGraph V) (C : Finset V) (y : V) (ρ : ℝ)
    (nonempty : C.Nonempty) :
    successIn G C y (100*ρ) (fun _ ↦ True) =
      (1-neighborFraction G C y)*(1+100*ρ*neighborFraction G C y) := by
  rw [successIn_eq G C y _ _ nonempty]
  have total := card_filter_add_card_filter_not (s := C) (G.Adj y)
  have cast : ((C.filter (G.Adj y)).card:ℝ)+(C.filter (fun x ↦ ¬G.Adj y x)).card = C.card := by
    exact_mod_cast total
  have pos : (0:ℝ)<C.card := by exact_mod_cast card_pos.mpr nonempty
  congr 1
  simp only [and_true,neighborFraction]
  field_simp
  linarith

/-- Marginal output mass at a prescribed vertex. Every nonneighbor in the
row has the same mass; every other vertex has mass zero. -/
theorem output_atom (G : SimpleGraph V) (C : Finset V) (y v : V) (ρ : ℝ)
    (nonempty : C.Nonempty) :
    successIn G C y (100*ρ) (fun x ↦ x=v) =
      if v ∈ C ∧ ¬G.Adj y v then (1+100*ρ*neighborFraction G C y)/C.card else 0 := by
  rw [successIn_eq G C y _ _ nonempty]
  by_cases yes : v ∈ C ∧ ¬G.Adj y v
  · have eq : C.filter (fun x ↦ ¬G.Adj y x ∧ x=v) = {v} := by
      ext x
      simp only [mem_filter,mem_singleton]
      exact ⟨fun a ↦ a.2.2,fun he ↦ he.symm ▸ ⟨yes.1,yes.2,rfl⟩⟩
    simp [eq,yes.1,yes.2,div_eq_mul_inv,mul_comm]
  · have eq : C.filter (fun x ↦ ¬G.Adj y x ∧ x=v) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      obtain ⟨hc,adj,rfl⟩ := mem_filter.mp hx
      exact yes ⟨hc,adj⟩
    simp [eq,yes]

/-- Counting a sender's target neighbors and its row deficit pays the
baseline, the representative contribution, the deficit term, and an
additional 37ρr for each unit of nonneighbor fraction. -/
theorem source_surplus (G : SimpleGraph V) (C : Finset V) (y : V) (r : ℕ) (ρ g : ℝ)
    (nonempty : C.Nonempty) (hr : 0 < r) (hρ : 0 ≤ ρ) (coin : 100*ρ ≤ 1)
    (heavy : 1/2 ≤ neighborFraction G C y)
    (deficit : (r:ℝ)-C.card ≤ g*ρ*r) (margin : 37 ≤ 50*(1-ρ)-1-g) :
    let q := neighborFraction G C y
    let v := successIn G C y (100*ρ) (fun _ ↦ True)
    (r:ℝ)*(1-v+ρ*v)+2*((r:ℝ)-C.card)*(1-q)+37*ρ*r*(1-q) ≤
      ((C.filter (G.Adj y)).card:ℝ)+((r:ℝ)-C.card) := by
  dsimp only
  rw [success_probability G C y ρ nonempty]
  let q := neighborFraction G C y
  let d := (r:ℝ)-C.card
  have pos : (0:ℝ)<r := by exact_mod_cast hr
  have cpos : (0:ℝ)<C.card := by exact_mod_cast card_pos.mpr nonempty
  have qtop : q ≤ 1 := (div_le_one cpos).2 (by exact_mod_cast card_le_card (filter_subset ..))
  have exactDegree : (C.card:ℝ)*q = (C.filter (G.Adj y)).card := by
    dsimp [q,neighborFraction]
    field_simp
  change 1/2 ≤ q at heavy
  change d ≤ g*ρ*r at deficit
  have gain : g ≤ 100*q*(1-ρ)-1-37 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr heavy) (show 0 ≤ 1-ρ by linarith only [coin]),margin]
  have scaled := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left gain hρ) pos.le
  have spare : 0 ≤ (ρ*(100*q*(1-ρ)-1-37)*r-d)*(1-q) := by
    apply mul_nonneg _ (sub_nonneg.mpr qtop)
    linarith only [scaled,deficit]
  change (r:ℝ)*(1-(1-q)*(1+100*ρ*q)+ρ*((1-q)*(1+100*ρ*q)))+
    2*d*(1-q)+37*ρ*r*(1-q) ≤ ((C.filter (G.Adj y)).card:ℝ)+d
  dsimp only [d] at spare ⊢
  nlinarith only [spare,exactDegree]

end
end Erdos617.SenderRetry
