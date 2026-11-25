import JointSenderLaw
import SenderRetry
import Mathlib.Data.Fintype.BigOperators

/-! Local legal sender states. Each successful retry draw is retained by an independent thinning coin. -/

namespace Erdos617.MarkedSender

open Finset FiniteLaw SenderRetry
open scoped Classical
noncomputable section
variable {V : Type*} [Fintype V]

inductive Kind (V : Type*) where
  | moderate
  | multiple
  | unique (row : Finset V) (nonempty : row.Nonempty)

/-- The outer option records the mark; a marked moderate vertex carries no representative. -/
abbrev State (V : Type*) := Option (Option V)

def eligible (G : SimpleGraph V) (y : V) (kind : Kind V) (ρ : ℝ) : ℝ :=
  match kind with
  | .moderate => 1
  | .multiple => 0
  | .unique C _ => successIn G C y (100*ρ) (fun _ ↦ True)

private def eligibleState (G : SimpleGraph V) (y : V) (kind : Kind V) (ρ : ℝ) (o : Option V) : ℝ :=
  match kind,o with
  | .moderate,none => 1
  | .unique C _,some v => successIn G C y (100*ρ) (fun x ↦ x=v)
  | _,_ => 0

omit [Fintype V] in
private theorem retry_range (G : SimpleGraph V) (y : V) (C : Finset V) (hC : C.Nonempty)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (rate : 100*ρ ≤ 1) :
    0 ≤ successIn G C y (100*ρ) (fun _ ↦ True) ∧
      successIn G C y (100*ρ) (fun _ ↦ True) ≤ 1 := by
  rw [success_probability G C y ρ hC]
  let q := neighborFraction G C y
  have q0 : 0 ≤ q := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have q1 : q ≤ 1 := (div_le_one (by exact_mod_cast card_pos.mpr hC)).2
    (by exact_mod_cast card_le_card (filter_subset ..))
  change 0 ≤ (1-q)*(1+100*ρ*q) ∧ (1-q)*(1+100*ρ*q) ≤ 1
  have g : 100*ρ*q ≤ q := by simpa using mul_le_mul_of_nonneg_right rate q0
  exact ⟨mul_nonneg (sub_nonneg.mpr q1) (by positivity),
    by nlinarith only [mul_le_mul_of_nonneg_left g (sub_nonneg.mpr q1),sq_nonneg q]⟩

omit [Fintype V] in
theorem eligible_range (G : SimpleGraph V) (y : V) (kind : Kind V) {ρ : ℝ}
    (hρ : 0 ≤ ρ) (rate : 100*ρ ≤ 1) : 0 ≤ eligible G y kind ρ ∧ eligible G y kind ρ ≤ 1 := by
  cases kind with
  | moderate => norm_num [eligible]
  | multiple => norm_num [eligible]
  | unique C hC => exact retry_range G y C hC hρ rate

private theorem eligibleState_sum (G : SimpleGraph V) (y : V) (kind : Kind V) (ρ : ℝ) :
    (∑ o, eligibleState G y kind ρ o) = eligible G y kind ρ := by
  rw [Fintype.sum_option]
  cases kind with
  | moderate => simp [eligibleState,eligible]
  | multiple => simp [eligibleState,eligible]
  | unique C hC =>
    simp only [eligibleState,zero_add,eligible]
    simp_rw [output_atom G C y _ ρ hC]
    rw [successIn_eq G C y _ _ hC]
    simp only [and_true]
    let K := C.filter fun v ↦ ¬G.Adj y v
    have eq : (univ.filter fun v ↦ v ∈ C ∧ ¬G.Adj y v) = K := by ext v; simp [K]
    rw [← sum_filter,eq,sum_const,nsmul_eq_mul]
    ring

omit [Fintype V] in
private theorem eligibleState_nonneg (G : SimpleGraph V) (y : V) (kind : Kind V)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (o : Option V) : 0 ≤ eligibleState G y kind ρ o := by
  cases kind <;> cases o <;> simp only [eligibleState] <;> try positivity
  rw [output_atom _ _ _ _ _ (by assumption)]
  split
  · unfold neighborFraction; positivity
  · exact le_rfl

/-- Thin a moderate mark or a successful unique representative. A multiple
sender stays unmarked. All mass rejected by the thinning or retry is placed
on the single unmarked state. -/
def law (G : SimpleGraph V) (y : V) (kind : Kind V) (ρ p : ℝ)
    (hρ : 0 ≤ ρ) (rate : 100*ρ ≤ 1) (hp : 0 ≤ p) (hp1 : p ≤ 1) : Law (State V) where
  weight o := match o with
    | none => 1-p*eligible G y kind ρ
    | some v => p*eligibleState G y kind ρ v
  nonneg o := by
    cases o with
    | none =>
      apply sub_nonneg.mpr
      simpa using mul_le_mul hp1 (eligible_range G y kind hρ rate).2
        (eligible_range G y kind hρ rate).1 zero_le_one
    | some v => exact mul_nonneg hp (eligibleState_nonneg G y kind hρ v)
  total := by
    erw [Fintype.sum_option]
    change 1-p*eligible G y kind ρ+(∑ v, p*eligibleState G y kind ρ v)=1
    rw [← mul_sum,eligibleState_sum]; ring

def marked (o : State V) : ℝ := if o.isSome then 1 else 0

/-- Increasing the thinning rate by a factor of at most k increases the
weight of any single sender state by at most k, including the unmarked state. -/
theorem oversample_weight (G : SimpleGraph V) (y : V) (kind : Kind V)
    (ρ p q k : ℝ) (hρ : 0 ≤ ρ) (rate : 100*ρ ≤ 1)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hk : 1 ≤ k) (inc : p ≤ q) (cap : q ≤ k*p) (o : State V) :
    (law G y kind ρ q hρ rate hq hq1).weight o ≤ k*(law G y kind ρ p hρ rate hp hp1).weight o := by
  cases o with
  | none =>
    have base := (law G y kind ρ p hρ rate hp hp1).nonneg none
    change 0 ≤ 1-p*eligible G y kind ρ at base
    change 1-q*eligible G y kind ρ ≤ k*(1-p*eligible G y kind ρ)
    calc
      _ ≤ 1-p*eligible G y kind ρ :=
        sub_le_sub_left (mul_le_mul_of_nonneg_right inc (eligible_range G y kind hρ rate).1) _
      _ ≤ _ := le_mul_of_one_le_left base hk
  | some v =>
    change q*eligibleState G y kind ρ v ≤ k*(p*eligibleState G y kind ρ v)
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right cap (eligibleState_nonneg G y kind hρ v)

theorem mark_mean (G : SimpleGraph V) (y : V) (kind : Kind V) (ρ p : ℝ)
    (hρ : 0 ≤ ρ) (rate : 100*ρ ≤ 1) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    (law G y kind ρ p hρ rate hp hp1).expect marked = p*eligible G y kind ρ := by
  unfold Law.expect
  erw [Fintype.sum_option]
  change _*marked (none:State V)+(∑ a : Option V, p*eligibleState G y kind ρ a * marked (some a))=_
  simp only [marked,Option.isSome_none,Option.isSome_some,Bool.false_eq_true,ite_false,ite_true,
    mul_zero,mul_one,zero_add,← mul_sum,eligibleState_sum]

theorem unique_atom (G : SimpleGraph V) (y : V) (C : Finset V) (hC : C.Nonempty) (ρ p : ℝ)
    (hρ : 0 ≤ ρ) (rate : 100*ρ ≤ 1) (hp : 0 ≤ p) (hp1 : p ≤ 1) (v : V) :
    (law G y (.unique C hC) ρ p hρ rate hp hp1).weight (some (some v)) =
      if v ∈ C ∧ ¬G.Adj y v then p*((1+100*ρ*neighborFraction G C y)/C.card) else 0 := by
  change p*successIn G C y (100*ρ) (fun x ↦ x=v) = _
  rw [output_atom G C y v ρ hC,mul_ite,mul_zero]

end
end Erdos617.MarkedSender
