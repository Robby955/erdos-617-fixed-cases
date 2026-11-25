import SenderPopulation

/-! Eligibility counts before the independent thinning of the exterior senders. -/

namespace Erdos617.ColoredLists

open Finset
open scoped Classical
noncomputable section

private theorem exists_assignments (rows : Finset ℕ) :
    ∃ A ⊆ rows, A.card = min 2 rows.card := exists_subset_card_eq (min_le_right ..)

/-- Use both strong destinations when there are two, and choose any two when there are more. -/
def assignedStrong (rows : Finset ℕ) : Finset ℕ := (exists_assignments rows).choose

theorem assignedStrong_subset (rows : Finset ℕ) : assignedStrong rows ⊆ rows :=
  (exists_assignments rows).choose_spec.1

theorem assignedStrong_card (rows : Finset ℕ) : (assignedStrong rows).card = min 2 rows.card :=
  (exists_assignments rows).choose_spec.2

theorem assignedStrong_eq (rows : Finset ℕ) (small : rows.card ≤ 2) : assignedStrong rows = rows :=
  eq_of_subset_of_card_le (assignedStrong_subset rows) (by rw [assignedStrong_card,min_eq_right small])

/-- Before thinning, a moderate sender succeeds automatically. A unique strong
sender retries in its only strong row. Senders assigned twice are ineligible. -/
def eligibleWeight (rows : Finset ℕ) (success : ℕ → ℝ) : ℝ :=
  if rows.card = 0 then 1 else if rows.card = 1 then ∑ i ∈ rows, success i else 0

/-- Keep the extra charge only for senders with a unique strong row. -/
def uniqueCharge (rows : Finset ℕ) (charge : ℕ → ℝ) : ℝ :=
  if rows.card = 1 then ∑ i ∈ rows, charge i else 0

/-- Compare the eligibility lost at a single sender to its assigned incidences.
The surplus is added once, even when many rows are strong. -/
theorem assignment_payment (rows : Finset ℕ) (r : ℝ) (success charge pay : ℕ → ℝ)
    (unique : ∀ i ∈ rows, r*(1-success i)+charge i ≤ pay i)
    (double : ∀ i ∈ rows, r/2 ≤ pay i) :
    r*(1-eligibleWeight rows success)+uniqueCharge rows charge ≤
      ∑ i ∈ assignedStrong rows, pay i := by
  by_cases zero : rows.card = 0
  · have empty := card_eq_zero.mp zero
    have chosen := assignedStrong_eq rows (by omega)
    rw [chosen]
    simp [eligibleWeight,uniqueCharge,empty]
  by_cases single : rows.card = 1
  · obtain ⟨i,eq⟩ := card_eq_one.mp single
    have chosen := assignedStrong_eq rows (by omega)
    rw [chosen]
    simpa [eligibleWeight,uniqueCharge,eq] using unique i (eq ▸ mem_singleton_self i)
  · have count : (assignedStrong rows).card = 2 := by rw [assignedStrong_card,min_eq_left (by omega)]
    have sum := sum_le_sum (s := assignedStrong rows) fun i hi ↦ double i (assignedStrong_subset rows hi)
    simp only [sum_const,nsmul_eq_mul,count,Nat.cast_ofNat] at sum
    simp [eligibleWeight,uniqueCharge,zero,single]
    linarith only [sum]

end
end Erdos617.ColoredLists
