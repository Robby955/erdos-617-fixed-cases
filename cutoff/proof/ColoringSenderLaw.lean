import MarkedSenderLaw
import EligibleSenders
import RepresentativeMass

/-! Each coordinate law is selected by the original sender's actual strong destinations. -/

namespace Erdos617.ColoredLists

open Finset PruningOverlap FiniteLaw MarkedSender SenderRetry
open scoped Classical
noncomputable section
variable {V : Type*} {r : ℕ} [Fintype V] (T : Trace V r)

private theorem strong_nonempty {E rows} {v : V} {i : ℕ} (hi : i ∈ strongRows T E rows v) :
    (rowList T E i).Nonempty := by
  have d := (mem_filter.mp hi).2
  have nonzero : (0:ℝ) < (((rowList T E i).filter ((targetGraph T.color T.target).Adj v)).card:ℝ) :=
    lt_of_le_of_lt (by positivity) d
  exact (card_pos.mp (by exact_mod_cast nonzero)).mono (filter_subset ..)

/-- Outside H the coordinate has zero marking probability. In H the empty,
singleton and multiple strong-row cases determine its local sampling law. -/
def senderKind (E : Finset V) (parts : Finset ℕ) (s : ℕ) (v : V) : MarkedSender.Kind V :=
  let R := strongRows T E parts v
  if v ∈ senderSet T E parts s then
    if ne : R.Nonempty then
      if R.card = 1 then .unique (rowList T E (R.min' ne)) (strong_nonempty T (R.min'_mem ne))
      else .multiple
    else .moderate
  else .multiple

def uniqueGroup (E : Finset V) (parts : Finset ℕ) (s i : ℕ) :=
  (senderSet T E parts s).filter fun v ↦ strongRows T E parts v = {i}

/-- The unique groups use their actual row clique. -/
theorem unique_kind {E parts s i} {v : V} (hv : v ∈ uniqueGroup T E parts s i) :
    ∃ ne : (rowList T E i).Nonempty, senderKind T E parts s v = .unique (rowList T E i) ne := by
  obtain ⟨h,one⟩ := mem_filter.mp hv
  have mem : i ∈ strongRows T E parts v := one ▸ mem_singleton_self i
  refine ⟨strong_nonempty T mem,?_⟩
  simp [senderKind,h,one]

theorem unique_destination {E parts s i} {v : V} (hv : v ∈ uniqueGroup T E parts s i) :
    i ∈ parts ∧ (r:ℝ)/2 < (((rowList T E i).filter ((targetGraph T.color T.target).Adj v)).card:ℝ) := by
  have h : i ∈ strongRows T E parts v := (mem_filter.mp hv).2 ▸ mem_singleton_self i
  exact mem_filter.mp h

theorem disjoint_unique_groups (E parts s) {i k : ℕ} (ne : i ≠ k) :
    Disjoint (uniqueGroup T E parts s i) (uniqueGroup T E parts s k) := by
  apply disjoint_left.mpr
  intro v hi hk
  exact ne (singleton_inj.mp ((mem_filter.mp hi).2.symm.trans (mem_filter.mp hk).2))

/-- The eligibility mass of the coordinate agrees with the original
coloring's payment calculation for every sender, including zero and one row. -/
theorem kind_eligibility (E parts s) (v : V) :
    MarkedSender.eligible (targetGraph T.color T.target) v (senderKind T E parts s v) ((9/40:ℝ)/s) =
      if v ∈ senderSet T E parts s then senderEligibility T E parts s v else 0 := by
  by_cases hv : v ∈ senderSet T E parts s
  · by_cases empty : strongRows T E parts v = ∅
    · simp [senderKind,MarkedSender.eligible,senderEligibility,eligibleWeight,hv,empty]
    · have ne := nonempty_iff_ne_empty.mpr empty
      by_cases one : (strongRows T E parts v).card = 1
      · obtain ⟨i,eq⟩ := card_eq_one.mp one
        obtain ⟨non,kind⟩ := unique_kind T (show v ∈ uniqueGroup T E parts s i from mem_filter.mpr ⟨hv,eq⟩)
        simp [kind,MarkedSender.eligible,senderEligibility,eligibleWeight,hv,eq,rowSuccess]
      · simp [senderKind,MarkedSender.eligible,senderEligibility,eligibleWeight,hv,ne,one,empty]
  · simp [senderKind,MarkedSender.eligible,hv]

/-- The thinning argument and the same-row conflict calculation both use
this product of the original coloring's coordinate laws. -/
def senderLaw (E : Finset V) (parts : Finset ℕ) (s : ℕ) (p : ℝ) (rate : 100*((9/40:ℝ)/s) ≤ 1)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (v : V) : Law (MarkedSender.State V) :=
  MarkedSender.law (targetGraph T.color T.target) v (senderKind T E parts s v) ((9/40:ℝ)/s) p
    (by positivity) rate hp hp1

theorem sender_mark_mean (E : Finset V) (parts : Finset ℕ) (s : ℕ) (p : ℝ) (rate : 100*((9/40:ℝ)/s) ≤ 1)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (v : V) :
    (senderLaw T E parts s p rate hp hp1 v).expect marked =
      p*(if v ∈ senderSet T E parts s then senderEligibility T E parts s v else 0) := by
  unfold senderLaw
  rw [mark_mean,kind_eligibility]

/-- Thinning keeps the manuscript's bound j/r on each represented atom
and preserves the point's condition of being a nonneighbor of its sender. -/
theorem sender_atom_bound {E : Finset V} {e n : ℕ} {α β M : ℝ}
    (S : WidthIntegral.Selection (ordinaryLists T E) (rowDeficit T E) (rowIncidence T E) e n α β M)
    (hr : 0 < r) (X : ℝ) (lo : 0 ≤ X) (hi : X < 1120) (width : 2*β*S.w ≤ X)
    (p : ℝ) (rate : 100*((9/40:ℝ)/S.s) ≤ 1) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    {i : ℕ} {v : V} (hv : v ∈ uniqueGroup T E S.retained S.s i) (z : V) :
    (senderLaw T E S.retained S.s p rate hp hp1 v).weight (some (some z)) ≤ representativeFactor X/r := by
  obtain ⟨ne,kind⟩ := unique_kind T hv
  have bound := (retained_atom_bound T S hr X lo hi width (unique_destination T hv).1 v z).2
  unfold senderLaw
  rw [kind]
  change p*successIn _ _ _ _ _ ≤ _
  have positive : 0 ≤ successIn (targetGraph T.color T.target) (rowList T E i) v
      (100*((9/40:ℝ)/S.s)) (fun y ↦ y=z) := by
    rw [output_atom _ _ _ _ _ ne]
    split
    · unfold neighborFraction
      positivity
    · exact le_rfl
  exact (mul_le_of_le_one_left positive hp1).trans bound

end
end Erdos617.ColoredLists
