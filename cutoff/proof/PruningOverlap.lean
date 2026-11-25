import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic

/-! The two incidence counts in Appendix A, Section 2. An ordered pair (x,y)
denotes the end at x of the original undirected edge {x,y}. -/

namespace Erdos617.PruningOverlap

open Finset
open scoped Classical
noncomputable section

/-- The raw row indices are in extraction order. A sequential deletion has the
time of its step. Undeleted vertices have time at least stop. A first-stage
source records exactly one destination row. -/
structure Trace (V : Type*) (r : ℕ) where
  color : {e : Sym2 V // ¬ e.IsDiag} → Fin r
  target : Fin r
  row : V → ℕ
  time : V → ℕ
  firstEnd : ℕ
  stop : ℕ
  stages : firstEnd ≤ stop
  destination : V → ℕ

namespace Trace
variable {V : Type*} {r : ℕ} [Fintype V] (T : Trace V r)

/-- The original target edges between different raw rows. -/
def crossGraph : SimpleGraph V where
  Adj x y := ∃ h : T.row x ≠ T.row y,
    T.color ⟨s(x,y), fun d => h (congrArg T.row (Sym2.mk_isDiag_iff.mp d))⟩ = T.target
  symm := ⟨by
    rintro x y ⟨h, hc⟩
    exact ⟨h.symm, (congrArg T.color (Subtype.ext Sym2.eq_swap)).trans hc⟩⟩
  loopless := ⟨fun _ ⟨h, _⟩ => h rfl⟩

def rowSize (i : ℕ) : ℕ := (univ.filter fun x => T.row x = i).card

/-- The test is equivalent to |Rᵢ| − r > r/256, with no rounded cutoff. -/
def oversized (chosen : Finset ℕ) (x : V) : Prop :=
  T.row x ∈ chosen ∧ 257*r < 256*T.rowSize (T.row x)

/-- All live target neighbors actually available at the deletion of x.
In stage one only the recorded destination contributes. -/
def star (x : V) : Finset V := univ.filter fun y =>
  T.crossGraph.Adj x y ∧ T.time x < T.stop ∧ T.time x < T.time y ∧
    (T.time x < T.firstEnd → T.row y = T.destination x)

private theorem mem_star {x y : V} : y ∈ T.star x ↔
    T.crossGraph.Adj x y ∧ T.time x < T.stop ∧ T.time x < T.time y ∧
    (T.time x < T.firstEnd → T.row y = T.destination x) := by simp [star]

def quota (x : V) : ℝ :=
  if T.time x < T.firstEnd then (r : ℝ)/4 else
  if T.time x < T.stop then (199/400:ℝ)*r else 0

/-- The two properties of the deletion rule used in this count. The
additional internal-edge test for a qualifying row is unnecessary here. -/
structure Legal : Prop where
  degree : ∀ x, T.time x < T.stop → T.quota x < (T.star x).card
  destinationSmall : ∀ x, T.time x < T.firstEnd →
    256*T.rowSize (T.destination x) ≤ 257*r

def sourceWeight (x y : V) : ℝ :=
  if y ∈ T.star x then T.quota x / (T.star x).card else 0

def pruningCharge (x y : V) : ℝ :=
  T.sourceWeight x y + if T.time y < T.firstEnd then T.sourceWeight y x else 0

def recorded (x y : V) : Prop :=
  (T.time x < T.firstEnd ∧ y ∈ T.star x) ∨ (T.time y < T.firstEnd ∧ x ∈ T.star y)

def forward (chosen : Finset ℕ) (x y : V) : Prop :=
  T.oversized chosen x ∧ T.row x < T.row y ∧ T.crossGraph.Adj x y

def ordinary (kept : Finset V) (x y : V) : Prop :=
  x ∈ kept ∧ T.crossGraph.Adj x y ∧ ¬ T.recorded x y

def overlap (chosen : Finset ℕ) (x y : V) : ℝ :=
  if T.forward chosen x y then T.pruningCharge x y else 0

/-- Sum over original edge ends. Each function below vanishes off its own support. -/
def total (f : V → V → ℝ) : ℝ := ∑ x, ∑ y, f x y

def countEnds (P : V → V → Prop) : ℝ := total fun x y => if P x y then 1 else 0

def firstSources : Finset V := univ.filter fun x => T.time x < T.firstEnd
def secondSources : Finset V := univ.filter fun x => T.firstEnd ≤ T.time x ∧ T.time x < T.stop
def earlyOversized (chosen : Finset ℕ) : Finset V :=
  univ.filter fun x => T.oversized chosen x ∧ T.time x < T.stop

omit [Fintype V] in
private theorem quota_nonneg (x : V) : 0 ≤ T.quota x := by
  unfold quota
  split_ifs <;> positivity

private theorem source_nonneg (x y : V) : 0 ≤ T.sourceWeight x y := by
  unfold sourceWeight
  split_ifs
  · exact div_nonneg (T.quota_nonneg x) (Nat.cast_nonneg _)
  · rfl

private theorem source_le_one (x y : V) (legal : T.Legal) : T.sourceWeight x y ≤ 1 := by
  by_cases h : y ∈ T.star x
  · have hpos : 0 < ((T.star x).card : ℝ) :=
      lt_of_le_of_lt (T.quota_nonneg _) (legal.degree x ((T.mem_star).mp h).2.1)
    simpa [sourceWeight, h] using
      (div_le_one hpos).2 (legal.degree x ((T.mem_star).mp h).2.1).le
  · simp [sourceWeight, h]

private theorem source_total (x : V) (legal : T.Legal) :
    ∑ y, T.sourceWeight x y = T.quota x := by
  rw [show (∑ y, T.sourceWeight x y) =
      (T.star x).card * (T.quota x / (T.star x).card) by
    simp [sourceWeight]]
  by_cases hx : T.time x < T.stop
  · have hpos := lt_of_le_of_lt (T.quota_nonneg _) (legal.degree x hx)
    field_simp [ne_of_gt hpos]
  · have hfirst : ¬ T.time x < T.firstEnd := fun h => hx (h.trans_le T.stages)
    simp [quota, hx, hfirst]

private theorem charge_le_one (legal : T.Legal) (x y : V) :
    T.pruningCharge x y ≤ 1 := by
  by_cases hy : y ∈ T.star x
  · have rev : x ∉ T.star y := fun h =>
      (asymm ((T.mem_star).mp hy).2.2.1) ((T.mem_star).mp h).2.2.1
    simpa [pruningCharge, sourceWeight, rev] using T.source_le_one x y legal
  · by_cases first : T.time y < T.firstEnd
    · simpa [pruningCharge, sourceWeight, hy, first] using T.source_le_one y x legal
    · simp [pruningCharge, sourceWeight, hy, first]

/-- At a chosen oversized endpoint the incoming first-stage charge vanishes,
even if the other endpoint is also deleted later. -/
theorem charge_at_oversized {chosen : Finset ℕ} {x : V} (hx : T.oversized chosen x)
    (legal : T.Legal) (y : V) : T.pruningCharge x y = T.sourceWeight x y := by
  by_cases first : T.time y < T.firstEnd
  · have rev : x ∉ T.star y := by
      intro h
      have size := legal.destinationSmall y first
      rw [← ((T.mem_star).mp h).2.2.2 first] at size
      exact (not_lt_of_ge size) hx.2
    simp [pruningCharge, first, sourceWeight, rev]
  · simp [pruningCharge, first]

/-- A particular end is charged twice exactly when it is the forward end
in a chosen oversized row and the opposite vertex was in its deletion star. -/
theorem overlap_pos_iff (chosen : Finset ℕ) (legal : T.Legal) (x y : V) :
    0 < T.overlap chosen x y ↔ T.forward chosen x y ∧ y ∈ T.star x := by
  by_cases fwd : T.forward chosen x y
  · have source := T.charge_at_oversized fwd.1 legal y
    by_cases mem : y ∈ T.star x
    · have hr : (0:ℝ) < r := by exact_mod_cast (Nat.zero_le _).trans_lt T.target.isLt
      have active := ((T.mem_star).mp mem).2.1
      have quota_pos : 0 < T.quota x := by
        unfold quota
        split_ifs <;> positivity
      have card_pos : 0 < ((T.star x).card : ℝ) := by
        exact_mod_cast (Finset.card_pos.mpr ⟨y, mem⟩)
      simp [overlap, fwd, source, sourceWeight, mem, div_pos quota_pos card_pos]
    · simp [overlap, fwd, source, sourceWeight, mem]
  · simp [overlap, fwd]

/-- The actual duplicated weight is bounded by the quotas of the deleted
vertices in the chosen oversized rows, with each source counted once. -/
theorem overlap_le_deleted_quotas (chosen : Finset ℕ) (legal : T.Legal) :
    total (T.overlap chosen) ≤ ∑ x ∈ T.earlyOversized chosen, T.quota x := by
  unfold total earlyOversized
  rw [Finset.sum_filter]
  apply Finset.sum_le_sum
  intro x _
  by_cases big : T.oversized chosen x
  · have bound : (∑ y, T.overlap chosen x y) ≤ T.quota x := by
      rw [← T.source_total x legal]
      apply Finset.sum_le_sum
      intro y _
      by_cases edge : T.forward chosen x y
      · simp [overlap, edge, T.charge_at_oversized big legal y]
      · simpa [overlap, edge] using T.source_nonneg x y
    by_cases deleted : T.time x < T.stop
    · simpa [big, deleted] using bound
    · have late : ¬ T.time x < T.firstEnd := fun h => deleted (h.trans_le T.stages)
      simpa [big, deleted, quota, late] using bound
  · simp [overlap, forward, big]

/-- Inclusion-exclusion at the particular end x of the original edge {x,y}. -/
private theorem incidence_union (chosen : Finset ℕ) (kept : Finset V) (legal : T.Legal)
    (keptOK : ∀ x ∈ kept, T.stop ≤ T.time x ∧ T.row x ∉ chosen) (x y : V) :
    (if T.ordinary kept x y then (1:ℝ) else 0) + T.pruningCharge x y +
        (if T.forward chosen x y then 1 else 0) ≤
      (if T.crossGraph.Adj x y then 1 else 0) + T.overlap chosen x y := by
  by_cases fwd : T.forward chosen x y
  · have outside : ¬ T.ordinary kept x y := fun h => (keptOK x h.1).2 fwd.1.1
    simp [overlap, fwd, outside, fwd.2.2, add_comm]
  · by_cases adj : T.crossGraph.Adj x y
    · by_cases keep : T.ordinary kept x y
      · have src : y ∉ T.star x := fun h =>
          (not_lt_of_ge (keptOK x keep.1).1) ((T.mem_star).mp h).2.1
        have incoming : (if T.time y < T.firstEnd then T.sourceWeight y x else 0) = 0 := by
          by_cases first : T.time y < T.firstEnd
          · have rev : x ∉ T.star y := fun h => keep.2.2 (Or.inr ⟨first, h⟩)
            simp [first, sourceWeight, rev]
          · simp [first]
        have zero : T.pruningCharge x y = 0 := by
          unfold pruningCharge
          rw [incoming]
          simp [sourceWeight, src]
        simp [keep, adj, fwd, overlap, zero]
      · simpa [keep, adj, fwd, overlap] using T.charge_le_one legal x y
    · have outside : ¬ T.ordinary kept x y := fun h => adj h.2.1
      have rev : ¬ T.crossGraph.Adj y x := fun h => adj h.symm
      simp [outside, fwd, adj, overlap, pruningCharge, sourceWeight, T.mem_star, rev]

private theorem all_ends :
    countEnds T.crossGraph.Adj = 2 * (T.crossGraph.edgeFinset.card : ℝ) := by
  have per (x : V) :
      (∑ y, if T.crossGraph.Adj x y then (1:ℝ) else 0) = T.crossGraph.degree x := by
    simp [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter]
  unfold countEnds total
  simp_rw [per]
  exact_mod_cast T.crossGraph.sum_degrees_eq_twice_card_edges

private theorem pruning_total (legal : T.Legal) :
    total T.pruningCharge =
      (r:ℝ)/2 * T.firstSources.card + ((199/400:ℝ)*r) * T.secondSources.card := by
  have totals : total T.pruningCharge =
      ∑ x, (T.quota x + if T.time x < T.firstEnd then T.quota x else 0) := by
    unfold total pruningCharge
    simp only [Finset.sum_add_distrib, T.source_total _ legal]
    congr 1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    by_cases h : T.time x < T.firstEnd <;> simp [h, T.source_total _ legal]
  have per (x : V) :
      T.quota x + (if T.time x < T.firstEnd then T.quota x else 0) =
        (if x ∈ T.firstSources then (r:ℝ)/2 else 0) +
        (if x ∈ T.secondSources then (199/400:ℝ)*r else 0) := by
    by_cases f : T.time x < T.firstEnd
    · simp [quota, firstSources, secondSources, f, not_le.mpr f]
      ring
    · simp [quota, firstSources, secondSources, f, le_of_not_gt f]
  rw [totals]
  simp_rw [per]
  simp [Finset.sum_add_distrib, mul_comm]

/-- Raw incidence budget before normalization by r². Both counts and the
recorded stars are constructed from the original coloring and deletion order. -/
theorem incidence_budget (chosen : Finset ℕ) (kept : Finset V) (legal : T.Legal)
    (keptOK : ∀ x ∈ kept, T.stop ≤ T.time x ∧ T.row x ∉ chosen) :
    countEnds (T.ordinary kept) +
        ((r:ℝ)/2 * T.firstSources.card + ((199/400:ℝ)*r) * T.secondSources.card) +
        countEnds (T.forward chosen) ≤
      2 * (T.crossGraph.edgeFinset.card : ℝ) + ∑ x ∈ T.earlyOversized chosen, T.quota x := by
  have point := T.incidence_union chosen kept legal keptOK
  have bound : countEnds (T.ordinary kept) + total T.pruningCharge + countEnds (T.forward chosen) ≤
      countEnds T.crossGraph.Adj + total (T.overlap chosen) := by
    have hs := Finset.sum_le_sum (s := (univ : Finset V)) fun x _ =>
      Finset.sum_le_sum (s := (univ : Finset V)) fun y _ => point x y
    simpa only [countEnds, total, Finset.sum_add_distrib] using hs
  rw [T.pruning_total legal, T.all_ends] at bound
  exact bound.trans (add_le_add le_rfl (T.overlap_le_deleted_quotas chosen legal))

/-- First-stage sources cost r/4 each. Charging all early sources at the
second-stage rate overestimates the allowance by 99r/400 for every first-stage
source in the chosen oversized rows. -/
theorem deleted_quota_rebate (chosen : Finset ℕ) :
    (∑ x ∈ T.earlyOversized chosen, T.quota x) +
        (99/400:ℝ)*r * ((T.earlyOversized chosen ∩ T.firstSources).card : ℝ) =
      (199/400:ℝ)*r * ((T.earlyOversized chosen).card : ℝ) := by
  let E := T.earlyOversized chosen
  let rebate := (99/400:ℝ)*r
  have inter : E.filter (fun x => T.time x < T.firstEnd) = E ∩ T.firstSources := by
    ext x
    simp [firstSources]
  have refunds : (∑ x ∈ E, if T.time x < T.firstEnd then rebate else 0) =
      rebate * ((E ∩ T.firstSources).card : ℝ) := by
    rw [← Finset.sum_filter]
    simp [inter, mul_comm]
  change (∑ x ∈ E, T.quota x) + rebate * ((E ∩ T.firstSources).card : ℝ) = _
  rw [← refunds, ← Finset.sum_add_distrib]
  calc
    _ = ∑ _x ∈ E, (199/400:ℝ)*r := by
      apply Finset.sum_congr rfl
      intro x hx
      have deleted : T.time x < T.stop := ((Finset.mem_filter.mp hx).2).2
      by_cases first : T.time x < T.firstEnd
      · simp [quota, first, rebate]
        ring
      · simp [quota, first, deleted]
    _ = _ := by simp [E, mul_comm]

/-- The overlap alone is bounded by τr per deleted vertex in the selected
oversized rows. This is τ a r² in the manuscript's notation. -/
theorem overlap_le_paper_allowance (chosen : Finset ℕ) (legal : T.Legal) :
    total (T.overlap chosen) ≤ (199/400:ℝ)*r*((T.earlyOversized chosen).card : ℝ) := by
  have h := T.deleted_quota_rebate chosen
  have hrefund : 0 ≤ (99/400:ℝ)*r * ((T.earlyOversized chosen ∩ T.firstSources).card : ℝ) :=
    by positivity
  linarith only [T.overlap_le_deleted_quotas chosen legal, h, hrefund]

/-- Substitution of the two separate graph estimates into the incidence count.
Here v is the partition variance divided by r² and O is the sum of the
selected oversized surpluses divided by r. The last term saves the difference
between the two deletion rates on the first-stage sources in those rows. -/
theorem normalized_ordinary_bound (chosen : Finset ℕ) (kept : Finset V) (legal : T.Legal)
    (keptOK : ∀ x ∈ kept, T.stop ≤ T.time x ∧ T.row x ∉ chosen)
    (hr : 0 < r) (v O : ℝ)
    (crossCap : (T.crossGraph.edgeFinset.card : ℝ) ≤ (1-v)*(r:ℝ)^2)
    (rowFloor : 2*((r:ℝ)-1)*O*r ≤ countEnds (T.forward chosen)) :
    let p := (T.firstSources.card : ℝ)/r
    let t := (T.secondSources.card : ℝ)/r
    let a := ((T.earlyOversized chosen).card : ℝ)/r
    let a₁ := ((T.earlyOversized chosen ∩ T.firstSources).card : ℝ)/r
    countEnds (T.ordinary kept)/(r:ℝ)^2 ≤
      (2-p/2-(199/400)*t) - 2*v - 2*(1-1/(r:ℝ))*O + (199/400)*a - (99/400)*a₁ := by
  dsimp only
  have pos : (0:ℝ) < r := by exact_mod_cast hr
  apply (div_le_iff₀ (sq_pos_of_pos pos)).2
  have budget := T.incidence_budget chosen kept legal keptOK
  have refund := T.deleted_quota_rebate chosen
  convert_to countEnds (T.ordinary kept) ≤
      2*(1-v)*(r:ℝ)^2 - (r:ℝ)/2*T.firstSources.card -
      (199/400:ℝ)*r*T.secondSources.card - 2*((r:ℝ)-1)*O*r +
      (199/400:ℝ)*r*(T.earlyOversized chosen).card -
      (99/400:ℝ)*r*(T.earlyOversized chosen ∩ T.firstSources).card
  · field_simp [pos.ne']
    ring
  linarith only [budget, refund, crossCap, rowFloor]

end Trace
end
end Erdos617.PruningOverlap
