import CutInputs
import ThirdPruningRowHoles

/-! Preserve the recorded stars of the first pass while using a smaller final
set for the lists and for the signed cut. -/
namespace Erdos617.ThirdPruning
open Finset PruningOverlap ColoredLists
open scoped Classical
noncomputable section
variable {V : Type*} {r : ℕ} [Fintype V] (T : Trace V r)

def restrictLive (A : Finset V) : Trace V r :=
  { T with time := fun x ↦ if T.time x < T.stop then T.time x else
                             if x ∈ A then T.stop+1 else T.stop
           stop := T.stop+1
           stages := T.stages.trans (Nat.le_succ _) }

theorem restrict_live (A : Finset V) (sub : A ⊆ live T) : live (restrictLive T A) = A := by
  ext x
  have inside : x ∈ A → T.stop ≤ T.time x := fun h ↦ (mem_filter.mp (sub h)).2
  by_cases hx : x ∈ A
  · have late := inside hx
    simp [live,restrictLive,hx,not_lt.mpr late]
  · by_cases h : T.time x < T.stop <;> simp [live,restrictLive,h,hx] <;> omega

private theorem first_iff (A : Finset V) (x : V) :
    (restrictLive T A).time x < T.firstEnd ↔ T.time x < T.firstEnd := by
  have cut := T.stages
  dsimp [restrictLive]
  split_ifs <;> omega

theorem restrict_sources (A : Finset V) : (restrictLive T A).firstSources = T.firstSources := by
  ext x
  simp only [Trace.firstSources,mem_filter,mem_univ,true_and]
  exact first_iff T A x

private theorem first_star (A : Finset V) {x : V} (hx : T.time x < T.firstEnd) :
    (restrictLive T A).star x = T.star x := by
  ext y
  have early := hx.trans_le T.stages
  have cmp : (restrictLive T A).time x < (restrictLive T A).time y ↔ T.time x < T.time y := by
    dsimp [restrictLive]
    simp only [if_pos early]
    split_ifs <;> omega
  simp only [Trace.star,mem_filter,mem_univ,true_and]
  change (T.crossGraph.Adj x y ∧ _ ∧ _ ∧ _) ↔ _
  rw [cmp]
  have xeq : (restrictLive T A).time x = T.time x := if_pos early
  rw [xeq]
  change (_ ∧ T.time x < T.stop+1 ∧ _ ∧ _) ↔ (_ ∧ T.time x < T.stop ∧ _ ∧ _)
  simp only [early,early.trans (Nat.lt_succ_self _),true_and]
  rfl

theorem restrict_recorded (A : Finset V) (x y : V) :
    (restrictLive T A).recorded x y ↔ T.recorded x y := by
  unfold Trace.recorded
  change (_ < T.firstEnd ∧ _) ∨ (_ < T.firstEnd ∧ _) ↔ _
  rw [first_iff,first_iff]
  by_cases hx : T.time x < T.firstEnd <;> by_cases hy : T.time y < T.firstEnd <;>
    simp_all only [first_star, false_and,true_and, false_or, or_false]

theorem restrict_degree (A : Finset V) (x : V) :
    unrecordedDegree (restrictLive T A) x = unrecordedDegree T x := by
  unfold unrecordedDegree
  exact sum_congr rfl fun y _ ↦ by
    change (if T.crossGraph.Adj x y ∧ ¬(restrictLive T A).recorded x y then _ else _) = _
    rw [restrict_recorded]

theorem restrict_first_stopped (A : Finset V) (done : FirstStageStopped T) :
    FirstStageStopped (restrictLive T A) := by
  let B := univ.filter fun x ↦ (restrictLive T A).firstEnd ≤ (restrictLive T A).time x
  have eq : B = univ.filter (fun x ↦ T.firstEnd ≤ T.time x) := by
    ext x
    simp only [B,mem_filter,mem_univ,true_and]
    exact le_iff_le_iff_lt_iff_lt.mpr (first_iff T A x)
  change ∀ x ∈ B, ∀ i ∈ qualifying T, 4*(B.filter fun y ↦ T.crossGraph.Adj x y ∧ T.row y = i).card ≤ r
  rw [eq]
  exact done

theorem restrict_assigned (A : Finset V) (i : ℕ) :
    assigned (restrictLive T A) i = assigned T i := by
  simp only [assigned,restrict_sources]
  rfl

end
end Erdos617.ThirdPruning
