import ThirdPruningOverlap
import ThirdPruningWidth
import ThirdPruningMass

namespace Erdos617.ThirdPruning
open Finset PruningOverlap PruningOverlap.Trace ColoredLists PackingLists
open scoped Classical
noncomputable section
variable {V : Type*} [Fintype V] {r : ℕ} (T : Trace V r)

def spentFraction := 1-(T.crossGraph.edgeFinset.card:ℝ)/(r:ℝ)^2
def survivingFraction (A : Finset V) := edges T.crossGraph A / (r:ℝ)^2
def thirdRate (A : Finset V) := ((live T \ A).card:ℝ)/r
def remaining := 1-firstRate T/4-(199/400)*secondRate T
def incidenceCap := 2-firstRate T/2-(199/400)*secondRate T

structure Pass (A : Finset V) : Prop where
  sub : A ⊆ live T
  stop : ∀ x ∈ A, deg T.crossGraph A x ≤ (9/25:ℝ)*r
  removed : ∀ x ∈ live T \ A, (9/25:ℝ)*r ≤ deg T.crossGraph (live T) x
  cost : edges T.crossGraph A + (r:ℝ)/4*T.firstSources.card +
      ((199/400:ℝ)*r)*T.secondSources.card + ((9/25:ℝ)*r)*(live T \ A).card +
      (∑ x ∈ univ \ A, max (deg T.crossGraph A x-(199/400:ℝ)*r) 0) ≤ T.crossGraph.edgeFinset.card

theorem exists_pass (legal : T.Legal) : ∃ A, Pass T A := by
  obtain ⟨A,sub,stop,removed,cost⟩ := three_pass_cost T legal
  exact ⟨A,sub,stop,removed,cost⟩

theorem normalized_cost {A : Finset V} (pass : Pass T A) (hr : 0 < r) :
    let slack := remaining T-spentFraction T-survivingFraction T A-(9/25)*thirdRate T A
    0 ≤ slack ∧ (∑ x ∈ univ \ A, max (deg T.crossGraph A x-(199/400:ℝ)*r) 0) ≤ slack*(r:ℝ)^2 := by
  intro slack
  have pos : (0:ℝ)<r := by exact_mod_cast hr
  have cost := pass.cost
  have eq : slack*(r:ℝ)^2 = (T.crossGraph.edgeFinset.card:ℝ) - edges T.crossGraph A -
      (r:ℝ)/4*T.firstSources.card - ((199/400:ℝ)*r)*T.secondSources.card -
      ((9/25:ℝ)*r)*(live T \ A).card := by
    dsimp [slack,remaining,spentFraction,survivingFraction,thirdRate,firstRate,secondRate]
    field_simp
    ring
  have h : (∑ x ∈ univ \ A, max (deg T.crossGraph A x-(199/400:ℝ)*r) 0) ≤ slack*(r:ℝ)^2 := by
    rw [eq]; linarith only [cost]
  exact ⟨nonneg_of_mul_nonneg_left ((sum_nonneg (fun _ _ ↦ le_max_right ..)).trans h) (sq_pos_of_pos pos),h⟩

theorem all_deleted {A : Finset V} (sub : A ⊆ live T) :
    ((univ \ A).card:ℝ)/r = firstRate T + secondRate T + thirdRate T A := by
  have eq := card_sdiff_add_card_eq_card sub
  have old := card_sdiff_add_card_eq_card (subset_univ (live T))
  have new := card_sdiff_add_card_eq_card (subset_univ A)
  have nat : (univ \ A).card = (univ \ live T).card + (live T \ A).card := by omega
  rw [nat,Nat.cast_add,add_div,deleted_rate,thirdRate]

theorem raw_fractions (pr : Pruned T) (no : ¬Witness T.color)
    (hr : 2 ≤ r) (order : Fintype.card V=r^2+1) :
    0 ≤ variance T ∧ variance T ≤ spentFraction T ∧ firstRate T ≤ 125/61 ∧
    firstRate T/4+(199/400)*secondRate T ≤ 1 := by
  have pos : (0:ℝ)<r := by exact_mod_cast (show 0<r by omega)
  obtain ⟨surplus,unused,cross⟩ := global_raw_budgets T hr order pr.rows pr.least pr.pivots no
  have dest (v) (hv : v ∈ T.firstSources) := (qualifying_bounds T (by omega) (pr.destinations v hv)).1
  have var : 0 ≤ variance T := by unfold variance; positivity
  have h := sum_le_sum (s:=range r) (fun i _ ↦ pr.paid i)
  rw [← mul_sum,assigned_total T dest] at h
  have c : (T.crossGraph.edgeFinset.card:ℝ)/(r:ℝ)^2 ≤ 1-variance T :=
    (div_le_iff₀ (sq_pos_of_pos pos)).mpr cross
  exact ⟨var,by unfold spentFraction; linarith only [c],by linarith only [h,unused,var],
    pruning_rates T pr.legal (by omega) (cross.trans (by nlinarith only [mul_nonneg var (sq_nonneg (r:ℝ))]))⟩

end
end Erdos617.ThirdPruning
