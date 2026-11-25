import SenderDestinations
import HeavyRowSenders

/-! Count distinct senders and their strong attachments on the original selected rows. -/

namespace Erdos617.ColoredLists

open Finset PackingLists PruningOverlap
open scoped Classical
noncomputable section
variable {V : Type*} {r : ℕ} [Fintype V] (T : Trace V r)

/-- Strong rows of a sender are counted before making any choice of an assignment. -/
def strongRows (E : Finset V) (rows : Finset ℕ) (v : V) :=
  rows.filter fun i ↦ (r:ℝ)/2 < (((rowList T E i).filter ((targetGraph T.color T.target).Adj v)).card:ℝ)

/-- Vertices with two or more strong destinations cost at least two actual
incidences each. The shortage and the retained deficits are in vertex units. -/
theorem sender_population (prep : Prepared T) (hr : 3 ≤ r) (no : ¬Witness T.color)
    (order : Fintype.card V = r^2+1) {E : Finset V} {e n : ℕ} {α β M Y b : ℝ}
    (lists : ListBounds (targetGraph T.color T.target) T.row univ (live T)
      (range r) (qualifying T) E r)
    (S : WidthIntegral.Selection (ordinaryLists T E) (rowDeficit T E) (rowIncidence T E) e n α β M)
    (band : RetainedWidth.Band Y b α β) (slots : e+(ordinaryLists T E).card = r) :
    let H := senderSet T E S.retained S.s
    let N := strongRows T E S.retained
    let Δ := ((S.s-1:ℕ):ℝ)*r-((lowExterior T E S.retained S.s).card:ℝ)
    1+Δ+((H.filter fun v ↦ 2 ≤ (N v).card).card:ℝ) ≤
      ((H.filter fun v ↦ (N v).card = 0).card:ℝ) + ∑ i ∈ S.retained, ((r:ℝ)-(rowList T E i).card) := by
  let H := senderSet T E S.retained S.s
  let N := strongRows T E S.retained
  let heavy := fun v i ↦ (r:ℝ)/2 < (((rowList T E i).filter ((targetGraph T.color T.target).Adj v)).card:ℝ)
  let arrivals := fun i ↦ H.filter fun v ↦ heavy v i
  let δ := fun i ↦ (r:ℝ)-(rowList T E i).card
  have rowBound (i) (hi : i ∈ S.retained) : ((arrivals i).card:ℝ) ≤ 2*δ i := by
    have dis : Disjoint (rowList T E i) (arrivals i) := by
      apply disjoint_left.mpr
      intro v hv h
      exact ((mem_senderSet T).mp (mem_filter.mp h).1).1 (mem_biUnion.mpr ⟨i,hi,hv⟩)
    have bound := (retained_heavy_senders T prep hr no lists S band hi (arrivals i) dis
      (fun _ hv ↦ (mem_filter.mp hv).2)).1
    have ordinary : i ∈ ordinaryLists T E := by
      rw [S.retained_eq] at hi
      exact (mem_sdiff.mp (mem_filter.mp hi).1).1
    have unused := (mem_sdiff.mp (mem_sdiff.mp (mem_inter.mp ordinary).1).1).2
    have cap := (caps_of_no_witness T.color T.target (by omega) no).2 _ (lists.clique i unused)
    change (rowList T E i).card ≤ r at cap
    dsimp only [δ]
    rw [← Nat.cast_sub (R := ℝ) cap]
    exact_mod_cast bound
  have swap : (∑ v ∈ H, (N v).card) = ∑ i ∈ S.retained, (arrivals i).card := by
    change (∑ v ∈ H, (S.retained.filter (heavy v)).card) =
      ∑ i ∈ S.retained, (H.filter fun v ↦ heavy v i).card
    simp only [card_filter]
    rw [sum_comm]
  have each (v : V) (_ : v ∈ H) : 1+(if 2 ≤ (N v).card then 1 else 0) ≤
      (if (N v).card = 0 then 1 else 0)+(N v).card := by split_ifs <;> omega
  have classified := sum_le_sum (s := H) each
  simp only [sum_add_distrib,sum_const,nsmul_one,← card_filter,swap] at classified
  have counted : (H.card:ℝ) + (H.filter fun v ↦ 2 ≤ (N v).card).card ≤
      ((H.filter fun v ↦ (N v).card=0).card:ℝ) + ∑ i ∈ S.retained, ((arrivals i).card:ℝ) := by
    exact_mod_cast classified
  have upper := sum_le_sum rowBound
  rw [← mul_sum] at upper
  have ledger := sender_ledger T S order slots
  change (H.card:ℝ) = _ + ∑ i ∈ S.retained, δ i at ledger
  change _ ≤ ((H.filter fun v ↦ (N v).card=0).card:ℝ)+∑ i ∈ S.retained, δ i
  linarith only [ledger,counted,upper]

end
end Erdos617.ColoredLists
