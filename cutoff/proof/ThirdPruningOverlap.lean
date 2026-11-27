import ThirdPruningIncidence

/-! The two original quota payments and the third-stage contribution on a
common set of retained vertices. -/
namespace Erdos617.ThirdPruning
open Finset PruningOverlap PruningOverlap.Trace ColoredLists PackingLists
open scoped Classical
noncomputable section
variable {V : Type*} [Fintype V] {r : ℕ} (T : Trace V r)

theorem live_unrecorded_degree {x : V} (hx : x ∈ live T) :
    deg T.crossGraph (live T) x ≤ unrecordedDegree T x := by
  have lx := (mem_filter.mp hx).2
  have h := T.stages
  unfold deg unrecordedDegree
  rw [natCast_card_filter]
  unfold live
  rw [sum_filter]
  apply sum_le_sum
  intro y _
  by_cases ly : T.stop ≤ T.time y
  · have earlyx : ¬T.time x<T.firstEnd := by omega
    have earlyy : ¬T.time y<T.firstEnd := by omega
    simp [ly,Trace.recorded,earlyx,earlyy]
  · simp [ly]; split_ifs <;> norm_num

/-- Incoming ends at new sources with an unchosen row can be paid inside the
old ordinary budget. A new source in a chosen oversized row costs at most the
overlap allowance for that same vertex. -/
theorem incidence_after_third (A K : Finset V) (C : Finset ℕ) (sub : A ⊆ live T)
    (kept : K ⊆ A) (outside : ∀ x ∈ K, T.row x ∉ C) (legal : T.Legal)
    (removed : ∀ x ∈ live T \ A, (9/25:ℝ)*r ≤ deg T.crossGraph (live T) x) :
    let B := oversizedRows univ T.row C r
    (∑ x ∈ K, unrecordedDegree T x) + (r:ℝ)/2*T.firstSources.card +
        ((199/400:ℝ)*r)*T.secondSources.card + ((9/25:ℝ)*r)*(live T \ A).card +
        countEnds (T.forward C) ≤ 2*(T.crossGraph.edgeFinset.card:ℝ) +
          ((199/400:ℝ)*r)*(verticesIn (univ \ A) T.row B).card := by
  intro B
  let D := live T \ A
  let L := D.filter fun x ↦ T.row x ∉ B
  let H := D.filter fun x ↦ T.row x ∈ B
  have bsub : B ⊆ C := filter_subset ..
  have kdis : Disjoint K L := disjoint_left.mpr fun x hk hl ↦
    (mem_sdiff.mp (mem_filter.mp hl).1).2 (kept hk)
  have keep (x) (hx : x ∈ K ∪ L) : T.stop ≤ T.time x ∧ T.row x ∉ B := by
    rcases mem_union.mp hx with hk|hl
    · exact ⟨(mem_filter.mp (sub (kept hk))).2,fun h ↦ outside x hk (bsub h)⟩
    · exact ⟨(mem_filter.mp (mem_sdiff.mp (mem_filter.mp hl).1).1).2,(mem_filter.mp hl).2⟩
  have inc := T.incidence_budget B _ legal keep
  rw [ordinary_total,sum_union kdis] at inc
  have refund := T.deleted_quota_rebate B
  have refund0 : 0 ≤ (99/400:ℝ)*r*((T.earlyOversized B ∩ T.firstSources).card : ℝ) := by positivity
  have big (x : V) : T.oversized B x ↔ T.row x ∈ B := by
    exact ⟨And.left, fun h ↦ ⟨h,(mem_filter.mp h).2⟩⟩
  have ident : T.forward B = T.forward C := by
    funext x y
    apply propext
    simp only [Trace.forward,big]
    change (_ ∧ _) ↔ (_ ∧ _)
    rw [show T.row x ∈ B ↔ T.oversized C x from mem_filter]
  rw [ident] at inc
  have lcost : ((9/25:ℝ)*r)*L.card ≤ ∑ x ∈ L, unrecordedDegree T x := by
    have h := sum_le_sum (s:=L) fun x hx ↦ (removed x (mem_filter.mp hx).1).trans
      (live_unrecorded_degree T (mem_sdiff.mp (mem_filter.mp hx).1).1)
    simpa [mul_comm] using h
  have partition : H.card+L.card=D.card := by
    dsimp [H,L]
    exact card_filter_add_card_filter_not ..
  have union : T.earlyOversized B ∪ H = verticesIn (univ \ A) T.row B := by
    ext x
    simp only [Trace.earlyOversized,verticesIn,H,D,mem_union,mem_sdiff,mem_filter,mem_univ,true_and,
      big,live,not_le]
    have h : x ∈ A → T.stop ≤ T.time x := fun hx ↦ (mem_filter.mp (sub hx)).2
    by_cases earlier : T.time x < T.stop
    · have n : x ∉ A := fun mem ↦ (not_lt.mpr (h mem)) earlier
      simp [earlier,not_le.mpr earlier,n]
    · simp [earlier,not_lt.mp earlier,and_comm]
  have dis : Disjoint (T.earlyOversized B) H := by
    apply disjoint_left.mpr
    intro x old new
    exact (not_lt.mpr (mem_filter.mp (mem_sdiff.mp (mem_filter.mp new).1).1).2) (mem_filter.mp old).2.2
  have all : ((T.earlyOversized B).card:ℝ)+H.card = (verticesIn (univ \ A) T.row B).card := by
    exact_mod_cast (card_union_of_disjoint dis).symm.trans (congrArg Finset.card union)
  have count : (H.card:ℝ)+L.card = D.card := by exact_mod_cast partition
  have rate : ((9/25:ℝ)*r)*H.card ≤ ((199/400:ℝ)*r)*H.card :=
    mul_le_mul_of_nonneg_right (by linarith [Nat.cast_nonneg (α:=ℝ) r]) (Nat.cast_nonneg _)
  change _ + ((9/25:ℝ)*r)*D.card + _ ≤ _
  rw [← count,← all]
  linarith only [inc,refund,refund0,lcost,rate]

end
end Erdos617.ThirdPruning
