import ThirdPruningLists
import BalancedColoringCutoff

namespace Erdos617.ThirdPruning
open Finset ColoredLists PackingLists PruningOverlap PruningOverlap.Trace
open scoped Classical
noncomputable section
variable {V : Type*} [Fintype V] {r : ℕ} (T : Trace V r)

private theorem ordinary_in_range (E : Finset V) : ordinaryLists T E ⊆ range r := by
  intro i hi
  exact (mem_sdiff.mp (mem_sdiff.mp (mem_inter.mp hi).1).1).1

theorem third_cut_inputs {A : Finset V} {Δ : ℕ} {u : ℝ} (stage : Stage T A Δ u) (pr : Pruned T) :
    CutInputs (restrictLive T A) (incidenceCap T) := by
  let U := restrictLive T A
  refine ⟨restrict_first_stopped T A pr.first_stopped,fun i ↦ (restrict_assigned T A i) ▸ pr.source_cap i,?_⟩
  intro E e n α β M S hr no order lists
  let I := S.retained
  let O := ordinaryLists U E
  have sub : I ⊆ O := by dsimp only [I]; rw [S.retained_eq]; exact (filter_subset ..).trans sdiff_subset
  have raw := sub.trans (ordinary_in_range U E)
  have cap := deficit_count_cap T stage pr (by omega) order no lists
  have dc := sum_le_sum_of_subset_of_nonneg (f:=rowDeficit U E) sub
    (fun i hi _ ↦ deficit_nonneg U (by omega) no lists i hi)
  change (∑ i ∈ I, rowDeficit U E i) ≤ deficitSum U E at dc
  obtain ⟨sz,unused,cross⟩ := global_raw_budgets T (by omega) order pr.rows pr.least pr.pivots no
  have sizes := (sum_le_sum_of_subset_of_nonneg (f:=rawSurplus T) raw
    (fun _ _ _ ↦ le_max_right ..)).trans sz
  have load := sum_le_sum_of_subset_of_nonneg (f:=assigned T) raw (fun i _ _ ↦ by unfold assigned; positivity)
  have dest (v) (hv : v ∈ T.firstSources) := (qualifying_bounds T (by omega) (pr.destinations v hv)).1
  rw [assigned_total T dest] at load
  obtain ⟨v0,_,pc,_⟩ := raw_fractions T pr no (by omega) order
  change (∑ i ∈ I, rowDeficit U E i) + (∑ i ∈ I, rawSurplus T i) + (∑ i ∈ I, assigned U i) ≤ 7 ∧ _
  have loadsEq (i) : assigned U i = assigned T i := restrict_assigned T A i
  simp_rw [loadsEq]
  refine ⟨by linarith only [dc,cap.1,sizes,load,pc],by linarith only [dc,cap.1],?_⟩
  let K := I.biUnion (rowList U E)
  have ke (x) (hx : x ∈ K) : T.stop ≤ T.time x ∧ T.row x ∉ (∅ : Finset ℕ) := by
    obtain ⟨i,hi,h⟩ := mem_biUnion.mp hx
    have all := mem_biUnion.mpr ⟨i,sub hi,h⟩
    exact ⟨(mem_filter.mp (stage.sub ((ordinary_kept T A E stage.sub).1 all))).2,notMem_empty _⟩
  have zero : 2*((r:ℝ)-1)*0*r ≤ countEnds (T.forward ∅) := by simp [Trace.forward,Trace.oversized,countEnds,total]
  have inc := T.normalized_ordinary_bound ∅ K pr.legal ke (by omega) (variance T) 0 cross zero
  have empty : T.earlyOversized ∅=∅ := by simp [Trace.earlyOversized,Trace.oversized]
  dsimp only at inc
  rw [ordinary_total] at inc
  simp only [empty,empty_inter,card_empty,Nat.cast_zero,zero_div,mul_zero,sub_zero,add_zero] at inc
  rw [incidence_total,ordinary_total]
  change (∑ x ∈ K, unrecordedDegree (restrictLive T A) x)/(r:ℝ)^2 ≤ incidenceCap T
  simp_rw [restrict_degree]
  unfold incidenceCap firstRate secondRate
  linarith only [inc,v0]

/-- If the actual lists cannot give a witness, every valid combined budget for
them must consume the full logarithmic width, with exactly the same reserved rows. -/
theorem forced_width_cost {A E : Finset V} {Δ : ℕ} {u b α β C : ℝ}
    (stage : Stage T A Δ u) (pr : Pruned T) (hr : 2^143 ≤ r)
    (order : Fintype.card V=r^2+1) (no : ¬Witness T.color)
    (data : Lists (restrictLive T A) E) (band : RetainedWidth.Band (incidenceCap T) b α β)
    (budget : let U := restrictLive T A; WidthIntegral.RowBudget (ordinaryLists U E)
      (rowDeficit U E) (rowIncidence U E) (omittedCount U E) α β C) :
    Real.log (scale b/1120) ≤ C-WidthEndpoint.saving (firstRate T) := by
  let U := restrictLive T A
  let O := ordinaryLists U E
  let n := omittedCount U E
  let e := (range r \ O).card
  have pos : 0 < r := by omega
  have counts := card_sdiff_add_card_eq_card (ordinary_in_range U E)
  rw [card_range] at counts
  obtain ⟨var,_,pc,_⟩ := raw_fractions T pr no (by omega) order
  obtain ⟨sizes,costs,_⟩ := global_raw_budgets T (by omega) order pr.rows pr.least pr.pivots no
  have target (v) (hv : v ∈ T.firstSources) := qualifying_bounds T pos (pr.destinations v hv)
  have hd (i) (_ : i ∈ range r) (h : 0 < assigned T i) : rawSurplus T i ≤ 1/256 ∧ unused T i ≤ 1/1200 := by
    have ex : (T.firstSources.filter fun v ↦ T.destination v=i).Nonempty := by
      by_contra empty
      rw [assigned,not_nonempty_iff_eq_empty.mp empty] at h; simp at h
    obtain ⟨v,hv⟩ := ex
    obtain ⟨hf,rfl⟩ := mem_filter.mp hv
    refine ⟨?_,(target v hf).2.2⟩
    change max ((T.rowSize (T.destination v):ℝ)/r-1) 0 ≤ 1/256
    apply max_le _ (by norm_num)
    apply sub_le_iff_le_add.mpr
    apply (div_le_iff₀ (by exact_mod_cast pos : (0:ℝ)<r)).2
    have h : (256:ℝ)*T.rowSize (T.destination v) ≤ 257*r := by exact_mod_cast (target v hf).2.1
    linarith only [h]
  have omissions := WidthIntegral.omitted_slots_of_row_charges (range r) (rawSurplus T) (unused T)
    (assigned T) e n (fun _ _ ↦ le_max_right ..) (fun _ _ ↦ by unfold assigned; positivity)
    sizes (by linarith only [costs,var]) (assigned_total T (fun v h ↦ (target v h).1))
    (fun i _ ↦ pr.paid i) hd (omitted_ordinary ..)
  by_contra! width
  obtain ⟨S,sc⟩ := selected_at_143 O (rowDeficit U E) (rowIncidence U E) e n r band
    (show 0 ≤ firstRate T by unfold firstRate; positivity) pc
    (deficit_count_cap T stage pr (by omega) order no data).2 hr
    (deficit_nonneg U (by omega) no data) (fun i _ ↦ by unfold rowIncidence unrecordedDegree; positivity)
    counts omissions budget width
  exact contradiction_of_selected_rows U (third_cut_inputs T stage pr) (by omega) no order data band S sc

end
end Erdos617.ThirdPruning
