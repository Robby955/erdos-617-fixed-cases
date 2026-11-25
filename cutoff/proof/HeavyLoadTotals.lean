import HeavyLoadBound

/-! Sum the original destination counts before truncating by their uniform
cap. The resulting bound controls how many rows are tested in expectation. -/

namespace Erdos617.ColoredLists

open Finset PruningOverlap PruningOverlap.Trace PackingLists FiniteLaw
open scoped Classical
noncomputable section
variable {V : Type*} {r : ℕ} [Fintype V] (T : Trace V r)
variable {E : Finset V} {e t : ℕ} {α β M Y b : ℝ}
  (S : WidthIntegral.Selection (ordinaryLists T E) (rowDeficit T E) (rowIncidence T E) e t α β M)

/-- The elementary budgets for the same retained rows as the marked sample.
Counting first-stage sources by destination charges each one at most once. -/
theorem retained_load_budgets (prep : Prepared T) (hr : 3 ≤ r) (no : ¬Witness T.color)
    (order : Fintype.card V = r^2+1)
    (lists : ListBounds (targetGraph T.color T.target) T.row univ (live T) (range r) (qualifying T) E r) :
    let I := S.retained
    (∑ i ∈ I, rowDeficit T E i)+(∑ i ∈ I, rawSurplus T i)+(∑ i ∈ I, assigned T i) ≤ 7 ∧
      2*(∑ i ∈ I, rowDeficit T E i) ≤ 9 ∧
      (∑ i ∈ I, rowIncidence T E i) ≤ 2-firstRate T/2-(199/400:ℝ)*secondRate T := by
  intro I
  let O := ordinaryLists T E
  have inO : I ⊆ O := by dsimp only [I]; rw [S.retained_eq]; exact (filter_subset ..).trans sdiff_subset
  have covered : O ⊆ range r := fun _ h ↦ (mem_sdiff.mp (mem_sdiff.mp (mem_inter.mp h).1).1).1
  have rp : (0:ℝ)<r := by exact_mod_cast (show 0<r by omega)
  have dest (v) (hv : v ∈ T.firstSources) := (qualifying_bounds T (by omega) (prep.destinations v hv)).1
  obtain ⟨surplus,unused,cross⟩ := global_raw_budgets T (by omega) order prep.rows prep.least prep.pivots no
  have hv : 0 ≤ variance T := by unfold variance; positivity
  have pcap : firstRate T ≤ 125/61 := by
    have h := sum_le_sum (s:=range r) (fun i _ ↦ prep.paid i)
    rw [← mul_sum,assigned_total T dest] at h
    linarith only [unused,h,hv]
  have rates := pruning_rates T prep.legal (by omega)
    (cross.trans (by nlinarith only [mul_nonneg hv (sq_nonneg (r:ℝ))]))
  have nonneg (i : ℕ) (hi : i ∈ O) : 0 ≤ rowDeficit T E i := by
    have maxSize := (caps_of_no_witness T.color T.target (by omega) no).2 _
      (lists.clique i (mem_sdiff.mp (mem_sdiff.mp (mem_inter.mp hi).1).1).2)
    apply sub_nonneg.mpr
    apply (div_le_iff₀ rp).mpr
    rw [one_mul]
    exact_mod_cast maxSize
  have deficits := sum_le_sum_of_subset_of_nonneg (f:=rowDeficit T E) inO (fun i h _ ↦ nonneg i h)
  have extra : chosenExcess (live T) T.row E r ≤ 1/2 := by
    have within : E.image T.row ⊆ range r := by
      intro i hi
      obtain ⟨y,_,rfl⟩ := mem_image.mp hi
      exact mem_range.mpr (prep.rows y)
    have all := (chosen_le_surplus univ (live T) T.row (range r) (E.image T.row) r
      (subset_univ _) within).trans surplus
    unfold chosenExcess
    change ((verticesIn (live T) T.row (E.image T.row)).card:ℝ)/r-_ ≤ 1/2
    rw [card_verticesIn,Nat.cast_sum,Finset.sum_div]
    simpa [sum_sub_distrib] using all
  have budget := lists.budget
  dsimp only at budget
  rw [deleted_rate] at budget
  change (∑ i ∈ O, rowDeficit T E i)+
    (((shortRows (range r \ E.image T.row) (fun i ↦ (rowList T E i).card) (blockSize r)).card:ℝ)+
    (E.image T.row).card)/400 ≤ firstRate T+secondRate T+chosenExcess (live T) T.row E r-1/r at budget
  have posFee : (0:ℝ) ≤
    (((shortRows (range r \ E.image T.row) (fun i ↦ (rowList T E i).card) (blockSize r)).card:ℝ)+
    (E.image T.row).card)/400 := by positivity
  have sur := (sum_le_sum_of_subset_of_nonneg (f:=rawSurplus T) (inO.trans covered)
    (fun _ _ _ ↦ le_max_right ..)).trans surplus
  have assignedCap := sum_le_sum_of_subset_of_nonneg (f:=assigned T) (inO.trans covered)
    (fun _ _ _ ↦ by unfold assigned; positivity)
  rw [assigned_total T dest] at assignedCap
  have inv0 : 0 ≤ 1/(r:ℝ) := by positivity
  refine ⟨by linarith only [deficits,budget,posFee,extra,rates,pcap,sur,assignedCap,inv0],
    by linarith only [deficits,budget,posFee,extra,rates,pcap,inv0],?_⟩
  let kept := I.biUnion (rowList T E)
  have keep (x) (hx : x ∈ kept) : T.stop ≤ T.time x ∧ T.row x ∉ (∅ : Finset ℕ) := by
    obtain ⟨i,_,xc⟩ := mem_biUnion.mp hx
    simp only [rowList,available,mem_filter] at xc
    exact ⟨(mem_filter.mp xc.1).2,notMem_empty _⟩
  have zero : 2*((r:ℝ)-1)*0*r ≤ countEnds (T.forward ∅) := by
    simp [countEnds,total,Trace.forward,Trace.oversized]
  have cap := T.normalized_ordinary_bound ∅ kept prep.legal keep (by omega) (variance T) 0 cross zero
  have empty : T.earlyOversized ∅ = ∅ := by simp [Trace.earlyOversized,Trace.oversized]
  dsimp only at cap
  rw [incidence_total]
  change countEnds (T.ordinary kept)/(r:ℝ)^2 ≤ _
  simp only [empty,empty_inter,card_empty,Nat.cast_zero,zero_div,mul_zero,sub_zero,add_zero] at cap
  unfold firstRate secondRate
  linarith only [cap,hv]

/-- With f=9/40 the total number of heavy loads divided by sr is at most
Y/f+7/1120. Y is evaluated from the actual deletion rates. -/
theorem heavy_load_total (prep : Prepared T) (hr : 3 ≤ r) (no : ¬Witness T.color)
    (order : Fintype.card V = r^2+1)
    (lists : ListBounds (targetGraph T.color T.target) T.row univ (live T) (range r) (qualifying T) E r)
    (band : RetainedWidth.Band Y b α β) (p : ℝ) (rate : 100*((9/40:ℝ)/S.s) ≤ 1)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    let I := S.retained
    let G := targetGraph T.color T.target
    let C := rowList T E
    let L := lowExterior T E I S.s
    let μ := senderLaw T E I S.s p rate hp hp1
    let n := heavyLoadMean G C L S.s r μ
    let Y₀ := 2-firstRate T/2-(199/400:ℝ)*secondRate T
    (∑ i ∈ I, n i) ≤ ((Y₀/(9/40:ℝ))+7/1120)*S.s*r := by
  intro I G C L μ n Y₀
  have rp : (0:ℝ)<r := by exact_mod_cast (show 0<r by omega)
  have slo : (1120:ℝ) ≤ S.s := by exact_mod_cast S.scale_lo
  have sp : (0:ℝ)<S.s := by linarith
  let ρ := (9/40:ℝ)/S.s
  have rho : 0<ρ := by dsimp [ρ]; positivity
  have h := sum_le_sum (s:=I) fun i hi ↦ heavy_load_height T S prep hr no lists band p rate hp hp1 hi
  change (∑ i ∈ I, n i/r) ≤ ∑ i ∈ I,
    (rowDeficit T E i+rawSurplus T i+assigned T i+rowIncidence T E i/ρ) at h
  simp only [sum_add_distrib,← sum_div] at h
  obtain ⟨exc,_,inc⟩ := retained_load_budgets T S prep hr no order lists
  have inc' : (∑ i ∈ I, rowIncidence T E i)/ρ ≤ Y₀/ρ := div_le_div_of_nonneg_right inc rho.le
  have main : (∑ i ∈ I, n i)/r ≤ 7+Y₀/ρ := by linarith only [h,exc,inc']
  apply (div_le_iff₀ rp).mp
  apply main.trans
  change 7+Y₀/((9/40:ℝ)/S.s) ≤ (Y₀/(9/40)+7/1120)*S.s
  rw [div_div_eq_mul_div]
  linarith only [slo]

end
end Erdos617.ColoredLists
