import ColoringLists
import CommonWidth

/-! The common threshold on the actual clique lists of a stopped pruning trace. -/

namespace Erdos617.ColoredLists

open Finset PackingLists PruningOverlap PruningOverlap.Trace
open scoped Classical
noncomputable section

variable {V : Type*} {r : ℕ} [Fintype V] (T : Trace V r)

/-- Number of nontarget edges internal to one raw row. -/
def internalMissing (i : ℕ) : ℕ :=
  let part := (Finset.univ : Finset V).filter fun v ↦ T.row v = i
  ((targetGraph T.color T.target)ᶜ.induce (part : Set V)).edgeFinset.card

def unused (i : ℕ) : ℝ :=
  ((internalMissing T i:ℝ)-((r:ℝ)-1)*((T.rowSize i:ℝ)-r))/(r:ℝ)^2

def variance : ℝ := (∑ i ∈ range r, ((T.rowSize i:ℝ)-r)^2)/(r:ℝ)^2

def rawSurplus := surplus (univ : Finset V) T.row r

def qualifying := range r \ WidthIntegral.unqualified (range r) (rawSurplus T) (unused T)

/-- Each end is incident with the given actual vertex. Only first-stage
recorded edges are excluded, in both orientations. -/
def unrecordedDegree (x : V) : ℝ :=
  ∑ y, if T.crossGraph.Adj x y ∧ ¬T.recorded x y then (1:ℝ) else 0

def rowList (E : Finset V) (i : ℕ) := available (targetGraph T.color T.target) (live T) T.row E i

def rowIncidence (E : Finset V) (i : ℕ) : ℝ :=
  (∑ x ∈ rowList T E i, unrecordedDegree T x)/(r:ℝ)^2

def rowDeficit (E : Finset V) (i : ℕ) : ℝ := 1-((rowList T E i).card:ℝ)/r

def ordinaryLists (E : Finset V) :=
  ordinaryRows (range r \ E.image T.row) (qualifying T) (fun i ↦ (rowList T E i).card) (blockSize r)

def omittedCount (E : Finset V) :=
  (shortRows (range r \ E.image T.row) (fun i ↦ (rowList T E i).card) (blockSize r)).card +
  (E.image T.row).card

theorem incidence_total (rows : Finset ℕ) (E : Finset V) :
    ∑ i ∈ rows, rowIncidence T E i =
      countEnds (T.ordinary (rows.biUnion (rowList T E)))/(r:ℝ)^2 := by
  let K := rows.biUnion (rowList T E)
  have per (x : V) : (∑ y, if T.ordinary K x y then (1:ℝ) else 0) =
      if x ∈ K then unrecordedDegree T x else 0 := by
    by_cases hx : x ∈ K <;> simp [Trace.ordinary, hx, unrecordedDegree]
  have total_eq : countEnds (T.ordinary K) = ∑ x ∈ K, unrecordedDegree T x := by
    unfold countEnds total
    simp_rw [per]
    simp
  have dis : (rows:Set ℕ).PairwiseDisjoint (rowList T E) := by
    intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro x hi hj
    simp only [rowList,available,Finset.mem_filter] at hi hj
    exact hij (hi.2.1.symm.trans hj.2.1)
  change _ = countEnds (T.ordinary K)/(r:ℝ)^2
  simp only [rowIncidence, ← Finset.sum_div]
  rw [total_eq, Finset.sum_biUnion dis]

/-- Inputs still needed from construction of the raw partition and the
ordered first-stage stars. All costs and counts refer to the same coloring. -/
structure RawEstimates : Prop where
  sizes : ∑ i ∈ range r, rawSurplus T i ≤ 1/2
  costs : ∑ i ∈ range r, unused T i ≤ 1/2
  crossCap : (T.crossGraph.edgeFinset.card:ℝ) ≤ (1-variance T)*(r:ℝ)^2
  forward : ∀ C ⊆ range r, 2*((r:ℝ)-1)*oversizedExcess univ T.row C r*r ≤ countEnds (T.forward C)
  localCost : ∀ i ∈ range r, (61/250)*assigned T i ≤ unused T i
  firstDest : ∀ v ∈ T.firstSources, unused T (T.destination v) ≤ 1/1200

theorem pruning_rates (legal : T.Legal) (hr : 0 < r)
    (cap : (T.crossGraph.edgeFinset.card:ℝ) ≤ (r:ℝ)^2) :
    firstRate T/4+(199/400)*secondRate T ≤ 1 := by
  have pos : (0:ℝ) < r := by exact_mod_cast hr
  have h := (T.source_cost legal).trans cap
  have reduced : (T.firstSources.card:ℝ)/4+(199/400)*(T.secondSources.card:ℝ) ≤ r := by
    apply le_of_mul_le_mul_right _ pos
    nlinarith only [h]
  unfold firstRate secondRate
  rw [show (T.firstSources.card:ℝ)/r/4+(199/400)*((T.secondSources.card:ℝ)/r) =
      ((T.firstSources.card:ℝ)/4+(199/400)*T.secondSources.card)/r by ring]
  exact (div_le_one pos).2 reduced

private theorem early_eq (C : Finset ℕ) :
    verticesIn (univ \ live T) T.row (oversizedRows univ T.row C r) = T.earlyOversized C := by
  have member (i) : i ∈ oversizedRows univ T.row C r ↔
      i ∈ C ∧ 257*r < 256*T.rowSize i := Finset.mem_filter
  apply Finset.ext
  intro x
  have hl : x ∈ live T ↔ T.stop ≤ T.time x := by simp [live]
  have ho : x ∈ T.earlyOversized C ↔ T.oversized C x ∧ T.time x < T.stop := by
    simp [Trace.earlyOversized]
  rw [ho]
  unfold verticesIn
  rw [Finset.mem_filter, Finset.mem_sdiff, member, hl]
  simp only [mem_univ,true_and,not_le,Trace.oversized]
  tauto

/-- The selected lists, the actual normalized edge counts and all three
inequalities (4), including the strict fourth-power cutoff. -/
def HasWidth : Prop :=
  ∃ E : Finset V, ListBounds (targetGraph T.color T.target) T.row univ (live T)
      (range r) (qualifying T) E r ∧
    ∃ b α β, RetainedWidth.Band (2-firstRate T/2-(199/400)*secondRate T) b α β ∧
      ∃ S : WidthIntegral.Selection (ordinaryLists T E) (rowDeficit T E) (rowIncidence T E)
          (range r \ ordinaryLists T E).card (omittedCount T E) α β
          ((2:ℝ)^((144-b)/4) / ((16:ℝ)/15)^(1/4:ℝ)),
        (2:ℝ)^b*(S.s:ℝ)^4 < 15*(2:ℝ)^140 ∧ (2:ℝ)^b*(S.s:ℝ)^4 < r

/-- A legal stopped trace on the original complete graph yields either the
conjecture's witness or a common threshold for the actual surviving clique lists. -/
theorem witness_or_width (hr : 15*2^140 ≤ r) (order : Fintype.card V = r^2+1)
    (rows : ∀ v, T.row v < r) (legal : T.Legal)
    (dest : ∀ v ∈ T.firstSources, T.destination v < r) (raw : RawEstimates T)
    (stop : ∀ v ∈ live T, (Transversal.neighbors T.crossGraph (live T) v).card ≤ degreeBound r) :
    Witness T.color ∨ HasWidth T := by
  by_cases no : Witness T.color
  · exact Or.inl no
  have hr₂ : 2 ≤ r := by omega
  have pos : (0:ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hv : 0 ≤ variance T := by unfold variance; positivity
  have hrates := pruning_rates T legal (by omega)
    (raw.crossCap.trans (by nlinarith only [mul_nonneg hv (sq_nonneg (r:ℝ))]))
  have loads := assigned_total T dest
  have hp : firstRate T ≤ 125/61 := by
    have h := Finset.sum_le_sum raw.localCost
    rw [← Finset.mul_sum, loads] at h
    linarith only [h,raw.costs]
  have hd (i) (_hi : i ∈ range r) (hx : 0 < assigned T i) :
      rawSurplus T i ≤ 1/256 ∧ unused T i ≤ 1/1200 := by
    have ex : (T.firstSources.filter fun v ↦ T.destination v = i).Nonempty := by
      by_contra h
      rw [assigned, Finset.not_nonempty_iff_eq_empty.mp h] at hx
      simp at hx
    obtain ⟨v,hv⟩ := ex
    obtain ⟨hf,rfl⟩ := mem_filter.mp hv
    refine ⟨?_,raw.firstDest _ hf⟩
    have hsize := legal.destinationSmall _ (mem_filter.mp hf).2
    change max ((T.rowSize (T.destination v):ℝ)/r-1) 0 ≤ 1/256
    apply max_le _ (by norm_num)
    apply sub_le_iff_le_add.mpr
    apply (div_le_iff₀ pos).2
    have hs : (256:ℝ)*T.rowSize (T.destination v) ≤ 257*r := by exact_mod_cast hsize
    linarith only [hs]
  obtain h | ⟨E,data⟩ := witness_or_lists T (qualifying T) hr₂ order rows stop
  · exact Or.inl h
  refine Or.inr ⟨E,data,?_⟩
  let C := E.image T.row
  let O := ordinaryLists T E
  let m := fun i ↦ (rowList T E i).card
  let n := omittedCount T E
  let e₀ := (range r \ O).card
  let excess := oversizedExcess univ T.row C r
  let a := ((T.earlyOversized C).card:ℝ)/r
  let a₁ := ((T.earlyOversized C ∩ T.firstSources).card:ℝ)/r
  have hc : C ⊆ range r := by
    intro i hi
    obtain ⟨v,_,rfl⟩ := mem_image.mp hi
    exact mem_range.mpr (rows v)
  have hO (i) (hi : i ∈ O) : i ∈ range r \ C := (mem_sdiff.mp (mem_inter.mp hi).1).1
  have cover : O ⊆ range r := fun i hi ↦ (mem_sdiff.mp (hO i hi)).1
  have count : e₀+O.card = r := by simpa [e₀] using card_sdiff_add_card_eq_card cover
  have cap := (caps_of_no_witness T.color T.target hr₂ no).2
  have hx (i) (hi : i ∈ O) : 0 ≤ rowDeficit T E i := by
    apply sub_nonneg.mpr
    apply (div_le_iff₀ pos).2
    rw [one_mul]
    exact_mod_cast cap _ (data.clique i (mem_sdiff.mp (hO i hi)).2)
  have hy (i) (_hi : i ∈ O) : 0 ≤ rowIncidence T E i := by
    unfold rowIncidence unrecordedDegree
    positivity
  have hex : 0 ≤ excess := by
    apply Finset.sum_nonneg
    intro i hi
    have h : 257*r < 256*rowCard (univ:Finset V) T.row i := (mem_filter.mp hi).2
    apply sub_nonneg.mpr
    apply (le_div_iff₀ pos).2
    rw [one_mul]
    exact_mod_cast (show r ≤ rowCard (univ:Finset V) T.row i by omega)
  have keep (x) (hex : x ∈ O.biUnion (rowList T E)) : T.stop ≤ T.time x ∧ T.row x ∉ C := by
    obtain ⟨i,hi,hlist⟩ := mem_biUnion.mp hex
    simp only [rowList,available,Finset.mem_filter] at hlist
    obtain ⟨hl,he,_⟩ := hlist
    exact ⟨(mem_filter.mp hl).2,he ▸ (mem_sdiff.mp (hO i hi)).2⟩
  have incidence := T.normalized_ordinary_bound C _ legal keep (by omega) (variance T)
    excess raw.crossCap (raw.forward C hc)
  rw [← incidence_total] at incidence
  dsimp only at incidence
  have chosen := chosen_oversize_bound univ (live T) T.row E r pos (subset_univ _)
  dsimp only at chosen
  rw [early_eq T] at chosen
  have cq : (C \ oversizedRows univ T.row C r).card ≤ C.card := card_le_card sdiff_subset
  have deficit := data.budget
  dsimp only at deficit
  rw [deleted_rate] at deficit
  have hd' : (∑ i ∈ O, rowDeficit T E i)+(n:ℝ)/400 ≤
      firstRate T + secondRate T + excess - a + (C.card:ℝ)/256 := by
    change PackingLists.deficit O m r + _ ≤ _
    change PackingLists.deficit O m r+(((shortRows (range r \ C) m (blockSize r)).card+C.card:ℕ):ℝ)/400 ≤ _
    rw [Nat.cast_add]
    change chosenExcess (live T) T.row E r ≤ excess-a+((C \ _).card:ℝ)/256 at chosen
    change PackingLists.deficit O m r+(((shortRows (range r \ C) m (blockSize r)).card:ℝ)+C.card)/400 ≤ _ at deficit
    have cq' : ((C \ oversizedRows univ T.row C r).card:ℝ) ≤ C.card := by exact_mod_cast cq
    linarith only [deficit,chosen,cq',div_nonneg zero_le_one pos.le]
  have hq : (C.card:ℝ) ≤ (n:ℝ)/2 := by
    have h := data.pairs_le_short
    change C.card ≤ (shortRows (range r \ C) m (blockSize r)).card at h
    change (C.card:ℝ) ≤ (((shortRows (range r \ C) m (blockSize r)).card+C.card:ℕ):ℝ)/2
    push_cast
    exact (le_div_iff₀ (by norm_num)).2 (by exact_mod_cast (show C.card*2 ≤ _ by omega))
  have hn : n ≤ 1411 := data.count_le pos (subset_univ _) (fun v _ ↦ mem_range.mpr (rows v))
    cap raw.sizes (deleted_rate T) hp hrates
  exact WidthIntegral.width_from_row_counts (range r) (rawSurplus T) (unused T) (assigned T) O
    (rowDeficit T E) (rowIncidence T E) e₀ n r (p := firstRate T) (t := secondRate T)
    (O := excess) (a := a) (v := variance T) (a₁ := a₁) (q := C.card)
    (by unfold firstRate; positivity) hp (by unfold secondRate; positivity) hrates hn hr count
    (fun _ _ ↦ le_max_right ..) (fun _ _ ↦ by unfold assigned; positivity)
    raw.sizes raw.costs loads raw.localCost hd (omitted_ordinary ..) hx hy hex
    (by dsimp [a]; positivity) hv (by dsimp [a₁]; positivity) hq incidence hd'

end
end Erdos617.ColoredLists
