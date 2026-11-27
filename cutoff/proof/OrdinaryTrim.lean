import ColoringWidth

/-! The temporary ordinary rows used in the exterior argument, Appendix A §4. -/

namespace Erdos617.ColoredLists

open Finset PackingLists RowExtraction PruningOverlap
open scoped Classical
noncomputable section

variable {V : Type*} {r : ℕ} [Fintype V] (T : Trace V r)

/-- Keep precisely the vertices whose unrecorded foreign degree is at most r/8. -/
def temporaryRow (E : Finset V) (i : ℕ) :=
  (rowList T E i).filter fun x ↦ unrecordedDegree T x ≤ (r:ℝ)/8

/-- Trimming an ordinary list preserves its clique in the original target graph. -/
theorem temporary_row_isClique {E : Finset V}
    (lists : ListBounds (targetGraph T.color T.target) T.row univ (live T) (range r) (qualifying T) E r)
    {i : ℕ} (ordinary : i ∈ ordinaryLists T E) :
    (targetGraph T.color T.target).IsClique (temporaryRow T E i : Set V) := by
  have unused := (mem_sdiff.mp (mem_sdiff.mp (mem_inter.mp ordinary).1).1).2
  exact (lists.clique i unused).subset (Finset.coe_subset.mpr (filter_subset ..))

/-- Target neighbors in the entire graph outside the original ordinary clique. -/
def outsideClique (E : Finset V) (i : ℕ) (x : V) :=
  univ.filter fun y ↦ (targetGraph T.color T.target).Adj x y ∧ y ∉ rowList T E i

/-- Every vertex removed from the row costs at least r/8 of its actual
unrecorded incidences. The degree and the row sum refer to the same coloring. -/
theorem trim_cost (E : Finset V) (i : ℕ) :
    ((rowList T E i \ temporaryRow T E i).card:ℝ)*(r:ℝ)/8 ≤
      (∑ x ∈ rowList T E i, unrecordedDegree T x) := by
  let D := rowList T E i \ temporaryRow T E i
  have hi (x) (hx : x ∈ D) : (r:ℝ)/8 ≤ unrecordedDegree T x := by
    obtain ⟨inL,out⟩ := mem_sdiff.mp hx
    exact le_of_lt (lt_of_not_ge (fun h ↦ out (mem_filter.mpr ⟨inL,h⟩)))
  have lower := Finset.sum_le_sum hi
  calc _ = ∑ _x ∈ D, (r:ℝ)/8 := by simp [D]; ring
       _ ≤ ∑ x ∈ D, unrecordedDegree T x := lower
       _ ≤ _ := sum_le_sum_of_subset_of_nonneg sdiff_subset (fun x _ _ ↦ by unfold unrecordedDegree; positivity)

private theorem row_subset (E : Finset V) (i : ℕ) :
    rowList T E i ⊆ fiber univ T.row i := by
  intro x hx
  simp only [rowList, available, Finset.mem_filter] at hx
  exact mem_filter.mpr ⟨mem_univ x,hx.2.1⟩

/-- A recorded edge incident with a surviving vertex must come from a
first-stage source assigned to its row. All other outside neighbors are
unrecorded cross edges or points in the raw row outside the original list. -/
theorem outsideClique_count (E : Finset V) (i : ℕ) {x : V} (hx : x ∈ rowList T E i) :
    ((outsideClique T E i x).card:ℝ) ≤ unrecordedDegree T x +
      (T.firstSources.filter fun y ↦ T.destination y = i).card + ((T.rowSize i:ℝ)-(rowList T E i).card) := by
  let U := univ.filter fun y ↦ T.crossGraph.Adj x y ∧ ¬T.recorded x y
  let B := T.firstSources.filter fun y ↦ T.destination y = i
  let L := rowList T E i
  let A := fiber univ T.row i
  have hlist := hx
  simp only [rowList,available,Finset.mem_filter] at hlist
  have htime : T.stop ≤ T.time x := (mem_filter.mp hlist.1).2
  have hrow : T.row x = i := hlist.2.1
  have cover : outsideClique T E i x ⊆ (U ∪ B) ∪ (A \ L) := by
    intro y hy
    obtain ⟨_,adj,out⟩ := mem_filter.mp hy
    by_cases same : T.row y = i
    · exact mem_union_right _ (mem_sdiff.mpr ⟨mem_filter.mpr ⟨mem_univ _,same⟩,out⟩)
    apply mem_union_left
    have foreign : T.crossGraph.Adj x y := by
      rw [← cross_target T]
      exact ⟨fun he ↦ same (he.symm.trans hrow),adj⟩
    by_cases rec : T.recorded x y
    · obtain ⟨before,_⟩ | ⟨before,star⟩ := rec
      · exact ((not_lt.mpr (T.stages.trans htime)) before).elim
      · have dest := (mem_filter.mp star).2.2.2.2 before
        exact mem_union_right _ (mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,before⟩,dest.symm.trans hrow⟩)
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _,foreign,rec⟩)
  have hn := (card_le_card cover).trans
    ((card_union_le ..).trans (Nat.add_le_add_right (card_union_le U B) _))
  have u : (U.card:ℝ) = unrecordedDegree T x := by simp [U,unrecordedDegree]
  have own : ((A \ L).card:ℝ)+(L.card:ℝ) = (T.rowSize i:ℝ) := by
    exact_mod_cast card_sdiff_add_card_eq_card (row_subset T E i)
  have bound : ((outsideClique T E i x).card:ℝ) ≤ (U.card:ℝ)+B.card+(A \ L).card := by exact_mod_cast hn
  rw [u] at bound
  change _ ≤ _+(B.card:ℝ)+((T.rowSize i:ℝ)-(L.card:ℝ))
  linarith only [own,bound]

/-- Each temporarily trimmed retained clique contains at least 255r/256
vertices. Each such vertex has fewer than 7r/50 neighbors of the target
color outside its original clique, counting all r²+1 vertices. -/
theorem temporary_row_bounds (prep : Prepared T) (hr : 0 < r) (E : Finset V)
    {Y b α β scale : ℝ} {e₀ n : ℕ} (band : RetainedWidth.Band Y b α β)
    (S : WidthIntegral.Selection (ordinaryLists T E) (rowDeficit T E) (rowIncidence T E) e₀ n α β scale)
    {i : ℕ} (retained : i ∈ S.retained) :
    (255/256:ℝ)*r ≤ (temporaryRow T E i).card ∧
      ∀ x ∈ temporaryRow T E i, ((outsideClique T E i x).card:ℝ) < (7/50:ℝ)*r := by
  have pos : (0:ℝ) < r := by exact_mod_cast hr
  have hα : α ≤ 656/4000 := by cases band <;> norm_num
  have hβ : β ≤ 925/4000 := by cases band <;> norm_num
  have hs : (1120:ℝ) ≤ S.s := by exact_mod_cast S.scale_lo
  have a (z w : ℝ) (hw : 0 ≤ w) (hz : (S.s:ℝ)*z ≤ w) : z ≤ w/1120 := by
    by_cases h : 0 ≤ z
    · linarith only [mul_le_mul_of_nonneg_right hs h,hz]
    · linarith only [le_of_not_ge h,hw]
  have xbound : rowDeficit T E i ≤ (2*925/4000)/1120 := by
    apply a _ _ (by norm_num)
    have paid := S.deficit i retained
    have hb : 0 ≤ β := by cases band <;> norm_num
    nlinarith only [paid,hβ,mul_le_mul_of_nonneg_left S.width_lt.le hb]
  have ybound : rowIncidence T E i ≤ (656/4000)/1120 := by
    apply a _ _ (by norm_num)
    have ha : 0 ≤ α := by cases band <;> norm_num
    linarith only [S.incidence i retained, mul_le_mul_of_nonneg_left S.width_lt.le ha,hα]
  let C := rowList T E i
  let K := temporaryRow T E i
  have hK : K ⊆ C := filter_subset ..
  have count : ((C \ K).card:ℝ)+K.card = (C.card:ℝ) := by
    exact_mod_cast card_sdiff_add_card_eq_card hK
  have short : (r:ℝ) - (C.card:ℝ) ≤ ((2*925/4000)/1120)*r := by
    have scaled := mul_le_mul_of_nonneg_right xbound pos.le
    change (1-(C.card:ℝ)/r)*r ≤ _ at scaled
    rwa [sub_mul,div_mul_cancel₀ _ pos.ne',one_mul] at scaled
  have upper := (div_le_iff₀ (sq_pos_of_pos pos)).mp ybound
  have loss : ((C \ K).card:ℝ) ≤ (8*(656/4000)/1120)*r := by
    apply le_of_mul_le_mul_right _ pos
    have cuts := trim_cost T E i
    change ((C \ K).card:ℝ)*r/8 ≤ _ at cuts
    linarith only [cuts,upper]
  refine ⟨by linarith only [short,count,loss,pos],?_⟩
  have ordinary : i ∈ ordinaryLists T E := by
    rw [S.retained_eq] at retained
    exact (mem_sdiff.mp (mem_filter.mp retained).1).1
  have qual : i ∈ qualifying T := (mem_inter.mp ordinary).2
  have rawSize : (256:ℝ)*T.rowSize i ≤ 257*r := by exact_mod_cast (qualifying_bounds T hr qual).2.1
  have assignedCount := (div_le_iff₀ pos).mp (prep.source_cap i)
  intro x hx
  obtain ⟨inside,small⟩ := mem_filter.mp hx
  have neighbors := outsideClique_count T E i inside
  change _ ≤ _ + _ + ((T.rowSize i:ℝ)-(C.card:ℝ)) at neighbors
  linarith only [neighbors,small,rawSize,assignedCount,short,pos]

end
end Erdos617.ColoredLists
