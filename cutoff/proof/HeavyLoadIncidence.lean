import RecoveredTest

/-! Direct exterior loads and foreign representative loads use disjoint
sets of neighbors of the receiving clique. -/

namespace Erdos617.ColoredLists

open Finset PruningOverlap PackingLists
open scoped Classical
noncomputable section

variable {V : Type*} {r : ℕ} [Fintype V] (T : Trace V r)

/-- The exterior of the selected cliques, before marking. -/
def loadOutside (E : Finset V) (I : Finset ℕ) := univ \ I.biUnion (rowList T E)

/-- A direct load in its own raw row or from a source recorded at this row
can be exceptional. The first-stage source has a single destination. -/
def loadExceptions (E : Finset V) (i : ℕ) :=
  ((univ.filter (fun y ↦ T.row y = i)) \ rowList T E i) ∪
    T.firstSources.filter (fun y ↦ T.destination y = i)

private theorem list_info {E : Finset V} {i : ℕ} {x : V} (hx : x ∈ rowList T E i) :
    x ∈ live T ∧ T.row x = i := by
  simp only [rowList,available,mem_filter] at hx
  exact ⟨hx.1,hx.2.1⟩

private theorem no_record {x y : V} (liveX : x ∈ live T)
    (outside : ¬(y ∈ T.firstSources ∧ T.row x = T.destination y)) :
    ¬T.recorded x y := by
  rintro (⟨f,_⟩|⟨f,star⟩)
  · exact (not_lt.mpr (T.stages.trans (mem_filter.mp liveX).2)) f
  · exact outside ⟨mem_filter.mpr ⟨mem_univ _,f⟩,(mem_filter.mp star).2.2.2.2 f⟩

omit [Fintype V] in
private theorem cut_degree_sum (G : SimpleGraph V) (C D : Finset V) :
    ((RepresentativeCut.cut G C D).card:ℝ) = ∑ y ∈ D, SameRowConflicts.degree G C y := by
  unfold RepresentativeCut.cut SameRowConflicts.degree
  simp only [card_filter,Nat.cast_sum,sum_product]
  rw [sum_comm]
  apply sum_congr rfl
  intro y _
  apply sum_congr rfl
  intro x _
  rw [G.adj_comm x y]

/-- The direct and foreign-edge counts together fit one original incidence
budget. Every edge is charged at its endpoint in the receiving clique. -/
theorem disjoint_load_incidence (E : Finset V) (I : Finset ℕ) {i : ℕ} (hi : i ∈ I) :
    let G := targetGraph T.color T.target
    let C := rowList T E
    let A := loadOutside T E I \ loadExceptions T E i
    (∑ y ∈ A, SameRowConflicts.degree G (C i) y) +
      (∑ k ∈ I.erase i, ((RepresentativeCut.cut G (C i) (C k)).card:ℝ)) ≤
      ∑ x ∈ C i, unrecordedDegree T x := by
  intro G C A
  let F := (I.erase i).biUnion C
  let D := A ∪ F
  have apart : ((I.erase i):Set ℕ).PairwiseDisjoint C := fun _ _ _ _ ne ↦
    disjoint_left.mpr fun _ ha hb ↦ ne ((list_info T ha).2.symm.trans (list_info T hb).2)
  have dis : Disjoint A F := by
    apply disjoint_left.mpr
    intro y hy hf
    obtain ⟨k,hk,hyk⟩ := mem_biUnion.mp hf
    exact (mem_sdiff.mp (mem_sdiff.mp hy).1).2 (mem_biUnion.mpr ⟨k,(mem_erase.mp hk).2,hyk⟩)
  have classify {x y : V} (hx : x ∈ C i) (hy : y ∈ D) (edge : G.Adj y x) :
      T.crossGraph.Adj x y ∧ ¬T.recorded x y := by
    obtain ⟨xl,xi⟩ := list_info T hx
    have unsupported (different : T.row y ≠ i)
        (unrecorded : ¬(y ∈ T.firstSources ∧ T.row x = T.destination y)) :
        T.crossGraph.Adj x y ∧ ¬T.recorded x y := by
      refine ⟨?_,no_record T xl unrecorded⟩
      rw [← cross_target]
      exact ⟨fun e ↦ different (e.symm.trans xi),G.adj_symm edge⟩
    rcases mem_union.mp hy with h|h
    · obtain ⟨out,ex⟩ := mem_sdiff.mp h
      have nc : y ∉ C i := fun yc ↦ (mem_sdiff.mp out).2 (mem_biUnion.mpr ⟨i,hi,yc⟩)
      apply unsupported
      · exact fun yrow ↦ ex (mem_union_left _ (mem_sdiff.mpr ⟨mem_filter.mpr ⟨mem_univ _,yrow⟩,nc⟩))
      · exact fun ⟨first,dst⟩ ↦ ex (mem_union_right _ (mem_filter.mpr ⟨first,dst.symm.trans xi⟩))
    · obtain ⟨k,hk,member⟩ := mem_biUnion.mp h
      obtain ⟨yl,yk⟩ := list_info T member
      exact unsupported (fun e ↦ (mem_erase.mp hk).1 (yk.symm.trans e))
        (fun ⟨first,_⟩ ↦ (not_lt.mpr (T.stages.trans (mem_filter.mp yl).2)) (mem_filter.mp first).2)
  simp_rw [cut_degree_sum]
  rw [← sum_biUnion apart,← sum_union dis]
  change (∑ y ∈ D, (((C i).filter (G.Adj y)).card:ℝ)) ≤ _
  simp only [card_filter,Nat.cast_sum]
  rw [sum_comm]
  apply sum_le_sum
  intro x hx
  unfold unrecordedDegree
  apply le_trans _ (sum_le_univ_sum_of_nonneg (fun y ↦ by split <;> norm_num) (s:=D))
  apply sum_le_sum
  intro y hy
  by_cases adj : G.Adj y x
  · simp [adj,classify hx hy adj]
  · simp [adj]
    split <;> norm_num

/-- Exceptions are paid by the actual difference in raw and retained row
sizes plus the count of sources whose unique destination is i. -/
theorem load_exceptions_card (E : Finset V) (i : ℕ) :
    ((loadExceptions T E i).card:ℝ) ≤ (T.rowSize i:ℝ)-(rowList T E i).card+
      ((T.firstSources.filter (fun y ↦ T.destination y = i)).card:ℝ) := by
  let R := univ.filter fun y ↦ T.row y=i
  have sub : rowList T E i ⊆ R := fun _ hx ↦ mem_filter.mpr ⟨mem_univ _,(list_info T hx).2⟩
  have h : ((R \ rowList T E i).card:ℝ)+(rowList T E i).card = (T.rowSize i:ℝ) := by
    exact_mod_cast card_sdiff_add_card_eq_card sub
  have bound := card_union_le (R \ rowList T E i) (T.firstSources.filter fun y ↦ T.destination y=i)
  have bound' : ((loadExceptions T E i).card:ℝ) ≤ ((R \ rowList T E i).card:ℝ)+
      ((T.firstSources.filter fun y ↦ T.destination y=i).card:ℝ) := by exact_mod_cast bound
  linarith only [bound',h]

end
end Erdos617.ColoredLists
