import ColoredAttachment

/-! From the original coloring to the enlarged rows used by the exterior shortage argument. -/

namespace Erdos617.ColoredLists

open Finset PruningOverlap PackingLists UniqueAttachment
open scoped Classical
noncomputable section
variable {V : Type*} {r : ℕ} [Fintype V] (T : Trace V r)

/-- The auxiliary vertices, surviving and enlarged cliques all use the same
edge labels as the given trace. The order of B decides which arena to count. -/
def HasEnlargedRows (E : Finset V) (retained : Finset ℕ) (s : ℕ) : Prop :=
  ∃ B ⊆ lowExterior T E retained s,
    B.card = min (lowExterior T E retained s).card ((s-1)*r+1) ∧
    (-(3/20:ℝ)*r ≤ (B.card:ℝ)-((s-1:ℕ):ℝ)*r ∧ (B.card:ℝ)-((s-1:ℕ):ℝ)*r ≤ 1) ∧
    ∃ row : B → ℕ, AuxiliaryPartition T s B row ∧ ∃ A : Finset B,
      AuxiliarySurvivors (targetGraph (inducedColor T.color B) T.target) row (s-1) r A ∧
      ∃ (arena : Finset V) (ordRows : Finset ℕ),
        ((B.card = (s-1)*r+1 ∧ arena = B ∧ ordRows = ∅) ∨
          (B.card ≠ (s-1)*r+1 ∧ arena = univ ∧ ordRows = retained)) ∧
        let parts := (range (s-1)).disjSum ordRows
        let C := attachmentRow T E A row
        let large := attachmentLarge T E A row
        ArenaBounds (targetGraph T.color T.target) arena parts C r ∧
          CanExtend (targetGraph T.color T.target) arena parts C large ∧
          EnlargedRows (targetGraph T.color T.target) arena parts C large r

/-- Failure of the strict shortage forces clique enlargement in the correct
arena. In particular every remaining exterior point has two large rows and
the integer deficits sum to its exterior population minus one. -/
theorem enlarged_of_failed_shortage (prep : Prepared T) (hr : 2 ≤ r) (no : ¬Witness T.color)
    (order : Fintype.card V = r^2+1) {E : Finset V} {e n : ℕ} {α β M Y b : ℝ}
    (S : WidthIntegral.Selection (ordinaryLists T E) (rowDeficit T E) (rowIncidence T E)
      e n α β M) (band : RetainedWidth.Band Y b α β) (scale : (2:ℝ)^b*(S.s:ℝ)^4 < r)
    (slots : e+(ordinaryLists T E).card = r)
    (lists : ListBounds (targetGraph T.color T.target) T.row univ (live T) (range r) (qualifying T) E r)
    (fail : ((S.s-1:ℕ):ℝ)*r-((lowExterior T E S.retained S.s).card:ℝ) ≤ (3/20:ℝ)*r) :
    HasEnlargedRows T E S.retained S.s := by
  obtain ⟨B,sub,count,offset,_,row,part,A,live⟩ :=
    auxiliary_cliques_of_failed_shortage T S hr no band scale slots fail
  refine ⟨B,sub,count,offset,row,part,A,live,?_⟩
  by_cases full : B.card = (S.s-1)*r+1
  · have bounds := auxiliary_arena_bounds T S hr no band slots sub full A row live
    have ext := actual_can_extend T prep (by omega) S band sub row part A live B
      ((range (S.s-1)).disjSum ∅) (by rw [toLeft_disjSum]) (by rw [toRight_disjSum]; exact empty_subset _)
    exact ⟨B,∅,Or.inl ⟨full,rfl,rfl⟩,bounds,ext,bounds.enlarge ext⟩
  · have bounds := full_arena_bounds T S hr no order slots lists sub A row live
    have ext := actual_can_extend T prep (by omega) S band sub row part A live univ
      ((range (S.s-1)).disjSum S.retained) (by simp) (by simp)
    exact ⟨univ,S.retained,Or.inr ⟨full,rfl,rfl⟩,bounds,ext,bounds.enlarge ext⟩

/-- The prescribed extension and enlargement conclusion with no external graph
hypotheses at the working cutoff. The last alternative is the one that the
pricing and capacity argument must exclude to establish the shortage. -/
theorem witness_or_shortage_or_enlargement (color : {e : Sym2 V // ¬e.IsDiag} → Fin r)
    (hr : 255*2^136 ≤ r) (order : Fintype.card V = r^2+1) :
    Witness color ∨ ∃ T : Trace V r, T.color = color ∧ Prepared T ∧
      ∃ E : Finset V, ListBounds (targetGraph T.color T.target) T.row univ (live T)
        (range r) (qualifying T) E r ∧
      ∃ b α β, RetainedWidth.Band (2-firstRate T/2-(199/400)*secondRate T) b α β ∧
      ∃ S : WidthIntegral.Selection (ordinaryLists T E) (rowDeficit T E) (rowIncidence T E)
          (range r \ ordinaryLists T E).card (omittedCount T E) α β
          ((2:ℝ)^((144-b)/4) / ((256:ℝ)/255)^(1/4:ℝ)),
        (2:ℝ)^b*(S.s:ℝ)^4 < 255*(2:ℝ)^136 ∧ (2:ℝ)^b*(S.s:ℝ)^4 < r ∧
        ((3/20:ℝ)*r < ((S.s-1:ℕ):ℝ)*r-((lowExterior T E S.retained S.s).card:ℝ) ∨
          HasEnlargedRows T E S.retained S.s) := by
  by_cases yes : Witness color
  · exact Or.inl yes
  obtain ⟨T,eq,prep⟩ := (witness_or_prepared color hr order).resolve_left yes
  obtain ⟨E,lists,b,α,β,band,S,cut,scale⟩ := prep.width
  refine Or.inr ⟨T,eq,prep,E,lists,b,α,β,band,S,cut,scale,?_⟩
  by_cases short : (3/20:ℝ)*r < ((S.s-1:ℕ):ℝ)*r-((lowExterior T E S.retained S.s).card:ℝ)
  · exact Or.inl short
  have incl : ordinaryLists T E ⊆ range r := by
    intro i hi
    exact (mem_sdiff.mp (mem_sdiff.mp (mem_inter.mp hi).1).1).1
  have slots := card_sdiff_add_card_eq_card incl
  rw [card_range] at slots
  exact Or.inr (enlarged_of_failed_shortage T prep (by omega) (eq ▸ yes) order S band scale slots lists
    (le_of_not_gt short))

end
end Erdos617.ColoredLists
