import ColoringEnlargement
import SenderPayment

/-! Strict exterior shortage at the working cutoff, on the actual selected ordinary rows. -/

namespace Erdos617.ColoredLists

open Finset PruningOverlap PackingLists
open scoped Classical
noncomputable section
variable {V : Type*} {r : ℕ} [Fintype V] (T : Trace V r)

/-- The priced arrivals cannot be realized in either of the two possible
arenas of enlarged rows. Both the joint deficit bound and the degree of each
arrival are taken on the original vertices of the selected rows. -/
theorem excludes_enlarged_rows (prep : Prepared T) (hr : 2^20 ≤ r) (no : ¬Witness T.color)
    {E : Finset V} {e n : ℕ} {α β M Y b : ℝ}
    (S : WidthIntegral.Selection (ordinaryLists T E) (rowDeficit T E) (rowIncidence T E)
      e n α β M) (band : RetainedWidth.Band Y b α β) (scale : (2:ℝ)^b*(S.s:ℝ)^4 < r) :
    ¬HasEnlargedRows T E S.retained S.s := by
  rintro ⟨B,_,_,offset,row,part,A,survive,arena,ordinary,which,bounds,extendRows,enlarged⟩
  let parts := (range (S.s-1)).disjSum ordinary
  let C := attachmentRow T E A row
  let large := attachmentLarge T E A row
  have ai : parts.toLeft ⊆ range (S.s-1) := by simp only [parts,toLeft_disjSum,Subset.rfl]
  have oi : parts.toRight ⊆ S.retained := by
    change ((range (S.s-1)).disjSum ordinary).toRight ⊆ S.retained
    rw [toRight_disjSum]
    rcases which with ⟨_,_,eq⟩|⟨_,_,eq⟩
    · rw [eq]; exact empty_subset _
    · rw [eq]
  apply priced_arena_impossible T.color T.target arena parts C large hr no bounds extendRows enlarged
  · intro J sub few
    exact tagged_deficit_cap T prep S band scale offset.1 part survive ai oi J sub few
      (fun k ↦ (C k).card) (fun _ _ ↦ le_rfl)
  · exact fun _ _ ↦ Iff.rfl

/-- For any coloring of the required order and any integer at the working
cutoff, either a color is missed on r+1 vertices, or the actual common width
has all three bounds and its exterior shortage strictly exceeds 3r/20. -/
theorem witness_or_exterior_shortage (color : {e : Sym2 V // ¬e.IsDiag} → Fin r)
    (hr : 255*2^136 ≤ r) (order : Fintype.card V = r^2+1) :
    Witness color ∨ ∃ T : Trace V r, T.color = color ∧ Prepared T ∧
      ∃ E : Finset V, ListBounds (targetGraph T.color T.target) T.row univ (live T)
        (range r) (qualifying T) E r ∧
      ∃ b α β, RetainedWidth.Band (2-firstRate T/2-(199/400)*secondRate T) b α β ∧
      ∃ S : WidthIntegral.Selection (ordinaryLists T E) (rowDeficit T E) (rowIncidence T E)
          (range r \ ordinaryLists T E).card (omittedCount T E) α β
          ((2:ℝ)^((144-b)/4) / ((256:ℝ)/255)^(1/4:ℝ)),
        (2:ℝ)^b*(S.s:ℝ)^4 < 255*(2:ℝ)^136 ∧ (2:ℝ)^b*(S.s:ℝ)^4 < r ∧
        (3/20:ℝ)*r < ((S.s-1:ℕ):ℝ)*r-((lowExterior T E S.retained S.s).card:ℝ) := by
  by_cases yes : Witness color
  · exact Or.inl yes
  obtain ⟨T,eq,prep,E,lists,b,α,β,band,S,cut,scale,alt⟩ :=
    (witness_or_shortage_or_enlargement color hr order).resolve_left yes
  exact Or.inr ⟨T,eq,prep,E,lists,b,α,β,band,S,cut,scale,alt.resolve_right
    (excludes_enlarged_rows T prep (by omega) (eq ▸ yes) S band scale)⟩

end
end Erdos617.ColoredLists
