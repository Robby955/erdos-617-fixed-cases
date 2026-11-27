import ColoringWidth
import AuxiliaryColoring
import AuxiliaryMoments
import AuxiliaryDeficit
import OrdinaryTrim

/-! From an arbitrary coloring to the signed and normalized auxiliary budgets of Appendix A, §4. -/

namespace Erdos617.ColoredLists

open Finset RowExtraction PackingLists PruningOverlap GraphPartitionCount AuxiliaryMoments
open scoped Classical
noncomputable section
variable {V : Type*} {r : ℕ} [Fintype V] (T : Trace V r)

/-- Data of the h auxiliary rows, with all bounds referring to the edges
and row sizes of the same induced graph on B. The raw order is hr+b. -/
structure AuxiliaryPartition (s : ℕ) (B : Finset V) (row : B → ℕ) : Prop where
  labels : ∀ x, row x < s-1
  pivots : ∀ i < s-1, RowStep (targetGraph (inducedColor T.color B) T.target)ᶜ
    (fiber univ row i) (laterRows univ row i)
  signed :
    let h := s-1
    let b := (B.card:ℝ)-(h:ℝ)*r
    let G := targetGraph (inducedColor T.color B) T.target
    ((cross G row).edgeFinset.card:ℝ) + (∑ i ∈ range h, ((size row i:ℝ)-r)^2) ≤
      (r:ℝ)*h*(h-1)+b^2+min (2*((h:ℝ)-1)*b) (2*((h:ℝ)-r)*b)
  normalized :
    let G := targetGraph (inducedColor T.color B) T.target
    ((cross G row).edgeFinset.card:ℝ)/(r:ℝ)^2 +
      (∑ i ∈ range (s-1), (max (1-(size row i:ℝ)/r) 0)^2) ≤ (3/20:ℝ)^2+1/2^20
  linear :
    let h := s-1
    let b := (B.card:ℝ)-(h:ℝ)*r
    let G := targetGraph (inducedColor T.color B) T.target
    (∑ i ∈ range h, max ((r:ℝ)-size row i) 0) ≤
      -b+((cross G row).edgeFinset.card:ℝ)/(2*((r:ℝ)-1))

/-- The set of exterior low-attachment vertices and its auxiliary subset,
kept with the original row selection. -/
def HasAuxiliary (E : Finset V) (parts : Finset ℕ) (s : ℕ) : Prop :=
  ∃ B ⊆ lowExterior T E parts s,
    B.card = min (lowExterior T E parts s).card ((s-1)*r+1) ∧
    (-(3/20:ℝ)*r ≤ (B.card:ℝ)-((s-1:ℕ):ℝ)*r ∧ (B.card:ℝ)-((s-1:ℕ):ℝ)*r ≤ 1) ∧
    ¬Witness (inducedColor T.color B) ∧ ∃ row, AuxiliaryPartition T s B row

/-- Failure of the exterior shortage yields h auxiliary rows on actual
vertices, with the signed edge estimate and the normalized square bound. -/
theorem auxiliary_of_failed_shortage {E : Finset V} {rows : Finset ℕ} {e n : ℕ}
    {α β M Y exp : ℝ}
    (S : WidthIntegral.Selection rows (rowDeficit T E) (rowIncidence T E) e n α β M)
    (hr : 2 ≤ r) (no : ¬Witness T.color) (band : RetainedWidth.Band Y exp α β)
    (scale : (2:ℝ)^exp*(S.s:ℝ)^4 < r) (slots : e+rows.card = r)
    (fail : ((S.s-1:ℕ):ℝ)*r-((lowExterior T E S.retained S.s).card:ℝ) ≤ (3/20:ℝ)*r) :
    HasAuxiliary T E S.retained S.s := by
  obtain ⟨B,sub,count,bounds,noB,cap⟩ := exists_auxiliary_coloring T S hr no band slots fail
  let h := S.s-1
  let b := (B.card:ℝ)-(h:ℝ)*r
  let color := inducedColor T.color B
  let G := targetGraph color T.target
  obtain ⟨row,labels,pivots⟩ := exists_ordered_rows Gᶜ h univ
    (fun A _ cl ↦ cap A (by simpa using cl))
  have inside (x : B) := labels x (mem_univ _)
  have order : (Fintype.card B:ℝ) = h*r+b := by simp [b]
  have signed := auxiliary_square_budget color T.target h b order
    (fun k _ ↦ (caps_of_no_witness color k hr noB).1) row inside pivots
  have linear := auxiliary_deficit color T.target row h b hr noB order inside pivots
  exact ⟨B,sub,count,bounds,noB,row,inside,pivots,signed,
    auxiliary_normalized G row band S.scale_lo scale bounds.1 bounds.2 signed,linear⟩

/-- The actual width selection either gives the required shortage or supplies
the induced auxiliary graph with its moment estimates. -/
def ExteriorAlternative : Prop :=
  ∃ E : Finset V, ListBounds (targetGraph T.color T.target) T.row univ (live T)
      (range r) (qualifying T) E r ∧
    ∃ exp α β, RetainedWidth.Band (2-firstRate T/2-(199/400)*secondRate T) exp α β ∧
      ∃ S : WidthIntegral.Selection (ordinaryLists T E) (rowDeficit T E) (rowIncidence T E)
          (range r \ ordinaryLists T E).card (omittedCount T E) α β
          ((2:ℝ)^((144-exp)/4) / ((16:ℝ)/15)^(1/4:ℝ)),
        (2:ℝ)^exp*(S.s:ℝ)^4 < 15*(2:ℝ)^140 ∧ (2:ℝ)^exp*(S.s:ℝ)^4 < r ∧
        (∀ i ∈ S.retained, (255/256:ℝ)*r ≤ (temporaryRow T E i).card ∧
          ∀ x ∈ temporaryRow T E i, ((outsideClique T E i x).card:ℝ) < (7/50:ℝ)*r) ∧
        ((3/20:ℝ)*r < ((S.s-1:ℕ):ℝ)*r-((lowExterior T E S.retained S.s).card:ℝ) ∨
          HasAuxiliary T E S.retained S.s)

/-- The arbitrary-coloring entry point retains the pruning history, selected
cliques and all auxiliary edge and square estimates under failed shortage. -/
theorem witness_or_exterior_auxiliary (color : {e : Sym2 V // ¬e.IsDiag} → Fin r)
    (hr : 15*2^140 ≤ r) (order : Fintype.card V = r^2+1) :
    Witness color ∨ ∃ T : Trace V r, T.color = color ∧ Prepared T ∧ ExteriorAlternative T := by
  by_cases yes : Witness color
  · exact Or.inl yes
  obtain ⟨T,eq,prepared⟩ := (witness_or_prepared color hr order).resolve_left yes
  obtain ⟨E,lists,exp,α,β,band,S,below,scale⟩ := prepared.width
  refine Or.inr ⟨T,eq,prepared,E,lists,exp,α,β,band,S,below,scale,fun _ hi ↦ temporary_row_bounds T prepared.cutInputs (by omega) E band S hi,?_⟩
  by_cases short : (3/20:ℝ)*r < ((S.s-1:ℕ):ℝ)*r-((lowExterior T E S.retained S.s).card:ℝ)
  · exact Or.inl short
  have ordinary : ordinaryLists T E ⊆ range r := by
    intro i hi
    exact (mem_sdiff.mp (mem_sdiff.mp (mem_inter.mp hi).1).1).1
  have slots := card_sdiff_add_card_eq_card ordinary
  rw [card_range] at slots
  exact Or.inr (auxiliary_of_failed_shortage T S (by omega) (eq ▸ yes) band scale slots
    (le_of_not_gt short))

end
end Erdos617.ColoredLists
