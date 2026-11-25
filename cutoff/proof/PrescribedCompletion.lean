import ColoredAuxiliaryExtension
import OrdinaryExtension

/-! Completing prescribed independent sets on the original vertices in Appendix A §4. -/

namespace Erdos617.ColoredLists

open Finset PruningOverlap Transversal
open scoped Classical
noncomputable section

/-- The original vertices of the requested surviving auxiliary rows. -/
def auxiliaryRowsOn {V : Type*} {B : Finset V} (A : Finset B)
    (row : B → ℕ) (parts : Finset ℕ) : Finset V :=
  (A.filter fun v ↦ row v ∈ parts).image Subtype.val

variable {V : Type*} {r : ℕ} [Fintype V] (T : Trace V r)

/-- Lift the independent auxiliary choices from the induced graph, then extend
the prescribed set in the original graph over precisely the requested ordinary
rows. All cardinalities refer to distinct vertices in the original coloring. -/
theorem finish_prescribed_ordinary (prep : Prepared T) (hr : 0 < r)
    {E : Finset V} {e n : ℕ} {α β M Y b : ℝ}
    (S : WidthIntegral.Selection (ordinaryLists T E) (rowDeficit T E) (rowIncidence T E)
      e n α β M) (band : RetainedWidth.Band Y b α β)
    {B : Finset V} (subB : B ⊆ lowExterior T E S.retained S.s)
    {A : Finset B} {row : B → ℕ} {aparts oparts : Finset ℕ} (osub : oparts ⊆ S.retained)
    {P D : Finset V} {Q R : Finset B}
    (sR : R ⊆ A) (rep : Partial (targetGraph (inducedColor T.color B) T.target) row R)
    (im : R.image row = aparts)
    (avoids : ∀ x ∈ R, ∀ v ∈ (P ∪ Q.image Subtype.val) ∪ D,
      ¬ (targetGraph T.color T.target).Adj v x.val)
    (qa : ∀ x ∈ Q, row x ∉ aparts)
    (slots : Q.card + aparts.card ≤ S.s)
    (oa : Disjoint P (auxiliaryRowsOn A row aparts))
    (oo : Disjoint P (oparts.biUnion (temporaryRow T E)))
    (small : ∀ x ∈ P, ∀ i ∈ oparts,
      (((temporaryRow T E i).filter ((targetGraph T.color T.target).Adj x)).card : ℝ)
        ≤ (369/1000 : ℝ)*r)
    (ordinary : ∀ x ∈ D, ∃ j ∈ S.retained, j ∉ oparts ∧ x ∈ temporaryRow T E j)
    (shape : (P.card ≤ 2 ∧ D = ∅) ∨ (P.card ≤ 1 ∧ D.card ≤ 2))
    (ind : (targetGraph T.color T.target).IsIndepSet
      (((P ∪ Q.image Subtype.val) ∪ D : Finset V) : Set V)) :
    ∃ O ⊆ oparts.biUnion (temporaryRow T E),
      Partial (targetGraph T.color T.target) T.row O ∧ O.image T.row = oparts ∧
      (R.image Subtype.val ∪ O).card = aparts.card + oparts.card ∧
      Disjoint ((P ∪ Q.image Subtype.val) ∪ D) (R.image Subtype.val ∪ O) ∧
      (targetGraph T.color T.target).IsIndepSet
        ((((P ∪ Q.image Subtype.val) ∪ D) ∪ (R.image Subtype.val ∪ O) : Finset V) : Set V) := by
  let G := targetGraph T.color T.target
  let F := (P ∪ Q.image Subtype.val) ∪ D
  let Rv := R.image Subtype.val
  have labels {x} (hx : x ∈ R) : row x ∈ aparts := im ▸ mem_image_of_mem row hx
  have orig : Rv ⊆ auxiliaryRowsOn A row aparts := by
    intro x hx
    obtain ⟨v,hv,rfl⟩ := mem_image.mp hx
    exact mem_image_of_mem _ (mem_filter.mpr ⟨sR hv,labels hv⟩)
  have fresh : Disjoint F Rv := by
    apply disjoint_left.mpr
    intro x hx hv
    obtain ⟨v,vR,rfl⟩ := mem_image.mp hv
    rcases mem_union.mp hx with pq | dv
    · rcases mem_union.mp pq with pv | qv
      · exact disjoint_left.mp oa pv (orig (mem_image_of_mem _ vR))
      · obtain ⟨u,uq,equ⟩ := mem_image.mp qv
        exact qa u uq ((Subtype.ext equ : u=v) ▸ labels vR)
    · obtain ⟨i,ri,_,vt⟩ := ordinary _ dv
      exact (mem_filter.mp (subB v.property)).2.1 (mem_biUnion.mpr ⟨i,ri,(mem_filter.mp vt).1⟩)
  have together : G.IsIndepSet ((F ∪ Rv : Finset V) : Set V) := by
    have independent := rep.independent
    rw [induced_target_graph] at independent
    intro x hx y hy ne
    rcases mem_union.mp hx with hx | hx <;> rcases mem_union.mp hy with hy | hy
    · exact ind hx hy ne
    · obtain ⟨v,hv,rfl⟩ := mem_image.mp hy
      exact avoids _ hv _ hx
    · obtain ⟨v,hv,rfl⟩ := mem_image.mp hx
      exact fun edge ↦ avoids _ hv _ hy (G.adj_symm edge)
    · obtain ⟨u,hu,rfl⟩ := mem_image.mp hx
      obtain ⟨v,hv,rfl⟩ := mem_image.mp hy
      exact independent hu hv (fun eq ↦ ne (congrArg Subtype.val eq))
  let Qall := Q.image Subtype.val ∪ Rv
  have low : Qall ⊆ lowExterior T E S.retained S.s := by
    intro v hv
    rcases mem_union.mp hv with hq | hr
    · obtain ⟨x,_,rfl⟩ := mem_image.mp hq
      exact subB x.property
    · obtain ⟨x,_,rfl⟩ := mem_image.mp hr
      exact subB x.property
  have countR : Rv.card = aparts.card := by
    calc _ = R.card := card_image_of_injective _ Subtype.val_injective
         _ = (R.image row).card := (card_image_of_injOn rep.distinct).symm
         _ = _ := congrArg card im
  have enough : Qall.card ≤ S.s := by
    apply le_trans (card_union_le ..)
    rw [countR,card_image_of_injective _ Subtype.val_injective]
    exact slots
  have rearrange : (P ∪ Qall) ∪ D = F ∪ Rv := by
    dsimp [Qall,F]
    ac_rfl
  have joined : G.IsIndepSet (((P ∪ Qall) ∪ D : Finset V) : Set V) := rearrange ▸ together
  obtain ⟨O,hO,orep,omap,dis,final⟩ := extend_prescribed_ordinary T prep hr S band oparts osub
    P Qall D oo small low enough ordinary shape joined
  rw [rearrange] at dis final
  obtain ⟨fO,rO⟩ := disjoint_union_left.mp dis
  refine ⟨O,hO,orep,omap,?_,disjoint_union_right.mpr ⟨fresh,fO⟩,?_⟩
  · rw [card_union_of_disjoint rO,countR,← card_image_of_injOn orep.distinct,omap]
  · rwa [union_assoc] at final

/-- Complete either two prescribed exterior vertices, or one exterior vertex
and up to two prescribed row representatives. The new vertices are counted in
the original coloring and lie in the requested auxiliary and ordinary rows.
Taking the ordinary subfamily empty gives a completion wholly inside B. -/
theorem complete_prescribed_rows (prep : Prepared T) (hr : 0 < r)
    {E : Finset V} {e n : ℕ} {α β M Y b : ℝ}
    (S : WidthIntegral.Selection (ordinaryLists T E) (rowDeficit T E) (rowIncidence T E)
      e n α β M) (band : RetainedWidth.Band Y b α β)
    {B : Finset V} (subB : B ⊆ lowExterior T E S.retained S.s)
    (row : B → ℕ) (part : AuxiliaryPartition T S.s B row)
    (A : Finset B) (live : AuxiliarySurvivors
      (targetGraph (inducedColor T.color B) T.target) row (S.s-1) r A)
    (aparts oparts : Finset ℕ) (ai : aparts ⊆ range (S.s-1)) (oi : oparts ⊆ S.retained)
    (P : Finset V) (Q : Finset B) (D : Finset V)
    (oa : Disjoint P (auxiliaryRowsOn A row aparts))
    (oo : Disjoint P (oparts.biUnion (temporaryRow T E)))
    (smallA : ∀ v ∈ P, ∀ i ∈ aparts,
      (((RowExtraction.fiber A row i).filter fun y ↦ (targetGraph T.color T.target).Adj v y.val).card : ℝ)
        ≤ (81/200 : ℝ)*r)
    (smallO : ∀ v ∈ P, ∀ i ∈ oparts,
      (((temporaryRow T E i).filter ((targetGraph T.color T.target).Adj v)).card : ℝ)
        ≤ (369/1000 : ℝ)*r)
    (qa : ∀ x ∈ Q, x ∈ A ∧ row x ∉ aparts)
    (do_ : ∀ x ∈ D, ∃ j ∈ S.retained, j ∉ oparts ∧ x ∈ temporaryRow T E j)
    (shape : (P.card ≤ 2 ∧ Q = ∅ ∧ D = ∅) ∨ (P.card ≤ 1 ∧ Q.card+D.card ≤ 2))
    (ind : (targetGraph T.color T.target).IsIndepSet
      (((P ∪ Q.image Subtype.val) ∪ D : Finset V) : Set V)) :
    ∃ C ⊆ auxiliaryRowsOn A row aparts ∪ oparts.biUnion (temporaryRow T E),
      C.card = aparts.card + oparts.card ∧ Disjoint ((P ∪ Q.image Subtype.val) ∪ D) C ∧
      (targetGraph T.color T.target).IsIndepSet ((((P ∪ Q.image Subtype.val) ∪ D) ∪ C : Finset V) : Set V) ∧
      ∃ R ⊆ A, Partial (targetGraph (inducedColor T.color B) T.target) row R ∧
        R.image row = aparts ∧ ∃ O ⊆ oparts.biUnion (temporaryRow T E),
          Partial (targetGraph T.color T.target) T.row O ∧ O.image T.row = oparts ∧
          C = R.image Subtype.val ∪ O := by
  have ordinary (v) (hv : v ∈ D) : ∃ j ∈ S.retained, v ∈ temporaryRow T E j := by
    obtain ⟨j,ret,_,mem⟩ := do_ v hv
    exact ⟨j,ret,mem⟩
  obtain ⟨R,sR,rep,im,avoid⟩ := colored_auxiliary_representatives T prep hr S band B subB
    row part A live aparts ai P Q D smallA qa ordinary shape
  have slots : Q.card + aparts.card ≤ S.s := by
    by_cases empty : Q = ∅
    · rw [empty,card_empty,zero_add]
      have bound := card_le_card ai
      rw [card_range] at bound
      omega
    · obtain ⟨v,hv⟩ := nonempty_iff_ne_empty.mpr empty
      have strict : aparts ⊂ range (S.s-1) := Finset.ssubset_iff_subset_ne.mpr ⟨ai,fun eq ↦
        (qa v hv).2 (eq ▸ mem_range.mpr (part.labels v))⟩
      have short := card_lt_card strict
      rw [card_range] at short
      obtain h | h := shape
      · exact (empty h.2.1).elim
      · have := h.2
        omega
  have oshape : (P.card ≤ 2 ∧ D = ∅) ∨ (P.card ≤ 1 ∧ D.card ≤ 2) := by
    obtain ⟨p,_,d⟩ | ⟨p,d⟩ := shape
    · exact Or.inl ⟨p,d⟩
    · exact Or.inr ⟨p,by omega⟩
  obtain ⟨O,hO,opr,om,cnt,fresh,indep⟩ := finish_prescribed_ordinary T prep hr S band subB oi
    sR rep im avoid (fun q h ↦ (qa q h).2) slots oa oo smallO do_ oshape ind
  refine ⟨R.image Subtype.val ∪ O,union_subset_union ?_ hO,cnt,fresh,indep,
    R,sR,rep,im,O,hO,opr,om,rfl⟩
  intro x hx
  obtain ⟨v,hv,rfl⟩ := mem_image.mp hx
  exact mem_image_of_mem _ (mem_filter.mpr ⟨sR hv,im ▸ mem_image_of_mem row hv⟩)

end
end Erdos617.ColoredLists
