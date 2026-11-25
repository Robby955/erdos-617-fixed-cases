import AuxiliaryCliques
import UniqueAttachment
import Mathlib.Data.Finset.Sum

/-! The two families of rows on which Appendix A, §4 uses attachment.
All rows and all large-neighborhood tests are measured in the original target graph. -/

namespace Erdos617.ColoredLists

open Finset PruningOverlap PackingLists RowExtraction
open scoped Classical
noncomputable section

variable {V : Type*} {r : ℕ} [Fintype V] (T : Trace V r)

/-- The two tags distinguish auxiliary survivor rows from trimmed ordinary rows. -/
def attachmentRow (E : Finset V) {B : Finset V} (A : Finset B) (row : B → ℕ) :
    ℕ ⊕ ℕ → Finset V :=
  Sum.elim (fun i ↦ (fiber A row i).image Subtype.val) (temporaryRow T E)

/-- A large attachment means strictly more neighbors than the appropriate
threshold. Its negation gives the weak upper bound used in the list proof. -/
def attachmentLarge (E : Finset V) {B : Finset V} (A : Finset B) (row : B → ℕ)
    (v : V) (i : ℕ ⊕ ℕ) : Prop :=
  (i.elim (fun _ ↦ (81/200:ℝ)) (fun _ ↦ (369/1000:ℝ)))*r <
    (((attachmentRow T E A row i).filter ((targetGraph T.color T.target).Adj v)).card : ℝ)

/-- The row and graph hypotheses needed for enlargement in either arena. -/
structure ArenaBounds {W K : Type*} (G : SimpleGraph W) (arena : Finset W) (parts : Finset K)
    (row : K → Finset W) (r : ℕ) : Prop where
  inside : ∀ i ∈ parts, row i ⊆ arena
  disjoint : ∀ i ∈ parts, ∀ j ∈ parts, i ≠ j → Disjoint (row i) (row j)
  cliques : ∀ i ∈ parts, G.IsClique (row i : Set W)
  order : arena.card = parts.card*r+1
  independent : ∀ Z ⊆ arena, G.IsIndepSet (Z : Set W) → Z.card ≤ parts.card
  clique_cap : ∀ Z ⊆ arena, G.IsClique (Z : Set W) → Z.card ≤ r

omit [Fintype V] in
private theorem auxiliary_image_clique {B : Finset V} {A : Finset B} {row : B → ℕ} {h : ℕ}
    (live : AuxiliarySurvivors (targetGraph (inducedColor T.color B) T.target) row h r A)
    {i : ℕ} (hi : i < h) :
    (targetGraph T.color T.target).IsClique ((fiber A row i).image Subtype.val : Set V) := by
  have cl := (live.rows i hi).2.1
  rw [induced_target_graph] at cl
  intro x hx y hy ne
  obtain ⟨u,hu,rfl⟩ := mem_image.mp hx
  obtain ⟨v,hv,rfl⟩ := mem_image.mp hy
  exact cl hu hv (fun eq ↦ ne (congrArg Subtype.val eq))

omit [Fintype V] in
private theorem auxiliary_image_disjoint {B : Finset V} {A : Finset B} {row : B → ℕ}
    {i j : ℕ} (ne : i ≠ j) : Disjoint ((fiber A row i).image Subtype.val)
      ((fiber A row j).image Subtype.val) := by
  refine disjoint_left.mpr fun x hx hy ↦ ?_
  obtain ⟨u,hu,rfl⟩ := mem_image.mp hx
  obtain ⟨v,hv,eq⟩ := mem_image.mp hy
  have := Subtype.val_injective eq
  subst v
  exact ne ((mem_filter.mp hu).2.symm.trans (mem_filter.mp hv).2)


/-- Output of the enlargement step. Large attachments always refer to the
original rows; sizes and deficits in the last two fields refer to enlarged rows. -/
structure EnlargedRows {W K : Type*} [DecidableEq W] (G : SimpleGraph W) (arena : Finset W)
    (parts : Finset K) (row : K → Finset W) (large : W → K → Prop) (r : ℕ) : Prop where
  attached : ∀ x ∈ UniqueAttachment.exterior arena parts row, ∃ i ∈ parts, large x i
  inside : ∀ i ∈ parts, UniqueAttachment.enlarged arena parts row large i ⊆ arena
  cliques : ∀ i ∈ parts, G.IsClique (UniqueAttachment.enlarged arena parts row large i : Set W)
  disjoint : ∀ i ∈ parts, ∀ j ∈ parts, i ≠ j → Disjoint
    (UniqueAttachment.enlarged arena parts row large i) (UniqueAttachment.enlarged arena parts row large j)
  remaining : ∀ x ∈ UniqueAttachment.exterior arena parts (UniqueAttachment.enlarged arena parts row large),
    ∃ i ∈ parts, ∃ j ∈ parts, i ≠ j ∧ large x i ∧ large x j
  size_cap : ∀ i ∈ parts, (UniqueAttachment.enlarged arena parts row large i).card ≤ r
  deficit_sum : (∑ i ∈ parts, (r-(UniqueAttachment.enlarged arena parts row large i).card))+1 =
    (UniqueAttachment.exterior arena parts (UniqueAttachment.enlarged arena parts row large)).card

/-- In either arena, the extension proof is the last input to the entire
enlargement step, including the exact count handed to the capacity argument. -/
theorem ArenaBounds.enlarge {W K : Type*} [DecidableEq W] [DecidableEq K]
    {G : SimpleGraph W} {arena : Finset W} {parts : Finset K} {row : K → Finset W}
    {large : W → K → Prop} {r : ℕ} (bounds : ArenaBounds G arena parts row r)
    (extendRows : UniqueAttachment.CanExtend G arena parts row large) :
    EnlargedRows G arena parts row large r := by
  have rowIn (i) (hi : i ∈ parts) : UniqueAttachment.enlarged arena parts row large i ⊆ arena :=
    union_subset (bounds.inside i hi) ((filter_subset ..).trans (sdiff_subset ..))
  have cl (i) (hi : i ∈ parts) := UniqueAttachment.enlarged_clique
    bounds.inside bounds.independent extendRows (bounds.cliques i hi)
  exact ⟨fun _ hx ↦ UniqueAttachment.exists_large bounds.inside bounds.independent extendRows hx,
    rowIn, cl, fun _ hi _ hj ne ↦ UniqueAttachment.enlarged_disjoint bounds.disjoint hi hj ne,
    fun _ hx ↦ UniqueAttachment.two_large_of_remaining bounds.inside bounds.independent extendRows hx,
    fun i hi ↦ bounds.clique_cap _ (rowIn i hi) (cl i hi),
    UniqueAttachment.enlarged_deficit_sum bounds.order bounds.inside bounds.disjoint bounds.cliques
      bounds.independent bounds.clique_cap extendRows⟩

private theorem temp_label {E : Finset V} {i : ℕ} {v : V} (mem : v ∈ temporaryRow T E i) :
    T.row v = i := by
  have hl := (mem_filter.mp mem).1
  simp only [rowList,available,mem_filter] at hl
  exact hl.2.1

private theorem temp_disjoint_aux {E B : Finset V} {A : Finset B} {row : B → ℕ}
    {ordinary : Finset ℕ} {s i j : ℕ} (hj : j ∈ ordinary)
    (sub : B ⊆ lowExterior T E ordinary s) :
    Disjoint ((fiber A row i).image Subtype.val) (temporaryRow T E j) := by
  refine disjoint_left.mpr fun x hx hy ↦ ?_
  obtain ⟨v,_,rfl⟩ := mem_image.mp hx
  exact (mem_filter.mp (sub v.property)).2.1 (mem_biUnion.mpr ⟨j,hj,(mem_filter.mp hy).1⟩)

variable {E : Finset V} {e n : ℕ} {α β M Y b : ℝ}
  (S : WidthIntegral.Selection (ordinaryLists T E) (rowDeficit T E) (rowIncidence T E)
      e n α β M)

/-- On B of order hr+1 the auxiliary cliques alone give h row slots, and the
low-attachment argument bounds independent sets of the original graph in B by h. -/
theorem auxiliary_arena_bounds (hr : 2 ≤ r) (no : ¬Witness T.color)
    (band : RetainedWidth.Band Y b α β) (slots : e+(ordinaryLists T E).card = r)
    {B : Finset V} (sub : B ⊆ lowExterior T E S.retained S.s)
    (order : B.card = (S.s-1)*r+1) (A : Finset B) (row : B → ℕ)
    (live : AuxiliarySurvivors (targetGraph (inducedColor T.color B) T.target) row (S.s-1) r A) :
    ArenaBounds (targetGraph T.color T.target) B ((range (S.s-1)).disjSum (∅ : Finset ℕ))
      (attachmentRow T E A row) r := by
  constructor
  · intro k hk x hx
    cases k with
    | inl i =>
      obtain ⟨v,_,rfl⟩ := mem_image.mp hx
      exact v.property
    | inr j => simp at hk
  · intro k hk l hl ne
    cases k with
    | inr i => simp at hk
    | inl i =>
      cases l with
      | inr j => simp at hl
      | inl j => exact auxiliary_image_disjoint (fun he ↦ ne (congrArg Sum.inl he))
  · intro k hk
    cases k with
    | inl i => exact auxiliary_image_clique T live (mem_range.mp (inl_mem_disjSum.mp hk))
    | inr i => simp at hk
  · simpa using order
  · intro Z hZ ind
    simpa using exterior_independence_cap T S hr no band slots Z (hZ.trans sub) ind
  · exact fun Z _ cl ↦ (caps_of_no_witness T.color T.target hr no).2 Z cl

/-- In the full arena there are h auxiliary rows and r−h retained ordinary
rows. All rows are disjoint in the original vertex type, including rows of
different kinds. -/
theorem full_arena_bounds (hr : 2 ≤ r) (no : ¬Witness T.color)
    (order : Fintype.card V = r^2+1) (slots : e+(ordinaryLists T E).card = r)
    (lists : ListBounds (targetGraph T.color T.target) T.row univ (ColoredLists.live T)
        (range r) (qualifying T) E r)
    {B : Finset V} (sub : B ⊆ lowExterior T E S.retained S.s)
    (A : Finset B) (row : B → ℕ)
    (live : AuxiliarySurvivors (targetGraph (inducedColor T.color B) T.target) row (S.s-1) r A) :
    ArenaBounds (targetGraph T.color T.target) univ ((range (S.s-1)).disjSum S.retained)
      (attachmentRow T E A row) r := by
  have retained : S.retained ⊆ ordinaryLists T E := by
    rw [S.retained_eq]
    exact (filter_subset ..).trans sdiff_subset
  have count : ((range (S.s-1)).disjSum S.retained).card = r := by
    rw [card_disjSum,card_range]
    have := card_sdiff_add_card_eq_card retained
    have := S.omitted
    omega
  constructor
  · exact fun _ _ ↦ subset_univ _
  · intro k hk l hl ne
    cases k with
    | inl i =>
      cases l with
      | inl j => exact auxiliary_image_disjoint (fun he ↦ ne (congrArg Sum.inl he))
      | inr j => exact temp_disjoint_aux T (inr_mem_disjSum.mp hl) sub
    | inr i =>
      cases l with
      | inl j => exact (temp_disjoint_aux T (inr_mem_disjSum.mp hk) sub).symm
      | inr j =>
        refine disjoint_left.mpr fun x hx hy ↦ ?_
        exact ne (congrArg Sum.inr ((temp_label T hx).symm.trans (temp_label T hy)))
  · intro k hk
    cases k with
    | inl i => exact auxiliary_image_clique T live (mem_range.mp (inl_mem_disjSum.mp hk))
    | inr j => exact temporary_row_isClique T lists (retained (inr_mem_disjSum.mp hk))
  · simpa [count,pow_two] using order
  · rw [count]
    exact fun Z _ ind ↦ (caps_of_no_witness T.color T.target hr no).1 Z ind
  · exact fun Z _ cl ↦ (caps_of_no_witness T.color T.target hr no).2 Z cl

end
end Erdos617.ColoredLists
