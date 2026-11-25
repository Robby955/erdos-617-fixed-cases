import LoadCap
import ArcRepairUnion

/-! The repaired sample on its own vertex subtype, with the edge bound and
independence hypothesis used by the signed sample cut. -/

namespace Erdos617.ColoredLists

open Finset PruningOverlap FiniteLaw MarkedSender RepresentativeRepairs
open scoped Classical
noncomputable section
variable {V : Type*} [Fintype V]

/-- Add the unordered pairs and restrict to the sampled exterior vertices. -/
def inducedRepair (G : SimpleGraph V) (W : Finset V) (P : Finset (Sym2 V)) : SimpleGraph W :=
  (G ⊔ SimpleGraph.fromEdgeSet (P:Set (Sym2 V))).induce (W:Set V)

omit [Fintype V] in
/-- The only new edges are images of pairs in P, even when P contains loops,
duplicates of old edges, or pairs with endpoints outside W. -/
theorem inducedRepair_card (G : SimpleGraph V) (W : Finset V) (P : Finset (Sym2 V)) :
    (inducedRepair G W P).edgeFinset.card ≤ (G.induce (W:Set V)).edgeFinset.card+P.card := by
  let B := (G.induce (W:Set V)).edgeFinset
  let R := (inducedRepair G W P).edgeFinset
  let embed := (Function.Embedding.subtype (fun x : V ↦ x ∈ W)).sym2Map
  have added : (R \ B).card ≤ P.card := by
    apply card_le_card_of_injOn embed _ embed.injective.injOn
    intro p
    induction p using Sym2.inductionOn with
    | _ x y =>
      intro hp
      obtain ⟨fresh,old⟩ := mem_sdiff.mp hp
      have h : G.Adj x.val y.val ∨ (s(x.val,y.val) ∈ P ∧ x.val ≠ y.val) := SimpleGraph.mem_edgeFinset.mp fresh
      rcases h with e|e
      · exact False.elim (old (SimpleGraph.mem_edgeFinset.mpr e))
      · exact e.1
  have base := card_le_card_sdiff_add_card (s := R) (t := B)
  change R.card ≤ B.card+P.card
  omega

/-- The finite row index is the retained subtype. This is the same index
set used by the product of independent start laws in expected_excess_union. -/
def sampleArcGraph (G : SimpleGraph V) (I : Finset ℕ) (C : ℕ → Finset V) (L : Finset V)
    (s r : ℕ) [NeZero (30*s*r)] (w : V → State V) (z : I → V → ZMod (30*s*r)) : SimpleGraph V :=
  ArcRepair.graphUnion univ fun i : I ↦ ArcRepair.graph (z i) fun y ↦
    ExcessCircle.excess s r (repairLoad G C L i.val y (w y))

omit [Fintype V] in
/-- Forgetting the subtype sends independent vertices to an original
independent set which avoids every pair in P. -/
private theorem forget_repair (G : SimpleGraph V) (W : Finset V) (P : Finset (Sym2 V))
    (A : Finset W) (h : (inducedRepair G W P).IsIndepSet (A:Set W)) :
    let Z := A.image Subtype.val
    Z ⊆ W ∧ G.IsIndepSet (Z:Set V) ∧ (∀ x ∈ Z, ∀ y ∈ Z, x ≠ y → s(x,y) ∉ P) := by
  refine ⟨?_,?_,?_⟩
  · intro _ hx
    obtain ⟨x,_,rfl⟩ := mem_image.mp hx
    exact x.property
  · intro _ hx _ hy ne adj
    obtain ⟨x,xin,rfl⟩ := mem_image.mp hx
    obtain ⟨y,yin,rfl⟩ := mem_image.mp hy
    exact h xin yin (fun eq ↦ ne (congrArg Subtype.val eq)) (Or.inl adj)
  · intro _ hx _ hy ne adj
    obtain ⟨x,xin,rfl⟩ := mem_image.mp hx
    obtain ⟨y,yin,rfl⟩ := mem_image.mp hy
    exact h xin yin (fun eq ↦ ne (congrArg Subtype.val eq)) (Or.inr ⟨adj,ne⟩)

variable {r : ℕ} (T : Trace V r)

/-- Every positively weighted sample and every lattice start assignment
yield an actual graph on W with the required independence cap. -/
theorem sample_repair_cap (prep : Prepared T) {E : Finset V} {e n : ℕ} {α β M Y b : ℝ}
    (S : WidthIntegral.Selection (ordinaryLists T E) (rowDeficit T E) (rowIncidence T E) e n α β M)
    (hr : 2 ≤ r) (no : ¬Witness T.color) (band : RetainedWidth.Band Y b α β)
    (slots : e+(ordinaryLists T E).card=r) {p rate hp hp1} {w : V → State V}
    (positive : 0 < (product (senderLaw T E S.retained S.s p rate hp hp1)).weight w)
    [NeZero (30*S.s*r)] (z : S.retained → V → ZMod (30*S.s*r)) :
    let G := targetGraph T.color T.target
    let C := rowList T E
    let H := senderSet T E S.retained S.s
    let L := lowExterior T E S.retained S.s
    let W := exterior H L w
    let P := edges G S.retained C H (uniqueGroup T E S.retained S.s) L w ∪
      (sampleArcGraph G S.retained C L S.s r w z).edgeFinset
    ∀ A : Finset W, (inducedRepair G W P).IsIndepSet (A:Set W) → A.card ≤ S.s-1 := by
  intro G C H L W P A ind
  let Z := A.image Subtype.val
  let starts := fun i : ℕ ↦ if hi : i ∈ S.retained then z ⟨i,hi⟩ else fun _ ↦ 0
  let U := uniqueGroup T E S.retained S.s
  have forgotten := forget_repair G W P A ind
  have outside : Disjoint W (S.retained.biUnion C) := by
    apply disjoint_left.mpr
    intro v hv
    rcases mem_union.mp hv with low|marked
    · exact (mem_filter.mp low).2.1
    · exact (mem_senderSet T).mp (mem_filter.mp marked).1 |>.1
  have qual : S.retained ⊆ qualifying T := by
    intro i hi
    rw [S.retained_eq] at hi
    exact (mem_inter.mp (mem_sdiff.mp (mem_filter.mp hi).1).1).2
  have fixed : Disjoint L H := disjoint_left.mpr fun _ hl hh ↦ (mem_sdiff.mp hh).2 hl
  have groups (i) (_ : i ∈ S.retained) : U i ⊆ H := filter_subset ..
  have scale : 1 ≤ S.s := by have := S.scale_lo; omega
  have cap := realized_repaired_independence_cap T S hr no band slots H L U w starts outside groups fixed
    (fun _ _ _ h ↦ represented_support T positive h) (fun _ hi x _ ↦ sender_load_fits T prep qual scale positive hi x) Z
    forgotten.1 forgotten.2.1 (fun x hx y hy ne hp ↦ forgotten.2.2 x hx y hy ne (mem_union_left _ hp))
    (by
      intro i hi x hx y hy ne
      by_contra arcHit
      apply forgotten.2.2 x hx y hy ne
      apply mem_union_right
      apply SimpleGraph.mem_edgeFinset.mpr
      refine ⟨⟨i,hi⟩,mem_univ _,ne,?_⟩
      simpa only [starts,dite_eq_left hi] using arcHit)
  rwa [show Z.card = A.card from card_image_of_injective _ Subtype.val_injective] at cap

end
end Erdos617.ColoredLists
