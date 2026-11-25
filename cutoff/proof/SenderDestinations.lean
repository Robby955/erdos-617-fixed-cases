import OrdinaryRepresentatives

/-! The exterior population on the original retained cliques at the start of Appendix A §5. -/

namespace Erdos617.ColoredLists

open Finset PruningOverlap PackingLists
open scoped Classical
noncomputable section

variable {V : Type*} {r : ℕ} [Fintype V] (T : Trace V r)

/-- The exterior vertices whose attachment exceeds the threshold on at least
one retained clique. These are the senders before marking or thinning. -/
def senderSet (E : Finset V) (parts : Finset ℕ) (s : ℕ) : Finset V :=
  (univ \ parts.biUnion (rowList T E)) \ lowExterior T E parts s

/-- A sender lies outside the original retained cliques and has at least one
destination with more than (9/40)r/s actual target neighbors. -/
theorem mem_senderSet {E : Finset V} {parts : Finset ℕ} {s : ℕ} {v : V} :
    v ∈ senderSet T E parts s ↔ v ∉ parts.biUnion (rowList T E) ∧
      ∃ i ∈ parts, (9/40:ℝ)/s*r <
        (((rowList T E i).filter ((targetGraph T.color T.target).Adj v)).card:ℝ) := by
  simp only [senderSet,lowExterior,mem_sdiff,mem_filter,mem_univ,true_and]
  constructor
  · rintro ⟨out,notLow⟩
    by_contra! bad
    exact notLow ⟨out,fun i hi ↦ bad out i hi⟩
  · rintro ⟨out,i,hi,hit⟩
    exact ⟨out,fun low ↦ hit.not_ge (low.2 i hi)⟩

private theorem rowList_label {E : Finset V} {i : ℕ} {v : V} (hv : v ∈ rowList T E i) :
    T.row v = i := by
  simp only [rowList,available,mem_filter] at hv
  exact hv.2.1

/-- All original vertices are accounted for exactly once. In vertex units the
sender population is one plus the exterior shortage plus the total retained
row deficit, on the very same selection that supplies the shortage. -/
theorem sender_ledger {E : Finset V} {e n : ℕ} {α β M : ℝ}
    (S : WidthIntegral.Selection (ordinaryLists T E) (rowDeficit T E) (rowIncidence T E)
      e n α β M) (order : Fintype.card V = r^2+1) (slots : e+(ordinaryLists T E).card=r) :
    ((senderSet T E S.retained S.s).card:ℝ) =
      1+(((S.s-1:ℕ):ℝ)*r-((lowExterior T E S.retained S.s).card:ℝ))+
        ∑ i ∈ S.retained, ((r:ℝ)-(rowList T E i).card) := by
  let K := S.retained.biUnion (rowList T E)
  let outside := univ \ K
  let G := lowExterior T E S.retained S.s
  let H := senderSet T E S.retained S.s
  have retained : S.retained ⊆ ordinaryLists T E := by
    rw [S.retained_eq]
    exact (filter_subset ..).trans (sdiff_subset ..)
  have count := card_sdiff_add_card_eq_card retained
  have omitted := S.omitted
  have sumSlots : (S.s-1:ℕ)+S.retained.card=r := by omega
  have sumReal : ((S.s-1:ℕ):ℝ)+S.retained.card=r := by exact_mod_cast sumSlots
  have within : G ⊆ outside := fun _ hv ↦ mem_sdiff.mpr ⟨mem_univ _,(mem_filter.mp hv).2.1⟩
  have partition : (H.card:ℝ)+G.card+K.card = (r:ℝ)^2+1 := by
    have first : H.card+G.card = outside.card := card_sdiff_add_card_eq_card within
    have second : outside.card+K.card = Fintype.card V :=
      (card_sdiff_add_card_eq_card (subset_univ K)).trans card_univ
    exact_mod_cast (show H.card+G.card+K.card=r^2+1 by omega)
  have distinct : (S.retained:Set ℕ).PairwiseDisjoint (rowList T E) := by
    intro i _ j _ ne
    exact disjoint_left.mpr fun _ hi hj ↦ ne ((rowList_label T hi).symm.trans (rowList_label T hj))
  have used : (K.card:ℝ) = ∑ i ∈ S.retained, ((rowList T E i).card:ℝ) := by
    exact_mod_cast card_biUnion distinct
  change (H.card:ℝ) = 1+(((S.s-1:ℕ):ℝ)*r-(G.card:ℝ))+_
  rw [sum_sub_distrib,sum_const,nsmul_eq_mul,← used]
  linarith only [partition,congrArg (fun y : ℝ ↦ y*r) sumReal]

end
end Erdos617.ColoredLists
