import SampleRepairGraph
import ColoringSample
import SignedSampleCut
import SignedCutExpectation

/-! The signed cut for a fixed tested subfamily of the same actual retained rows. -/

namespace Erdos617.ColoredLists

open Finset PruningOverlap PackingLists FiniteLaw MarkedSender RepresentativeRepairs
open scoped Classical
noncomputable section
local instance (I : Finset ℕ) : DecidableEq I := Classical.decEq _
variable {V : Type*} {r : ℕ} [Fintype V] (T : Trace V r)

/-- All possible justifications for a repair are collected as unordered
pairs in a single set. Its restriction to a particular exterior can only
decrease its size. -/
def samplePairs (E : Finset V) (I : Finset ℕ) (s : ℕ) [NeZero (30*s*r)]
    (w : V → State V) (z : I → V → ZMod (30*s*r)) : Finset (Sym2 V) :=
  let G := targetGraph T.color T.target
  let C := rowList T E
  let H := senderSet T E I s
  let L := lowExterior T E I s
  edges G I C H (uniqueGroup T E I s) L w ∪ (sampleArcGraph G I C L s r w z).edgeFinset

def rowToExterior (E : Finset V) (W : Finset V) (i : ℕ) : ℝ :=
  ∑ x ∈ W, SameRowConflicts.degree (targetGraph T.color T.target) (rowList T E i) x

def betweenRows (E : Finset V) (a : ℕ × ℕ) : ℝ :=
  ((RepresentativeCut.cut (targetGraph T.color T.target) (rowList T E a.1) (rowList T E a.2)).card:ℝ)

variable {E : Finset V} {e n : ℕ} {α β M Y b : ℝ}
  (S : WidthIntegral.Selection (ordinaryLists T E) (rowDeficit T E) (rowIncidence T E) e n α β M)

/-- A fixed set of tests on a positive-weight outcome. The cap of the
repaired graph and the budget for its original edge additions are derived
on the very same exterior W. -/
theorem sample_signed_cut (prep : Prepared T) (hr : 2 ≤ r) (no : ¬Witness T.color)
    (lists : ListBounds (targetGraph T.color T.target) T.row univ (live T) (range r) (qualifying T) E r)
    (band : RetainedWidth.Band Y b α β) (slots : e+(ordinaryLists T E).card=r)
    (K : Finset ℕ) (tested : K ⊆ S.retained) {p rate hp hp1} {w : V → State V}
    (positive : 0 < (product (senderLaw T E S.retained S.s p rate hp hp1)).weight w)
    [NeZero (30*S.s*r)] (z : S.retained → V → ZMod (30*S.s*r)) :
    let h := S.s-1
    let H := h+K.card
    let W := exterior (senderSet T E S.retained S.s) (lowExterior T E S.retained S.s) w
    let v := (h:ℝ)*r-W.card
    let d := fun i ↦ (r:ℝ)-(rowList T E i).card
    let D := ∑ i ∈ K, d i
    2*((∑ i ∈ K, rowToExterior T E W i)+(∑ a ∈ rowPairs K, betweenRows T E a)) ≤
      2*((samplePairs T E S.retained S.s w z).card:ℝ)+r*H*((H:ℝ)-1)+D^2-
        (∑ i ∈ K, (d i)^2)+2*v*D+v*(v-1) := by
  intro h H W v d D
  let G := targetGraph T.color T.target
  let C := rowList T E
  let P := samplePairs T E S.retained S.s w z
  have selected : S.retained ⊆ ordinaryLists T E := by
    rw [S.retained_eq]
    exact (filter_subset ..).trans sdiff_subset
  have label {x : V} {i : ℕ} (hx : x ∈ C i) : T.row x = i := by
    simp only [C,rowList,available,mem_filter] at hx
    exact hx.2.1
  have apart : (K:Set ℕ).PairwiseDisjoint C := fun i _ k _ ne ↦
    disjoint_left.mpr fun _ hx hy ↦ ne ((label hx).symm.trans (label hy))
  have separated : Disjoint W (K.biUnion C) := by
    apply disjoint_left.mpr
    intro x hx hy
    obtain ⟨i,hi,hxi⟩ := mem_biUnion.mp hy
    have used := mem_biUnion.mpr ⟨i,tested hi,hxi⟩
    rcases mem_union.mp hx with low|mark
    · exact (mem_filter.mp low).2.1 used
    · exact (mem_senderSet T).mp (mem_filter.mp mark).1 |>.1 <| used
  have clique (i) (hi : i ∈ K) : G.IsClique (C i:Set V) := by
    have ordinary := selected (tested hi)
    exact lists.clique i (mem_sdiff.mp (mem_sdiff.mp (mem_inter.mp ordinary).1).1).2
  have count := card_sdiff_add_card_eq_card selected
  have omitted := S.omitted
  have size := card_le_card tested
  have Hcap : h+K.card ≤ r := by dsimp only [h]; omega
  have cap := sample_repair_cap T prep S hr no band slots positive z
  have cost : ((inducedRepair G W P).edgeFinset.card:ℝ) ≤
      ((G.induce (W:Set V)).edgeFinset.card:ℝ)+(P.card:ℝ) := by exact_mod_cast inducedRepair_card G W P
  exact SignedSampleCut.full_incidence_cut T.color T.target W K C h (inducedRepair G W P) P.card
    hr no apart separated clique Hcap cap cost

/-- Average the actual cut, retaining each target edge between tested rows.
This holds for every admissible thinning probability, including oversampling. -/
theorem expected_fixed_cut (prep : Prepared T) (hr : 2 ≤ r) (no : ¬Witness T.color)
    (lists : ListBounds (targetGraph T.color T.target) T.row univ (live T) (range r) (qualifying T) E r)
    (band : RetainedWidth.Band Y b α β) (slots : e+(ordinaryLists T E).card=r)
    (K : Finset ℕ) (tested : K ⊆ S.retained)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) [NeZero (30*S.s*r)] :
    let I := S.retained
    let s := S.s
    let h := s-1
    let H := h+K.card
    let L := lowExterior T E I s
    let send := senderSet T E I s
    let μ := product (senderLaw T E I s p (retry_rate_of_scale S.scale_lo) hp hp1)
    let ν := product fun _ : I ↦ ArcRepair.starts V (30*s*r)
    let P := μ.expect (fun w ↦ ν.expect fun z ↦ ((samplePairs T E I s w z).card:ℝ))
    let m := μ.expect (markCount send)
    let u := (h:ℝ)*r-L.card-m
    let d := fun i ↦ (r:ℝ)-(rowList T E i).card
    let D := ∑ i ∈ K, d i
    2*((∑ i ∈ K, μ.expect (fun w ↦ rowToExterior T E (exterior send L w) i))+
      ∑ a ∈ rowPairs K, betweenRows T E a) ≤
      2*P+(r*H*((H:ℝ)-1)+D^2-(∑ i ∈ K, (d i)^2))+2*u*D+u^2+m-u := by
  intro I s h H L send μ ν P m u d D
  let W := exterior send L
  let v := fun w ↦ (h:ℝ)*r-((W w).card:ℝ)
  let cross := ∑ a ∈ rowPairs K, betweenRows T E a
  let cut := fun w ↦ (∑ i ∈ K, rowToExterior T E (W w) i)+cross
  let B := r*H*((H:ℝ)-1)+D^2-(∑ i ∈ K, (d i)^2)
  let repair := fun w z ↦ ((samplePairs T E I s w z).card:ℝ)
  have point (w) (positive : 0 < μ.weight w) (z) :
      2*cut w ≤ 2*repair w z+B+2*v w*D+v w*(v w-1) := by
    have per := sample_signed_cut T S prep hr no lists band slots K tested positive z
    change 2*cut w ≤ 2*repair w z+_+D^2-(∑ i ∈ K, (d i)^2)+2*v w*D+v w*(v w-1) at per
    dsimp only [B]
    linarith only [per]
  have mom := exterior_shortage_moments T E I s p (retry_rate_of_scale S.scale_lo) hp hp1
  have bound := expected_signed_cut μ ν cut v repair B D u m point mom.1 mom.2
  have cutmean : μ.expect cut = (∑ i ∈ K, μ.expect (fun w ↦ rowToExterior T E (W w) i))+cross := by
    unfold cut
    rw [Law.expect_add,Law.expect_const,Law.expect_sum]
  rw [cutmean] at bound
  exact bound

end
end Erdos617.ColoredLists
