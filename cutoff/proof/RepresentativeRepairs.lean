import SameRowConflicts
import DistinctRowConflicts

/-! The unordered representative repair edges on the actual sampled exterior. -/

namespace Erdos617.RepresentativeRepairs

open Finset FiniteLaw
open scoped Classical
noncomputable section
variable {V : Type*} [Fintype V]

def rowPairs (parts : Finset ℕ) := (parts ×ˢ parts).filter fun p ↦ p.1 < p.2

/-- Every conflicting pair of representative outputs appears in exactly one
orientation of its two row labels. The image takes unordered sender edges. -/
def crossEdges (G : SimpleGraph V) (C D U T : Finset V) (w : V → Option (Option V)) :=
  ((U ×ˢ T).filter fun p ↦ ∃ a ∈ C, ∃ b ∈ D,
    w p.1 = some (some a) ∧ w p.2 = some (some b) ∧ G.Adj a b).image Sym2.mk.uncurry

/-- The exterior points available in the outcome w, including the fixed
low-attachment set L. -/
def exterior (H L : Finset V) (w : V → Option (Option V)) :=
  L ∪ H.filter fun x ↦ (w x).isSome

/-- Multiple reasons for adding the same edge give a single unordered edge. -/
def edges (G : SimpleGraph V) (parts : Finset ℕ) (C : ℕ → Finset V) (H : Finset V)
    (U : ℕ → Finset V) (L : Finset V) (w : V → Option (Option V)) :=
  parts.biUnion (fun i ↦ SameRowConflicts.edges G (C i) (U i) (H \ U i) L w) ∪
    (rowPairs parts).biUnion fun p ↦ crossEdges G (C p.1) (C p.2) (U p.1) (U p.2) w

omit [Fintype V] in
private theorem cross_count (G : SimpleGraph V) (C D U T : Finset V) (w : V → Option (Option V)) :
    ((crossEdges G C D U T w).card:ℝ) ≤
      ∑ x ∈ U, ∑ y ∈ T, RepresentativeCut.collision G C D (w x) (w y) := by
  let coll (p : V × V) := ∃ a ∈ C, ∃ b ∈ D,
    w p.1 = some (some a) ∧ w p.2 = some (some b) ∧ G.Adj a b
  have nonneg (p : V × V) : 0 ≤ RepresentativeCut.collision G C D (w p.1) (w p.2) := by
    apply sum_nonneg
    intro a _
    apply mul_nonneg <;> unfold RepresentativeCut.atom <;> split <;> norm_num
  have lower (p : V × V) (_ : p ∈ U ×ˢ T) :
      (if coll p then (1:ℝ) else 0) ≤ RepresentativeCut.collision G C D (w p.1) (w p.2) := by
    split_ifs with h
    · obtain ⟨a,ha,b,hb,hx,hy,adj⟩ := h
      have hit : (a,b) ∈ RepresentativeCut.cut G C D := mem_filter.mpr ⟨mem_product.mpr ⟨ha,hb⟩,adj⟩
      rw [hx,hy,RepresentativeCut.collision_selected,ite_eq_left hit]
    · exact nonneg _
  have card : (crossEdges G C D U T w).card ≤ ((U ×ˢ T).filter coll).card := card_image_le
  apply ((Nat.cast_le (α := ℝ)).mpr card).trans
  have sum := sum_le_sum lower
  rw [card_filter,Nat.cast_sum]
  apply le_trans _ (sum_product (s := U) (t := T) (f := fun p ↦ RepresentativeCut.collision G C D (w p.1) (w p.2))).le
  simpa only [Nat.cast_ite,Nat.cast_one,Nat.cast_zero] using sum

/-- Expected number of distinct representative repair edges, with both terms
evaluated in the same product of sender laws. The first sum uses each row's
actual cut to the sampled exterior; the second uses the cut between true rows. -/
theorem expected_edges (G : SimpleGraph V) (parts : Finset ℕ) (C : ℕ → Finset V)
    (H : Finset V) (U : ℕ → Finset V) (L : Finset V) (μ : V → Law (Option (Option V)))
    (inside : ∀ i ∈ parts, U i ⊆ H)
    (groups : ∀ i ∈ parts, ∀ k ∈ parts, i ≠ k → Disjoint (U i) (U k))
    (fixed : Disjoint L H) (r j : ℝ) (hr : 0 < r) (hj : 1 ≤ j)
    (cap : ∀ i ∈ parts, ∀ x ∈ U i, ∀ v ∈ C i, (μ x).weight (some (some v)) ≤ j/r)
    (heavy : ∀ i ∈ parts, ∀ x ∈ U i, r/2 ≤ SameRowConflicts.degree G (C i) x) :
    (product μ).expect (fun w ↦ ((edges G parts C H U L w).card:ℝ)) ≤
      (∑ i ∈ parts, (j/r)*(U i).card*(product μ).expect
        (fun w ↦ ∑ y ∈ exterior H L w, SameRowConflicts.degree G (C i) y)) +
      (j/r)^2 * ∑ p ∈ rowPairs parts,
        ((U p.1).card:ℝ)*(U p.2).card*((RepresentativeCut.cut G (C p.1) (C p.2)).card:ℝ) := by
  let localEdges := fun (w : V → Option (Option V)) i ↦ SameRowConflicts.edges G (C i) (U i) (H \ U i) L w
  let across := fun (w : V → Option (Option V)) (p : ℕ × ℕ) ↦ crossEdges G (C p.1) (C p.2) (U p.1) (U p.2) w
  have size (w : V → Option (Option V)) :
      ((edges G parts C H U L w).card:ℝ) ≤ (∑ i ∈ parts, ((localEdges w i).card:ℝ))+
        ∑ p ∈ rowPairs parts, ((across w p).card:ℝ) := by
    have n : (edges G parts C H U L w).card ≤ (∑ i ∈ parts, (localEdges w i).card)+
        ∑ p ∈ rowPairs parts, (across w p).card :=
      (card_union_le ..).trans (Nat.add_le_add (card_biUnion_le ..) (card_biUnion_le ..))
    exact_mod_cast n
  apply ((product μ).expect_mono size).trans
  rw [Law.expect_add,Law.expect_sum,Law.expect_sum,mul_sum]
  apply add_le_add
  · apply sum_le_sum
    intro i hi
    have partition := union_sdiff_of_subset (inside i hi)
    have realSet (w : V → Option (Option V)) :
        SameRowConflicts.sampled (U i) (H \ U i) L w = exterior H L w := by
      simp only [SameRowConflicts.sampled,exterior,partition]
    simpa only [realSet] using SameRowConflicts.expected_edges_le_cut G (C i) (U i) (H \ U i) L μ
      (disjoint_left.mpr fun _ hx hy ↦ (mem_sdiff.mp hy).2 hx) (by rwa [partition]) r j hr hj (cap i hi) (heavy i hi)
  · apply sum_le_sum
    intro p hp
    obtain ⟨h,lt⟩ := mem_filter.mp hp
    obtain ⟨i,k⟩ := mem_product.mp h
    have atom (l) (hl : l ∈ parts) (x) (hx : x ∈ U l) (v) (hv : v ∈ C l) :
        (μ x).expect (RepresentativeCut.atom v) ≤ j/r := by
      trans (μ x).weight (some (some v))
      · apply le_of_eq
        convert Law.expect_atom (μ x) (some (some v)) using 2
        funext a
        by_cases h : a = some (some v) <;> simp [RepresentativeCut.atom,h]
      · exact cap l hl x hx v hv
    have budget := RepresentativeCut.between_row_groups G (C p.1) (C p.2) (U p.1) (U p.2) μ
      (groups _ i _ k (ne_of_lt lt)) (atom _ i) (atom _ k)
    apply ((product μ).expect_mono (cross_count G (C p.1) (C p.2) (U p.1) (U p.2))).trans
    exact budget.trans_eq (by ring)

omit [Fintype V] in
/-- Two marked senders in the same unique group always give one repair edge.
This includes the case of equal representative outputs. -/
theorem same_group_edge (G : SimpleGraph V) (parts : Finset ℕ) (C : ℕ → Finset V)
    (H : Finset V) (U : ℕ → Finset V) (L : Finset V) (w : V → Option (Option V))
    {i : ℕ} (hi : i ∈ parts) {x y : V} (hx : x ∈ U i) (hy : y ∈ U i) (ne : x ≠ y)
    (mx : (w x).isSome) (my : (w y).isSome) : s(x,y) ∈ edges G parts C H U L w := by
  apply mem_union_left _
  apply mem_biUnion.mpr ⟨i,hi,?_⟩
  apply mem_union_left _
  apply mem_image_of_mem Sym2.mk.uncurry (a := (x,y))
  exact mem_offDiag.mpr
    ⟨mem_filter.mpr ⟨hx,mx⟩,mem_filter.mpr ⟨hy,my⟩,ne⟩

omit [Fintype V] in
/-- A representative hitting another sampled exterior vertex produces an
edge even when both senders belong to this row. -/
theorem incident_edge (G : SimpleGraph V) (parts : Finset ℕ) (C : ℕ → Finset V)
    (H : Finset V) (U : ℕ → Finset V) (L : Finset V) (w : V → Option (Option V))
    {i : ℕ} (hi : i ∈ parts) {x y v : V} (hx : x ∈ U i) (hv : v ∈ C i)
    (ox : w x = some (some v)) (hy : y ∈ exterior H L w) (ne : x ≠ y)
    (adj : G.Adj y v) : s(x,y) ∈ edges G parts C H U L w := by
  have hit : ∃ a ∈ C i, w x=some (some a) ∧ G.Adj y a := ⟨v,hv,ox,adj⟩
  rcases mem_union.mp hy with yl|ym
  · apply mem_union_left _
    apply mem_biUnion.mpr ⟨i,hi,?_⟩
    apply mem_union_right _
    apply mem_biUnion.mpr ⟨x,hx,?_⟩
    exact mem_union_left _ (mem_image_of_mem (Sym2.mk x) (mem_filter.mpr ⟨yl,hit⟩))
  · obtain ⟨yh,my⟩ := mem_filter.mp ym
    by_cases yi : y ∈ U i
    · exact same_group_edge G parts C H U L w hi hx yi ne (by simp [ox]) my
    · apply mem_union_left _
      apply mem_biUnion.mpr ⟨i,hi,?_⟩
      apply mem_union_right _
      apply mem_biUnion.mpr ⟨x,hx,?_⟩
      exact mem_union_right _ (mem_image_of_mem (Sym2.mk x)
        (mem_filter.mpr ⟨mem_sdiff.mpr ⟨yh,yi⟩,hit,my⟩))

omit [Fintype V] in
private theorem ordered_pair_edge (G : SimpleGraph V) (parts : Finset ℕ) (C : ℕ → Finset V)
    (H : Finset V) (U : ℕ → Finset V) (L : Finset V) (w : V → Option (Option V))
    {i k : ℕ} (hi : i ∈ parts) (hk : k ∈ parts) (lt : i<k) {x y a b : V}
    (hx : x ∈ U i) (hy : y ∈ U k) (ha : a ∈ C i) (hb : b ∈ C k)
    (ox : w x = some (some a)) (oy : w y = some (some b))
    (adj : G.Adj a b) : s(x,y) ∈ edges G parts C H U L w := by
  apply mem_union_right _
  apply mem_biUnion.mpr ⟨(i,k),mem_filter.mpr ⟨mem_product.mpr ⟨hi,hk⟩,lt⟩,?_⟩
  change s(x,y) ∈ crossEdges G (C i) (C k) (U i) (U k) w
  apply mem_image_of_mem Sym2.mk.uncurry (a := (x,y))
  exact mem_filter.mpr ⟨mem_product.mpr ⟨hx,hy⟩,⟨a,ha,b,hb,ox,oy,adj⟩⟩

omit [Fintype V] in
/-- On an exterior set avoiding the unordered repair edges, every emitted
representative avoids all exterior points, including its sender if that draw
is a valid retry output. Distinct senders' representatives occupy different
rows and are mutually nonadjacent. -/
theorem compatible (G : SimpleGraph V) (parts : Finset ℕ) (C : ℕ → Finset V)
    (H : Finset V) (U : ℕ → Finset V) (L : Finset V) (w : V → Option (Option V))
    (Z : Finset V) (sample : Z ⊆ exterior H L w)
    (avoid : ∀ x ∈ Z, ∀ y ∈ Z, x ≠ y → s(x,y) ∉ edges G parts C H U L w)
    {i : ℕ} (hi : i ∈ parts) {x a : V} (xz : x ∈ Z) (hx : x ∈ U i) (ha : a ∈ C i)
    (ox : w x=some (some a)) (self : ¬G.Adj x a) :
    (∀ y ∈ Z, ¬G.Adj y a) ∧ ∀ k ∈ parts, ∀ y ∈ Z, x ≠ y →
      ∀ b ∈ C k, y ∈ U k → w y=some (some b) → i ≠ k ∧ ¬G.Adj a b := by
  constructor
  · intro y yz
    by_cases n : x=y
    · exact n ▸ self
    · exact fun edge ↦ avoid x xz y yz n
        (incident_edge G parts C H U L w hi hx ha ox (sample yz) n edge)
  · intro k hk y yz xy b hb hy oy
    have ne : i ≠ k := by
      rintro rfl
      exact avoid x xz y yz xy (same_group_edge G parts C H U L w hi hx hy xy (by simp [ox]) (by simp [oy]))
    refine ⟨ne,fun e ↦ ?_⟩
    rcases lt_or_gt_of_ne ne with lt|gt
    · exact avoid x xz y yz xy (ordered_pair_edge G parts C H U L w hi hk lt hx hy ha hb ox oy e)
    · exact avoid y yz x xz xy.symm
        (ordered_pair_edge G parts C H U L w hk hi gt hy hx hb ha oy ox (G.adj_symm e))

end
end Erdos617.RepresentativeRepairs
