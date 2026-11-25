import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Tactic

/-! The enlargement step of Appendix A, §4. The arena can be the entire
coloring or the auxiliary subset of order hr+1. The attachment relation is
measured on the original rows. -/

namespace Erdos617.UniqueAttachment

open Finset
open scoped Classical
noncomputable section

variable {V I : Type*} [DecidableEq V] [DecidableEq I]

def exterior (arena : Finset V) (parts : Finset I) (row : I → Finset V) :=
  arena \ parts.biUnion row

/-- The prescribed sets consist of either one exterior vertex and at most two
representatives of omitted rows, or two exterior vertices. Any subfamily U
with only small attachments from E can be filled independently of E and P.
Only the size and disjointness of the completion are used for enlargement. -/
def CanExtend (G : SimpleGraph V) (arena : Finset V) (parts : Finset I)
    (row : I → Finset V) (large : V → I → Prop) : Prop :=
  ∀ (E P : Finset V) (U : Finset I), E ⊆ exterior arena parts row →
    P ⊆ (parts \ U).biUnion row → U ⊆ parts →
    (E.card = 1 ∧ P.card ≤ 2 ∨ E.card = 2 ∧ P = ∅) →
    G.IsIndepSet ((E ∪ P : Finset V) : Set V) →
    (∀ x ∈ E, ∀ i ∈ U, ¬large x i) →
    ∃ C ⊆ U.biUnion row, C.card = U.card ∧ Disjoint (E ∪ P) C ∧
      G.IsIndepSet (((E ∪ P) ∪ C : Finset V) : Set V)

variable {G : SimpleGraph V} {arena : Finset V} {parts : Finset I}
  {row : I → Finset V} {large : V → I → Prop}

private theorem prescribed_size_bound
    (inside : ∀ i ∈ parts, row i ⊆ arena)
    (cap : ∀ Z ⊆ arena, G.IsIndepSet (Z : Set V) → Z.card ≤ parts.card)
    (extendsRows : CanExtend G arena parts row large)
    (E P : Finset V) (U : Finset I) (ex : E ⊆ exterior arena parts row)
    (rep : P ⊆ (parts \ U).biUnion row) (sub : U ⊆ parts)
    (shape : E.card = 1 ∧ P.card ≤ 2 ∨ E.card = 2 ∧ P = ∅)
    (ind : G.IsIndepSet ((E ∪ P : Finset V) : Set V))
    (small : ∀ x ∈ E, ∀ i ∈ U, ¬large x i) :
    (E ∪ P).card + U.card ≤ parts.card := by
  obtain ⟨C,hC,count,fresh,indC⟩ := extendsRows E P U ex rep sub shape ind small
  have within (ids : Finset I) (h : ids ⊆ parts) : ids.biUnion row ⊆ arena := by
    intro v hv
    obtain ⟨i,hi,rv⟩ := mem_biUnion.mp hv
    exact inside i (h hi) rv
  have allIn : (E ∪ P) ∪ C ⊆ arena := union_subset
    (union_subset (ex.trans (sdiff_subset ..)) (rep.trans (within _ (sdiff_subset ..))))
    (hC.trans (within _ sub))
  simpa only [card_union_of_disjoint fresh,count] using cap _ allIn indC

private theorem independent_pair {x y : V} (nonedge : ¬G.Adj x y) :
    G.IsIndepSet (({x,y} : Finset V) : Set V) := by
  intro a ha b hb ne
  simp only [Finset.coe_insert,Finset.coe_singleton,Set.mem_insert_iff,Set.mem_singleton_iff] at ha hb
  rcases ha with rfl|rfl <;> rcases hb with rfl|rfl
  · exact (ne rfl).elim
  · exact nonedge
  · exact fun e ↦ nonedge (G.adj_symm e)
  · exact (ne rfl).elim

/-- Every exterior point has at least one large row. -/
theorem exists_large (inside : ∀ i ∈ parts, row i ⊆ arena)
    (cap : ∀ Z ⊆ arena, G.IsIndepSet (Z : Set V) → Z.card ≤ parts.card)
    (extendsRows : CanExtend G arena parts row large) {x : V}
    (hx : x ∈ exterior arena parts row) : ∃ i ∈ parts, large x i := by
  by_contra! small
  have bound := prescribed_size_bound inside cap extendsRows {x} ∅ parts
    (singleton_subset_iff.mpr hx) (empty_subset _) (Subset.rfl)
    (Or.inl (by simp)) (by simp)
    (by simpa using small)
  simp at bound

/-- Vertex x has precisely row i as its large attachment among the chosen rows. -/
def Sole (parts : Finset I) (large : V → I → Prop) (x : V) (i : I) : Prop :=
  i ∈ parts ∧ large x i ∧ ∀ j ∈ parts, large x j → j = i

/-- A vertex with exactly one large row is adjacent to every vertex of it. -/
theorem joins_row (inside : ∀ i ∈ parts, row i ⊆ arena)
    (cap : ∀ Z ⊆ arena, G.IsIndepSet (Z : Set V) → Z.card ≤ parts.card)
    (extendsRows : CanExtend G arena parts row large) {x v : V} {i : I}
    (hx : x ∈ exterior arena parts row) (sole : Sole parts large x i)
    (hv : v ∈ row i) : G.Adj x v := by
  by_contra nonedge
  have ne : x ≠ v := fun eq ↦ (mem_sdiff.mp hx).2 (mem_biUnion.mpr ⟨i,sole.1,eq ▸ hv⟩)
  let U := parts.erase i
  have rep : ({v} : Finset V) ⊆ (parts \ U).biUnion row :=
    singleton_subset_iff.mpr (mem_biUnion.mpr ⟨i,mem_sdiff.mpr ⟨sole.1,by simp [U]⟩,hv⟩)
  have bound := prescribed_size_bound inside cap extendsRows {x} {v} U
    (singleton_subset_iff.mpr hx) rep (erase_subset ..) (Or.inl (by simp))
    (by simpa using independent_pair nonedge) (by
      intro a ha j hj e
      have h := mem_erase.mp hj
      exact h.1 (sole.2.2 j h.2 (mem_singleton.mp ha ▸ e)))
  have erased := card_erase_add_one sole.1
  simp [U,ne] at bound
  omega

/-- Distinct exterior vertices assigned to the same unique row are adjacent. -/
theorem assigned_adjacent (inside : ∀ i ∈ parts, row i ⊆ arena)
    (cap : ∀ Z ⊆ arena, G.IsIndepSet (Z : Set V) → Z.card ≤ parts.card)
    (extendsRows : CanExtend G arena parts row large) {x y : V} {i : I}
    (hx : x ∈ exterior arena parts row) (hy : y ∈ exterior arena parts row)
    (sx : Sole parts large x i) (sy : Sole parts large y i) (ne : x ≠ y) : G.Adj x y := by
  by_contra nonedge
  let U := parts.erase i
  have bound := prescribed_size_bound inside cap extendsRows {x,y} ∅ U
    (insert_subset hx (singleton_subset_iff.mpr hy)) (empty_subset _) (erase_subset ..)
    (Or.inr (by simp [ne])) (by simpa using independent_pair nonedge) (by
      intro a ha j hj e
      obtain ⟨ji,jp⟩ := mem_erase.mp hj
      rcases mem_insert.mp ha with rfl|hy'
      · exact ji (sx.2.2 j jp e)
      · exact ji (sy.2.2 j jp (mem_singleton.mp hy' ▸ e)))
  have erased := card_erase_add_one sx.1
  simp [U,ne] at bound
  omega

/-- Enlarge the original row by precisely its uniquely attached exterior vertices. -/
def enlarged (arena : Finset V) (parts : Finset I) (row : I → Finset V)
    (large : V → I → Prop) (i : I) : Finset V :=
  row i ∪ (exterior arena parts row).filter fun x ↦ Sole parts large x i

theorem enlarged_clique (inside : ∀ i ∈ parts, row i ⊆ arena)
    (cap : ∀ Z ⊆ arena, G.IsIndepSet (Z : Set V) → Z.card ≤ parts.card)
    (extendsRows : CanExtend G arena parts row large) {i : I}
    (original : G.IsClique (row i : Set V)) :
    G.IsClique (enlarged arena parts row large i : Set V) := by
  intro x hx y hy ne
  rcases mem_union.mp hx with origX|newX <;> rcases mem_union.mp hy with origY|newY
  · exact original origX origY ne
  · obtain ⟨ey,sy⟩ := mem_filter.mp newY
    exact G.adj_symm (joins_row inside cap extendsRows ey sy origX)
  · obtain ⟨ex,sx⟩ := mem_filter.mp newX
    exact joins_row inside cap extendsRows ex sx origY
  · obtain ⟨ex,sx⟩ := mem_filter.mp newX
    obtain ⟨ey,sy⟩ := mem_filter.mp newY
    exact assigned_adjacent inside cap extendsRows ex ey sx sy ne

omit [DecidableEq I] in
/-- Unique attachment preserves the disjointness of the clique rows. -/
theorem enlarged_disjoint (sep : ∀ i ∈ parts, ∀ j ∈ parts, i ≠ j → Disjoint (row i) (row j))
    {i j : I} (hi : i ∈ parts) (hj : j ∈ parts) (ne : i ≠ j) :
    Disjoint (enlarged arena parts row large i) (enlarged arena parts row large j) := by
  apply disjoint_left.mpr
  intro x hx hy
  rcases mem_union.mp hx with origX|newX <;> rcases mem_union.mp hy with origY|newY
  · exact disjoint_left.mp (sep i hi j hj ne) origX origY
  · exact (mem_sdiff.mp (mem_filter.mp newY).1).2 (mem_biUnion.mpr ⟨i,hi,origX⟩)
  · exact (mem_sdiff.mp (mem_filter.mp newX).1).2 (mem_biUnion.mpr ⟨j,hj,origY⟩)
  · exact ne ((mem_filter.mp newY).2.2.2 i hi (mem_filter.mp newX).2.2.1)

/-- An exterior point left after enlargement has at least two distinct large
attachments, measured on the original rows. -/
theorem two_large_of_remaining (inside : ∀ i ∈ parts, row i ⊆ arena)
    (cap : ∀ Z ⊆ arena, G.IsIndepSet (Z : Set V) → Z.card ≤ parts.card)
    (extendsRows : CanExtend G arena parts row large) {x : V}
    (hx : x ∈ exterior arena parts (enlarged arena parts row large)) :
    ∃ i ∈ parts, ∃ j ∈ parts, i ≠ j ∧ large x i ∧ large x j := by
  obtain ⟨ha,remain⟩ := mem_sdiff.mp hx
  have ex : x ∈ exterior arena parts row := mem_sdiff.mpr ⟨ha,by
    intro covered
    obtain ⟨i,hi,rv⟩ := mem_biUnion.mp covered
    exact remain (mem_biUnion.mpr ⟨i,hi,mem_union_left _ rv⟩)⟩
  obtain ⟨i,hi,ix⟩ := exists_large inside cap extendsRows ex
  by_contra none
  have sole : Sole parts large x i := ⟨hi,ix,by
    intro j hj jx
    by_contra ji
    exact none ⟨i,hi,j,hj,Ne.symm ji,ix,jx⟩⟩
  exact remain (mem_biUnion.mpr ⟨i,hi,mem_union_right _ (mem_filter.mpr ⟨ex,sole⟩)⟩)

/-- The enlarged deficits in vertices sum to exactly one less than the number
of exterior vertices that remain. The clique size cap is used here to justify
natural-number subtraction row by row. -/
theorem enlarged_deficit_sum {r : ℕ} (order : arena.card = parts.card*r+1)
    (inside : ∀ i ∈ parts, row i ⊆ arena)
    (sep : ∀ i ∈ parts, ∀ j ∈ parts, i ≠ j → Disjoint (row i) (row j))
    (cliques : ∀ i ∈ parts, G.IsClique (row i : Set V))
    (indCap : ∀ Z ⊆ arena, G.IsIndepSet (Z : Set V) → Z.card ≤ parts.card)
    (cliqueCap : ∀ C ⊆ arena, G.IsClique (C : Set V) → C.card ≤ r)
    (extendsRows : CanExtend G arena parts row large) :
    (∑ i ∈ parts, (r - (enlarged arena parts row large i).card))+1 =
      (exterior arena parts (enlarged arena parts row large)).card := by
  let F := enlarged arena parts row large
  have rowIn (i) (hi : i ∈ parts) : F i ⊆ arena :=
    union_subset (inside i hi) ((filter_subset ..).trans (sdiff_subset ..))
  have uni : parts.biUnion F ⊆ arena := by
    intro v hv
    obtain ⟨i,hi,hv⟩ := mem_biUnion.mp hv
    exact rowIn i hi hv
  have sizes (i) (hi : i ∈ parts) : (F i).card ≤ r :=
    cliqueCap _ (rowIn i hi) (enlarged_clique inside indCap extendsRows (cliques i hi))
  have fill : (∑ i ∈ parts, (r - (F i).card))+(∑ i ∈ parts, (F i).card) = parts.card*r := by
    rw [← sum_add_distrib]
    calc
      _ = ∑ _i ∈ parts, r := sum_congr rfl fun i hi ↦ Nat.sub_add_cancel (sizes i hi)
      _ = _ := by simp
  have pairwise : (parts : Set I).PairwiseDisjoint F :=
    fun i hi j hj ne ↦ enlarged_disjoint sep hi hj ne
  have allCount := card_sdiff_add_card_eq_card uni
  rw [card_biUnion pairwise] at allCount
  change (∑ i ∈ parts, (r - (F i).card)) + 1 = (arena \ parts.biUnion F).card
  omega

/-- An exterior point with precisely two possible large rows forces a complete
target-color rectangle between its nonneighbors in those rows. A missing edge
would supply three prescribed vertices while only two rows are omitted. -/
theorem two_row_rectangle (inside : ∀ i ∈ parts, row i ⊆ arena)
    (sep : ∀ i ∈ parts, ∀ j ∈ parts, i ≠ j → Disjoint (row i) (row j))
    (cap : ∀ Z ⊆ arena, G.IsIndepSet (Z:Set V) → Z.card ≤ parts.card)
    (extendRows : CanExtend G arena parts row large) {x : V}
    (hx : x ∈ exterior arena parts row) {i j : I} (hi : i ∈ parts) (hj : j ∈ parts)
    (ne : i ≠ j) (onlyTwo : ∀ k ∈ parts, large x k → k = i ∨ k = j)
    {a b : V} (ha : a ∈ row i) (hb : b ∈ row j) (xa : ¬G.Adj x a) (xb : ¬G.Adj x b) :
    G.Adj a b := by
  by_contra ab
  let U := parts \ {i,j}
  have ij : ({i,j} : Finset I) ⊆ parts := by
    intro k hk
    rcases mem_insert.mp hk with rfl|one
    · exact hi
    · exact mem_singleton.mp one ▸ hj
  have a_ne_b : a ≠ b := fun eq ↦ disjoint_left.mp (sep i hi j hj ne) ha (eq ▸ hb)
  have xout : x ∉ ({a,b} : Finset V) := by
    intro mem
    rcases mem_insert.mp mem with rfl|one
    · exact (mem_sdiff.mp hx).2 (mem_biUnion.mpr ⟨i,hi,ha⟩)
    · exact (mem_sdiff.mp hx).2 (mem_biUnion.mpr ⟨j,hj,mem_singleton.mp one ▸ hb⟩)
  have omitted {k : I} (hit : k ∈ ({i,j} : Finset I)) : k ∈ parts \ U :=
    mem_sdiff.mpr ⟨ij hit,fun hu ↦ (mem_sdiff.mp hu).2 hit⟩
  have reps : ({a,b}:Finset V) ⊆ (parts \ U).biUnion row := by
    intro v hv
    rcases mem_insert.mp hv with rfl | one
    · exact mem_biUnion.mpr ⟨i,omitted (by simp),ha⟩
    · exact mem_biUnion.mpr ⟨j,omitted (by simp),mem_singleton.mp one ▸ hb⟩
  have ind : G.IsIndepSet (({x} ∪ {a,b} : Finset V) : Set V) := by
    intro v hv w hw diff
    have pair := independent_pair ab
    rcases mem_union.mp hv with vx|vp <;> rcases mem_union.mp hw with wx|wp
    · exact (diff ((mem_singleton.mp vx).trans (mem_singleton.mp wx).symm)).elim
    · rw [mem_singleton.mp vx]
      rcases mem_insert.mp wp with rfl|one
      · exact xa
      · exact mem_singleton.mp one ▸ xb
    · rw [mem_singleton.mp wx]
      rcases mem_insert.mp vp with rfl|one
      · exact fun edge ↦ xa (G.adj_symm edge)
      · exact fun edge ↦ xb (mem_singleton.mp one ▸ G.adj_symm edge)
    · exact pair vp wp diff
  have small : ∀ y ∈ ({x} : Finset V), ∀ k ∈ U, ¬large y k := by
    intro y hy k hk big
    obtain ⟨kp,out⟩ := mem_sdiff.mp hk
    rcases onlyTwo k kp (mem_singleton.mp hy ▸ big) with rfl|rfl <;> simp at out
  have bound := prescribed_size_bound inside cap extendRows {x} {a,b} U
    (by simpa using hx) reps sdiff_subset (Or.inl (by simp [a_ne_b])) ind small
  have count := card_sdiff_add_card_eq_card ij
  have two : ({i,j}:Finset I).card = 2 := by simp [ne]
  have three : ({x} ∪ {a,b} : Finset V).card = 3 := by
    rw [singleton_union,card_insert_of_notMem xout,card_pair a_ne_b]
  rw [three] at bound
  change U.card + _ = _ at count
  omega

end
end Erdos617.UniqueAttachment
