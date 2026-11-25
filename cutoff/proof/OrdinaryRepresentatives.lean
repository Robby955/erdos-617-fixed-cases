import CountingTransversal
import PrunedWidth

/-! Independent representatives on sublists of the cliques selected by the width theorem. -/

namespace Erdos617.ColoredLists

open Finset PackingLists PruningOverlap Transversal
open scoped Classical
noncomputable section

variable {V : Type*} {r : ℕ} [Fintype V] (T : Trace V r)

private theorem live_unrecorded {x y : V} (hx : x ∈ live T) (hy : y ∈ live T) :
    ¬ T.recorded x y := by
  have ex := (mem_filter.mp hx).2
  have ey := (mem_filter.mp hy).2
  rintro (⟨f,_⟩|⟨f,_⟩)
  · exact (not_lt.mpr ex) (f.trans_le T.stages)
  · exact (not_lt.mpr ey) (f.trans_le T.stages)

private theorem mem_rowList {E : Finset V} {i : ℕ} {x : V} (hx : x ∈ rowList T E i) :
    x ∈ live T ∧ T.row x = i := by
  simp only [rowList,available,mem_filter] at hx
  exact ⟨hx.1,hx.2.1⟩

/-- Every conflicting pair is counted at its first vertex by the original
unrecorded incidence on that row. Both endpoints survived pruning. -/
theorem sublist_conflict_bound (E A : Finset V) (parts : Finset ℕ) (i : ℕ)
    (sub : ∀ x ∈ A, x ∈ rowList T E (T.row x)) :
    ((conflicts (targetGraph T.color T.target) A T.row i (parts.erase i)).card:ℝ) ≤
      ∑ x ∈ rowList T E i, unrecordedDegree T x := by
  let C := conflicts (targetGraph T.color T.target) A T.row i (parts.erase i)
  have ends {u : V × V} (hu : u ∈ C) :
      u.1 ∈ rowList T E i ∧ T.crossGraph.Adj u.1 u.2 ∧ ¬T.recorded u.1 u.2 := by
    obtain ⟨hprod,adj⟩ := mem_filter.mp hu
    obtain ⟨h₁,h₂⟩ := mem_product.mp hprod
    obtain ⟨h₁A,hrow⟩ := mem_filter.mp h₁
    obtain ⟨h₂A,ht⟩ := mem_filter.mp h₂
    have h₁L := sub _ h₁A
    have h₂L := sub _ h₂A
    refine ⟨hrow ▸ h₁L, ?_,live_unrecorded T (mem_rowList T h₁L).1 (mem_rowList T h₂L).1⟩
    rw [← cross_target]
    exact ⟨hrow ▸ (mem_erase.mp ht).1.symm,adj⟩
  have cover : (C:Set (V × V)).MapsTo Prod.fst (rowList T E i) := fun _ h ↦ (ends h).1
  change (C.card:ℝ) ≤ _
  rw [Finset.card_eq_sum_card_fiberwise cover,Nat.cast_sum]
  apply sum_le_sum
  intro x _
  let N := univ.filter fun y ↦ T.crossGraph.Adj x y ∧ ¬T.recorded x y
  have per : (C.filter fun u ↦ u.1 = x).card ≤ N.card := by
    apply card_le_card_of_injOn Prod.snd
    · intro u hu
      obtain ⟨hin,eq⟩ := mem_filter.mp hu
      exact mem_filter.mpr ⟨mem_univ _,eq ▸ (ends hin).2⟩
    · intro u hu v hv same
      exact Prod.ext ((mem_filter.mp hu).2.trans (mem_filter.mp hv).2.symm) same
  have degree : unrecordedDegree T x = N.card := by simp [unrecordedDegree,N]
  rw [degree]
  exact_mod_cast per

variable {E : Finset V} {rows : Finset ℕ} {e n : ℕ} {α β M Y b : ℝ}
  (S : WidthIntegral.Selection rows (rowDeficit T E) (rowIncidence T E) e n α β M)

/-- Arbitrary sublists of size at least r/41 in any retained subfamily admit
independent representatives in the original target graph. -/
theorem retained_representatives (hr : 0 < r) (band : RetainedWidth.Band Y b α β)
    (parts : Finset ℕ) (subset : parts ⊆ S.retained) (A : Finset V)
    (sub : ∀ x ∈ A, x ∈ rowList T E (T.row x))
    (size : ∀ i ∈ parts, (r:ℝ)/41 ≤ (A.filter fun x ↦ T.row x = i).card) :
    ∃ R ⊆ A, Partial (targetGraph T.color T.target) T.row R ∧ R.image T.row = parts := by
  have pos : (0:ℝ) < r := by exact_mod_cast hr
  apply exists_of_row_conflicts _ _ _ _ ((r:ℝ)/41) (by positivity) size
  intro i hi
  have incidence := S.incidence i (subset hi)
  have alpha : α ≤ 656/4000 := by cases band <;> norm_num
  have hα : 0 ≤ α := by cases band <;> norm_num
  have scale : (1120:ℝ) ≤ S.s := by exact_mod_cast S.scale_lo
  have nonneg : 0 ≤ rowIncidence T E i := by unfold rowIncidence unrecordedDegree; positivity
  have paid : rowIncidence T E i ≤ (656/4000)/1120 := by
    linarith only [mul_le_mul_of_nonneg_right scale nonneg,incidence,
      mul_le_mul_of_nonneg_left S.width_lt.le hα,alpha]
  unfold rowIncidence at paid
  have budget := (div_le_iff₀ (sq_pos_of_pos pos)).mp paid
  have bound := sublist_conflict_bound T E A parts i sub
  nlinarith only [bound,budget,sq_nonneg (r:ℝ)]

/-- Exterior vertices with at most (9/40)r/s target neighbors in each
retained clique, including vertices from raw rows that were pruned. -/
def lowExterior (E : Finset V) (parts : Finset ℕ) (s : ℕ) :=
  univ.filter fun x ↦ x ∉ parts.biUnion (rowList T E) ∧ ∀ i ∈ parts,
    (((rowList T E i).filter ((targetGraph T.color T.target).Adj x)).card:ℝ) ≤
      (9/40:ℝ)/s*r

/-- Independent exterior vertices with small attachments have cardinality
at most s−1. A family of s such vertices leaves enough room in each retained
row for an additional independent representative. -/
theorem exterior_independence_cap (hr : 2 ≤ r) (no : ¬Witness T.color)
    (band : RetainedWidth.Band Y b α β) (slots : e+rows.card = r)
    (Z : Finset V) (outside : Z ⊆ lowExterior T E S.retained S.s)
    (independent : (targetGraph T.color T.target).IsIndepSet (Z:Set V)) : Z.card ≤ S.s-1 := by
  let G := targetGraph T.color T.target
  let C := rowList T E
  let K := S.retained.biUnion C
  have sp : 0 < S.s := by have := S.scale_lo; omega
  have pos : (0:ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have spos : (0:ℝ) < S.s := by exact_mod_cast sp
  by_contra! tooMany
  obtain ⟨B,hBZ,hB⟩ := Finset.exists_subset_card_eq (show S.s ≤ Z.card by omega)
  let A := K.filter fun x ↦ ∀ v ∈ B, ¬G.Adj v x
  have inRow {x} (hx : x ∈ K) : x ∈ C (T.row x) := by
    obtain ⟨i,_,hx⟩ := mem_biUnion.mp hx
    rw [(mem_rowList T hx).2]
    exact hx
  have size (i) (hi : i ∈ S.retained) : (r:ℝ)/41 ≤ (A.filter fun x ↦ T.row x=i).card := by
    have βlo : 0 ≤ β := by cases band <;> norm_num
    have βhi : β ≤ 924/4000 := by cases band <;> norm_num
    have dx : rowDeficit T E i ≤ 1/2 := by
      by_cases h : 0 ≤ rowDeficit T E i
      · have sc : (1:ℝ) ≤ S.s := by exact_mod_cast sp
        linarith only [mul_le_mul_of_nonneg_right sc h, S.deficit i hi,
          mul_le_mul_of_nonneg_left S.width_lt.le (show 0 ≤ 2*β by linarith only [βlo]),βhi]
      · linarith only [le_of_not_ge h]
    have whole : (r:ℝ)/2 ≤ (C i).card := by
      change 1-((C i).card:ℝ)/r ≤ 1/2 at dx
      have half : (1/2:ℝ) ≤ ((C i).card:ℝ)/r := by linarith
      linarith only [(le_div_iff₀ pos).mp half]
    let N := fun v ↦ (C i).filter (G.Adj v)
    have lost : ((B.biUnion N).card:ℝ) ≤ (9/40:ℝ)*r := by
      have degree (v) (hv : v ∈ B) : ((N v).card:ℝ) ≤ (9/40:ℝ)/S.s*r :=
        (mem_filter.mp (outside (hBZ hv))).2.2 i hi
      have budget := Finset.sum_le_sum degree
      simp only [sum_const,nsmul_eq_mul,hB] at budget
      have ds : (S.s:ℝ)*((9/40:ℝ)/S.s*r) = (9/40:ℝ)*r := by field_simp
      rw [ds] at budget
      apply le_trans _ budget
      exact_mod_cast (card_biUnion_le (s := B) (t := N))
    have cover : C i ⊆ (A.filter fun x ↦ T.row x=i) ∪ B.biUnion N := by
      intro x hx
      by_cases clean : ∀ v ∈ B, ¬G.Adj v x
      · exact mem_union_left _ (mem_filter.mpr ⟨mem_filter.mpr ⟨mem_biUnion.mpr ⟨i,hi,hx⟩,clean⟩,
          (mem_rowList T hx).2⟩)
      · push Not at clean
        obtain ⟨v,hv,edge⟩ := clean
        exact mem_union_right _ (mem_biUnion.mpr ⟨v,hv,mem_filter.mpr ⟨hx,edge⟩⟩)
    have cov : ((C i).card:ℝ) ≤ (A.filter fun x ↦ T.row x=i).card+((B.biUnion N).card:ℝ) := by
      exact_mod_cast (card_le_card cover).trans (card_union_le ..)
    linarith only [lost,cov,whole,pos]
  obtain ⟨R,sub,rep,im⟩ := retained_representatives T S (by omega) band S.retained
    (by rfl) A (fun x hx ↦ inRow (mem_filter.mp hx).1) size
  have dis : Disjoint B R := disjoint_left.mpr fun x hb hr ↦
    (mem_filter.mp (outside (hBZ hb))).2.1 (mem_filter.mp (sub hr)).1
  have across {x y} (hx : x ∈ B) (hy : y ∈ R) : ¬G.Adj x y := (mem_filter.mp (sub hy)).2 _ hx
  have both : G.IsIndepSet ((B ∪ R : Finset V):Set V) := by
    intro x hx y hy ne
    rcases mem_union.mp hx with hx|hx <;> rcases mem_union.mp hy with hy|hy
    · exact independent (hBZ hx) (hBZ hy) ne
    · exact across hx hy
    · exact fun edge ↦ across hy hx (G.adj_symm edge)
    · exact rep.independent hx hy ne
  have cap := (caps_of_no_witness T.color T.target hr no).1 _ both
  have subRows : S.retained ⊆ rows := by rw [S.retained_eq]; exact (filter_subset ..).trans sdiff_subset
  have total := card_sdiff_add_card_eq_card subRows
  have num := S.omitted
  rw [card_union_of_disjoint dis,hB, ← card_image_of_injOn rep.distinct,im] at cap
  omega

end
end Erdos617.ColoredLists
