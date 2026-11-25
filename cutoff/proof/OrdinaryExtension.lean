import OrdinaryRepresentatives
import OrdinaryTrim

/-! Prescribed vertices extend across the ordinary rows in Appendix A §4. -/

namespace Erdos617.ColoredLists

open Finset PackingLists PruningOverlap Transversal
open scoped Classical
noncomputable section

variable {V : Type*} {r : ℕ} [Fintype V] (T : Trace V r)

private theorem row_label {E : Finset V} {i : ℕ} {x : V}
    (mem : x ∈ rowList T E i) : T.row x = i := by
  simp only [rowList, available, mem_filter] at mem
  exact mem.2.1

omit [Fintype V] in
private theorem covered_neighbors {H : SimpleGraph V} (F C : Finset V) {d : ℝ}
    (degree : ∀ v ∈ F, ((C.filter (H.Adj v)).card : ℝ) ≤ d) :
    ((F.biUnion fun v ↦ C.filter (H.Adj v)).card : ℝ) ≤ F.card * d := by
  have bound := sum_le_sum degree
  simp only [sum_const, nsmul_eq_mul] at bound
  apply le_trans _ bound
  exact_mod_cast card_biUnion_le (s := F) (t := fun v ↦ C.filter (H.Adj v))

/-- Fill any subfamily of retained ordinary rows while preserving the prescribed
independent set. P consists of exterior points, Q of auxiliary representatives
and D of representatives already fixed in other temporary ordinary rows. -/
theorem extend_prescribed_ordinary (prep : Prepared T) (hr : 0 < r)
    {E : Finset V} {e n : ℕ} {α β M Y b : ℝ}
    (S : WidthIntegral.Selection (ordinaryLists T E) (rowDeficit T E) (rowIncidence T E)
      e n α β M)
    (band : RetainedWidth.Band Y b α β)
    (parts : Finset ℕ) (sub : parts ⊆ S.retained)
    (P Q D : Finset V)
    (outside : Disjoint P (parts.biUnion (temporaryRow T E)))
    (small : ∀ x ∈ P, ∀ i ∈ parts,
      (((temporaryRow T E i).filter ((targetGraph T.color T.target).Adj x)).card : ℝ)
        ≤ (369/1000 : ℝ)*r)
    (aux : Q ⊆ lowExterior T E S.retained S.s) (auxSize : Q.card ≤ S.s)
    (ordinary : ∀ x ∈ D, ∃ j ∈ S.retained, j ∉ parts ∧ x ∈ temporaryRow T E j)
    (cases : (P.card ≤ 2 ∧ D = ∅) ∨ (P.card ≤ 1 ∧ D.card ≤ 2))
    (indep : (targetGraph T.color T.target).IsIndepSet ((P ∪ Q ∪ D : Finset V) : Set V)) :
    ∃ R ⊆ parts.biUnion (temporaryRow T E),
      Partial (targetGraph T.color T.target) T.row R ∧ R.image T.row = parts ∧
      Disjoint (P ∪ Q ∪ D) R ∧
      (targetGraph T.color T.target).IsIndepSet ((P ∪ Q ∪ D ∪ R : Finset V) : Set V) := by
  let G := targetGraph T.color T.target
  let K := parts.biUnion (temporaryRow T E)
  let B := P ∪ Q ∪ D
  let A := K.filter fun x ↦ ∀ v ∈ B, ¬G.Adj v x
  have pos : (0 : ℝ) < r := by exact_mod_cast hr
  have spos : (0 : ℝ) < S.s := by exact_mod_cast (show 0 < S.s by have := S.scale_lo; omega)
  have inRow {x} (h : x ∈ K) : x ∈ rowList T E (T.row x) := by
    obtain ⟨i,_,mem⟩ := mem_biUnion.mp h
    have orig := (mem_filter.mp mem).1
    exact (row_label T orig).symm ▸ orig
  have size (i) (hi : i ∈ parts) : (r : ℝ)/41 ≤ (A.filter fun x ↦ T.row x = i).card := by
    let C := temporaryRow T E i
    let N := fun v ↦ C.filter (G.Adj v)
    have cover : C ⊆ (A.filter fun x ↦ T.row x = i) ∪
        (P.biUnion N ∪ Q.biUnion N ∪ D.biUnion N) := by
      intro x hx
      by_cases clean : ∀ v ∈ B, ¬G.Adj v x
      · exact mem_union_left _ (mem_filter.mpr ⟨mem_filter.mpr
          ⟨mem_biUnion.mpr ⟨i,hi,hx⟩,clean⟩,row_label T (mem_filter.mp hx).1⟩)
      · push Not at clean
        obtain ⟨v,hv,edge⟩ := clean
        have hn : x ∈ N v := mem_filter.mpr ⟨hx,edge⟩
        apply mem_union_right
        rcases mem_union.mp hv with vPQ | vD
        · apply mem_union_left
          rcases mem_union.mp vPQ with vP | vQ
          · exact mem_union_left _ (mem_biUnion.mpr ⟨v,vP,hn⟩)
          · exact mem_union_right _ (mem_biUnion.mpr ⟨v,vQ,hn⟩)
        · exact mem_union_right _ (mem_biUnion.mpr ⟨v,vD,hn⟩)
    have cov : (C.card : ℝ) ≤ (A.filter fun x ↦ T.row x = i).card +
        ((P.biUnion N).card + (Q.biUnion N).card + (D.biUnion N).card : ℝ) := by
      exact_mod_cast (card_le_card cover).trans ((card_union_le ..).trans
        (Nat.add_le_add_left ((card_union_le ..).trans (Nat.add_le_add_right (card_union_le ..) _)) _))
    have pCost := covered_neighbors (H := G) P C (fun v hv ↦ small v hv i hi)
    have qCost := covered_neighbors (H := G) Q C (d := (9/40:ℝ)/S.s*r) (by
      intro v hv
      have h := (mem_filter.mp (aux hv)).2.2 i (sub hi)
      apply le_trans _ h
      exact_mod_cast card_le_card (filter_subset_filter _ (show C ⊆ rowList T E i from filter_subset ..)))
    have qcard : (Q.card : ℝ) ≤ S.s := by exact_mod_cast auxSize
    have qlim := mul_le_mul_of_nonneg_right qcard (show 0 ≤ (9/40:ℝ)/S.s*r by positivity)
    have simpQ : (S.s:ℝ)*((9/40:ℝ)/S.s*r) = (9/40:ℝ)*r := by field_simp
    rw [simpQ] at qlim
    have dCost := covered_neighbors (H := G) D C (d := (7/50:ℝ)*r) (by
      intro v hv
      obtain ⟨j,jr,jout,hv⟩ := ordinary v hv
      apply le_trans _ ((temporary_row_bounds T prep hr E band S jr).2 _ hv).le
      apply Nat.cast_le.mpr (card_le_card ?_)
      intro x hx
      obtain ⟨hxC,adj⟩ := mem_filter.mp hx
      apply mem_filter.mpr
      refine ⟨mem_univ _,adj,fun hxj ↦ jout ?_⟩
      rwa [← row_label T hxj, row_label T (mem_filter.mp hxC).1])
    have total := (temporary_row_bounds T prep hr E band S (sub hi)).1
    change (255/256:ℝ)*r ≤ C.card at total
    change ((P.biUnion N).card:ℝ) ≤ P.card*((369/1000:ℝ)*r) at pCost
    change ((Q.biUnion N).card:ℝ) ≤ Q.card*((9/40:ℝ)/S.s*r) at qCost
    change ((D.biUnion N).card:ℝ) ≤ D.card*((7/50:ℝ)*r) at dCost
    rcases cases with ⟨p,d⟩ | ⟨p,d⟩
    · have pCap : (P.card:ℝ) ≤ 2 := by exact_mod_cast p
      have dZero : (D.card : ℝ) = 0 := by simp [d]
      rw [dZero,zero_mul] at dCost
      linarith only [total,cov,pCost,qCost.trans qlim,dCost,pos,
        mul_le_mul_of_nonneg_right pCap (show 0 ≤ (369/1000:ℝ)*r by positivity)]
    · have pCap : (P.card:ℝ) ≤ 1 := by exact_mod_cast p
      have dCap : (D.card:ℝ) ≤ 2 := by exact_mod_cast d
      linarith only [total,cov,pCost,qCost.trans qlim,dCost,pos,
        mul_le_mul_of_nonneg_right pCap (show 0 ≤ (369/1000:ℝ)*r by positivity),
        mul_le_mul_of_nonneg_right dCap (show 0 ≤ (7/50:ℝ)*r by positivity)]
  obtain ⟨R,hRA,rep,im⟩ := retained_representatives T S hr band parts sub A
    (fun _ hx ↦ inRow (mem_filter.mp hx).1) size
  have hRK : R ⊆ K := hRA.trans (filter_subset ..)
  have dis : Disjoint B R := by
    apply disjoint_left.mpr
    intro x hxB hxR
    obtain ⟨i,hi,hxi⟩ := mem_biUnion.mp (hRK hxR)
    have hxi' := (mem_filter.mp hxi).1
    rcases mem_union.mp hxB with hPQ | hD
    · rcases mem_union.mp hPQ with hP | hQ
      · exact disjoint_left.mp outside hP (hRK hxR)
      · exact (mem_filter.mp (aux hQ)).2.1 (mem_biUnion.mpr ⟨i,sub hi,hxi'⟩)
    · obtain ⟨j,_,out,hxj⟩ := ordinary x hD
      exact out ((row_label T (mem_filter.mp hxj).1) ▸ ((row_label T hxi').symm ▸ hi))
  refine ⟨R,hRK,rep,im,dis,?_⟩
  intro x hx y hy ne
  rcases mem_union.mp hx with hx | hx <;> rcases mem_union.mp hy with hy | hy
  · exact indep hx hy ne
  · exact (mem_filter.mp (hRA hy)).2 _ hx
  · exact fun edge ↦ (mem_filter.mp (hRA hx)).2 _ hy (G.adj_symm edge)
  · exact rep.independent hx hy ne

end
end Erdos617.ColoredLists
