import ExteriorAuxiliary
import AuxiliaryPeeling
import AuxiliaryRowFloor
import SublistEdges

/-! Auxiliary survivors form target cliques under the exterior square budget. -/

namespace Erdos617.ColoredLists

open Finset RowExtraction PackingLists PruningOverlap Transversal GraphPartitionCount
open scoped Classical
noncomputable section

variable {W : Type*} (G : SimpleGraph W) (row : W → ℕ)

private theorem add_independent (x : W) (R : Finset W) (h : G.IsIndepSet (R:Set W))
    (avoid : ∀ u ∈ R, ¬G.Adj x u) : G.IsIndepSet ((insert x R:Finset W):Set W) := by
  intro u hu v hv ne
  obtain eu | huR := mem_insert.mp hu
  · subst u
    obtain ev | hvR := mem_insert.mp hv
    · exact (ne ev.symm).elim
    · exact avoid _ hvR
  · obtain ev | hvR := mem_insert.mp hv
    · subst v
      exact fun edge ↦ avoid _ huR (G.adj_symm edge)
    · exact h huR hvR ne

/-- A nonedge in a surviving row would extend to an independent set of h+1
vertices using one representative in every other row. -/
theorem surviving_auxiliary_cliques (A : Finset W) (h r : ℕ) (hr : 0 < r)
    (cap : ∀ Z : Finset W, G.IsIndepSet (Z:Set W) → Z.card ≤ h)
    (floor : ∀ i < h, (21/25:ℝ)*r ≤ (fiber A row i).card)
    (degree : ∀ x ∈ A, (((A.filter ((cross G row).Adj x)).card):ℝ) ≤ (43/200:ℝ)*r)
    (edgeCap : ∀ L ⊆ A, ∀ i (parts : Finset ℕ),
      4*((conflicts G L row i (parts.erase i)).card:ℝ) ≤ (2*(r:ℝ)/5)^2)
    (i : ℕ) (hi : i < h) : G.IsClique (fiber A row i:Set W) := by
  intro x hx y hy ne
  by_contra nonedge
  have pos : (0:ℝ) < r := by exact_mod_cast hr
  obtain ⟨hxA,hxi⟩ := mem_filter.mp hx
  obtain ⟨hyA,hyi⟩ := mem_filter.mp hy
  let L := A.filter fun v ↦ row v ≠ i ∧ ¬G.Adj x v ∧ ¬G.Adj y v
  let N := fun v ↦ A.filter ((cross G row).Adj v)
  let parts := (range h).erase i
  have large (k) (hk : k ∈ parts) : 2*(r:ℝ)/5 ≤ (L.filter fun v ↦ row v = k).card := by
    obtain ⟨ki,kh⟩ := mem_erase.mp hk
    have cover : fiber A row k ⊆ (L.filter fun v ↦ row v = k) ∪ (N x ∪ N y) := by
      intro u hu
      obtain ⟨hua,eq⟩ := mem_filter.mp hu
      have diff : row u ≠ i := eq ▸ ki
      by_cases ex : G.Adj x u
      · exact mem_union_right _ (mem_union_left _ (mem_filter.mpr ⟨hua,hxi ▸ diff.symm,ex⟩))
      by_cases ey : G.Adj y u
      · exact mem_union_right _ (mem_union_right _ (mem_filter.mpr ⟨hua,hyi ▸ diff.symm,ey⟩))
      exact mem_union_left _ (mem_filter.mpr ⟨mem_filter.mpr ⟨hua,diff,ex,ey⟩,eq⟩)
    have hn := (card_le_card cover).trans ((card_union_le ..).trans
      (Nat.add_le_add_left (card_union_le ..) _))
    have count : ((fiber A row k).card:ℝ) ≤ (L.filter fun u ↦ row u=k).card+
        (((N x).card:ℝ)+(N y).card) := by exact_mod_cast hn
    have dx : ((N x).card:ℝ) ≤ (43/200:ℝ)*r := degree x hxA
    have dy : ((N y).card:ℝ) ≤ (43/200:ℝ)*r := degree y hyA
    linarith only [count,floor k (mem_range.mp kh),dx,dy,pos]
  obtain ⟨R,sub,rep,im⟩ := exists_of_row_conflicts G L row parts (2*(r:ℝ)/5)
    (by positivity) large (fun k _ ↦ edgeCap L (filter_subset ..) k parts)
  have fresh_x : x ∉ R := fun hxR ↦ (mem_filter.mp (sub hxR)).2.1 hxi
  have fresh_y : y ∉ R := fun hyR ↦ (mem_filter.mp (sub hyR)).2.1 hyi
  have ry := add_independent G y R rep.independent fun z hz ↦ (mem_filter.mp (sub hz)).2.2.2
  have rxy := add_independent G x (insert y R) ry (by
    intro z hz
    rcases mem_insert.mp hz with rfl|hz
    · exact nonedge
    · exact (mem_filter.mp (sub hz)).2.2.1)
  have contradiction :=  cap _ rxy
  rw [card_insert_of_notMem (show x ∉ insert y R by simpa [ne] using fresh_x),
    card_insert_of_notMem fresh_y, ← card_image_of_injOn rep.distinct,im] at contradiction
  have erased : parts.card = h-1 := by simp [parts,card_erase_of_mem (mem_range.mpr hi)]
  omega

variable [Fintype W]

/-- The residual edge budget and all h cliques refer to the same set A of
survivors. The lower bound applies even to row labels padded by the partition. -/
structure AuxiliarySurvivors (h r : ℕ) (A : Finset W) : Prop where
  degree : ∀ x ∈ A, ((A.filter ((cross G row).Adj x)).card:ℝ) ≤ (43/200:ℝ)*r
  residual : (((cross G row).induce (A:Set W)).edgeFinset.card:ℝ) +
    (43/200:ℝ)*r*((Fintype.card W:ℝ)-A.card) ≤ ((cross G row).edgeFinset.card:ℝ)
  rows : ∀ i < h, (fiber A row i).Nonempty ∧ G.IsClique (fiber A row i:Set W) ∧
    (21/25:ℝ)*r ≤ (fiber A row i).card

/-- Peeling the auxiliary partition yields a nonempty clique in each of the
h rows and preserves the residual cross-edge budget. -/
theorem exists_surviving_auxiliary_cliques (h r : ℕ) (hr : 0 < r)
    (cap : ∀ Z : Finset W, G.IsIndepSet (Z:Set W) → Z.card ≤ h)
    (budget : ((cross G row).edgeFinset.card:ℝ)/(r:ℝ)^2 +
      (∑ i ∈ range h, (max (1-(size row i:ℝ)/r) 0)^2) ≤ (3/20:ℝ)^2+1/2^20) :
    ∃ A : Finset W, AuxiliarySurvivors G row h r A := by
  have pos : (0:ℝ) < r := by exact_mod_cast hr
  obtain ⟨A,degree,residual⟩ := AuxiliaryPeeling.exists_live (cross G row) ((43/200:ℝ)*r)
  have paid : (43/200:ℝ)*r*((Fintype.card W:ℝ)-A.card) ≤ ((cross G row).edgeFinset.card:ℝ) :=
    (le_add_of_nonneg_left (Nat.cast_nonneg _)).trans residual
  have floor := AuxiliaryMoments.live_row_floor G row A h r hr budget paid
  have edges : ((cross G row).edgeFinset.card:ℝ) ≤ ((3/20:ℝ)^2+1/2^20)*(r:ℝ)^2 := by
    apply (div_le_iff₀ (sq_pos_of_pos pos)).mp
    apply le_trans _ budget
    exact le_add_of_nonneg_right (sum_nonneg fun i _ ↦ sq_nonneg _)
  have conflicts (L : Finset W) (_sub : L ⊆ A) (i : ℕ) (parts : Finset ℕ) :
      4*((conflicts G L row i (parts.erase i)).card:ℝ) ≤ (2*(r:ℝ)/5)^2 := by
    have small := conflicts_le_cross_edges G L row i parts
    have bound : ((Transversal.conflicts G L row i (parts.erase i)).card:ℝ) ≤
        ((cross G row).edgeFinset.card:ℝ) := by exact_mod_cast small
    nlinarith only [bound,edges,sq_nonneg (r:ℝ)]
  refine ⟨A,degree,residual,?_⟩
  intro i hi
  have lower := floor i hi
  have ne : 0 < (fiber A row i).card := by
    exact_mod_cast lt_of_lt_of_le (show 0 < (21/25:ℝ)*r by positivity) lower
  exact ⟨card_pos.mp ne,surviving_auxiliary_cliques G row A h r hr cap floor degree conflicts i hi,lower⟩

variable {V : Type*} {r : ℕ} [Fintype V] (T : Trace V r)

/-- On the actual induced coloring used under failure of the exterior
shortage, choose the auxiliary vertices, their raw partition and the peeled
cliques while keeping all the counts on that same partition. -/
theorem auxiliary_cliques_of_failed_shortage {E : Finset V} {rows : Finset ℕ} {e n : ℕ}
    {α β M Y exp : ℝ}
    (S : WidthIntegral.Selection rows (rowDeficit T E) (rowIncidence T E) e n α β M)
    (hr : 2 ≤ r) (no : ¬Witness T.color) (band : RetainedWidth.Band Y exp α β)
    (scale : (2:ℝ)^exp*(S.s:ℝ)^4 < r) (slots : e+rows.card = r)
    (fail : ((S.s-1:ℕ):ℝ)*r-((lowExterior T E S.retained S.s).card:ℝ) ≤ (3/20:ℝ)*r) :
    ∃ B ⊆ lowExterior T E S.retained S.s,
      B.card = min (lowExterior T E S.retained S.s).card ((S.s-1)*r+1) ∧
      (-(3/20:ℝ)*r ≤ (B.card:ℝ)-((S.s-1:ℕ):ℝ)*r ∧ (B.card:ℝ)-((S.s-1:ℕ):ℝ)*r ≤ 1) ∧
      ¬Witness (inducedColor T.color B) ∧ ∃ row, AuxiliaryPartition T S.s B row ∧
        ∃ A : Finset B, AuxiliarySurvivors (targetGraph (inducedColor T.color B) T.target) row (S.s-1) r A := by
  obtain ⟨B,sub,count,bounds,noB,row,part⟩ := auxiliary_of_failed_shortage T S hr no band scale slots fail
  exact ⟨B,sub,count,bounds,noB,row,part,exists_surviving_auxiliary_cliques _ _ _ _ (by omega)
    (induced_exterior_cap T S hr no band slots B sub) part.normalized⟩

end
end Erdos617.ColoredLists
