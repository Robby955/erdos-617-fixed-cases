import ThirdPruningSelection
import ThirdPruningZero

namespace Erdos617.ThirdPruning
open Finset ColoredLists PackingLists PruningOverlap PruningOverlap.Trace
open scoped Classical
noncomputable section
variable {V : Type*} [Fintype V] {r : ℕ} (T : Trace V r)

private theorem empty_list (A : Finset V) (sub : A ⊆ live T) (i : ℕ) :
    rowList (restrictLive T A) ∅ i = A.filter (fun v ↦ T.row v=i) := by
  unfold rowList available
  rw [restrict_live T A sub]
  ext x; simp [restrictLive]

theorem empty_cliques {A : Finset V} (sub : A ⊆ live T) (data : Lists (restrictLive T A) ∅) :
    ∀ i < r, (targetGraph T.color T.target).IsClique ((A.filter fun v ↦ T.row v=i):Set V) := by
  intro i _
  rw [← empty_list T A sub i]
  exact data.clique i (by simp)

theorem short_row_refund {A : Finset V} (sub : A ⊆ live T) (pr : Pruned T) (hr : 2 ≤ r)
    (order : Fintype.card V=r^2+1) (no : ¬Witness T.color) (data : Lists (restrictLive T A) ∅)
    (i : ℕ) (hi : i < r) :
    let U := restrictLive T A
    deficitSum U ∅+(omittedCount U ∅:ℝ)/400+(liveDef T A i-1/400) ≤ mass T A := by
  let U := restrictLive T A
  let m := rowCard A T.row
  let d := liveDef T A
  let F := shortRows (range r) m (blockSize r)
  let O := ordinaryLists U ∅
  have rp : (0:ℝ)<r := by exact_mod_cast (show 0<r by omega)
  have sizes (i) : (rowList U ∅ i).card = m i := congrArg Finset.card (empty_list T A sub i)
  have defs (i) : rowDeficit U ∅ i = d i := by unfold rowDeficit; rw [sizes]; rfl
  have nF : omittedCount U ∅=F.card := by simp [omittedCount,sizes,F]
  have partition : O = ((range r) \ F) ∩ qualifying U := by simp [O,ordinaryLists,ordinaryRows,sizes,F]
  have dis : Disjoint O F := by rw [partition]; exact sdiff_disjoint.mono_left inter_subset_left
  have un : O ∪ F ⊆ range r := by rw [partition]; exact union_subset (inter_subset_left.trans sdiff_subset) (filter_subset ..)
  have cap := (caps_of_no_witness T.color T.target hr no).2
  have dpos (j) (hj : j ∈ range r) : 0 ≤ d j :=
    sub_nonneg.mpr ((div_le_one rp).mpr (Nat.cast_le.mpr (cap _ (empty_cliques T sub data j (mem_range.mp hj)))))
  have pop : (∑ j ∈ range r, m j) = A.card :=
    (card_eq_sum_card_fiberwise (s:=A) (t:=range r) (f:=T.row) fun x _ ↦ mem_range.mpr (pr.rows x)).symm
  have delta : (∑ j ∈ range r, d j) = mass T A - 1/r := by
    have h := card_sdiff_add_card_eq_card (subset_univ A)
    rw [card_univ,order] at h
    have hc : ((univ \ A).card:ℝ)+A.card=(r:ℝ)^2+1 := by exact_mod_cast h
    change (∑ j ∈ range r, (1-(m j:ℝ)/r)) = _
    rw [sum_sub_distrib,← Finset.sum_div,← Nat.cast_sum,pop,← show ((univ \ A).card:ℝ)/r = mass T A from all_deleted T sub]
    simp only [sum_const,card_range,nsmul_eq_mul,mul_one]
    field_simp; linarith only [hc]
  have allot : (∑ j ∈ O, d j)+(∑ j ∈ F, d j) ≤ mass T A-1/r := by
    rw [← sum_union dis,← delta]; exact sum_le_sum_of_subset_of_nonneg un (fun j h _ ↦ dpos j h)
  have short (j) (hj : j ∈ F) : (1/400:ℝ) ≤ d j := by
    have small : m j < 399*r/400 := (mem_filter.mp hj).2
    have nat : 400*m j ≤ 399*r := by omega
    have cast : (400:ℝ)*m j ≤ 399*r := by exact_mod_cast nat
    change _ ≤ 1-(m j:ℝ)/r
    have ratio : (m j:ℝ)/r ≤ 399/400 := (div_le_iff₀ rp).mpr (by linarith)
    linarith only [ratio]
  change (∑ j ∈ O, rowDeficit U ∅ j)+(omittedCount U ∅:ℝ)/400+(d i-1/400) ≤ mass T A
  rw [nF]; simp_rw [defs]
  by_cases sh : i ∈ F
  · have m := sum_le_sum (s:=F.erase i) (fun j hj ↦ short j (mem_erase.mp hj).2)
    have card := card_erase_add_one sh
    have c : ((F.erase i).card:ℝ)+1=F.card := by exact_mod_cast card
    have sum := sum_erase_add F d sh
    simp only [sum_const,nsmul_eq_mul] at m
    linarith only [c,sum,m,allot,div_nonneg zero_le_one rp.le]
  · have large : 399*r/400 ≤ m i := by
      by_contra! small; exact sh (mem_filter.mpr ⟨mem_range.mpr hi,small⟩)
    have nat : 399*r ≤ 400*(m i+1) := by omega
    have cast : (399:ℝ)*r ≤ 400*((m i:ℝ)+1) := by exact_mod_cast nat
    have floor : d i-1/400 ≤ 1/r := by
      change 1-(m i:ℝ)/r-1/400 ≤ 1/r
      apply le_of_mul_le_mul_right _ rp
      field_simp; linarith only [cast]
    have charge := sum_le_sum (s:=F) short
    simp only [sum_const,nsmul_eq_mul] at charge
    linarith only [allot,charge,floor]

theorem zero_width_deficit {A : Finset V} {Δ : ℕ} {u b α β : ℝ}
    (stage : Stage T A Δ u) (pr : Pruned T) (hr : 2^143 ≤ r)
    (order : Fintype.card V=r^2+1) (no : ¬Witness T.color)
    (data : Lists (restrictLive T A) ∅) (band : RetainedWidth.Band (incidenceCap T) b α β)
    (i : ℕ) (hi : i < r) :
    liveDef T A i-1/400 ≤ thirdRate T A-β*(margin (firstRate T) (secondRate T) b α β+
        (spentFraction T+remaining T-survivingFraction T A)/α) := by
  let U := restrictLive T A
  let K := ordinaryVertices U ∅
  let Q := incidenceCap T-(spentFraction T+remaining T-survivingFraction T A)
  let P := mass T A-(liveDef T A i-1/400)
  have rp : (0:ℝ)<r := by exact_mod_cast (show 0<r by omega)
  have inc := final_incidences T A K (ordinary_kept T A ∅ stage.sub).1 pr.legal
  have cap : incidenceSum U ∅ ≤ Q := by
    rw [incidence_eq]
    apply (div_le_iff₀ (sq_pos_of_pos rp)).mpr
    have eq : Q*(r:ℝ)^2 = (T.crossGraph.edgeFinset.card:ℝ)+edges T.crossGraph A-
        (r:ℝ)/4*T.firstSources.card := by
      dsimp only [Q,incidenceCap,spentFraction,remaining,survivingFraction,firstRate,secondRate]
      field_simp; ring
    rw [eq]; linarith only [inc]
  have ref := short_row_refund T stage.sub pr (by omega) order no data i hi
  change deficitSum U ∅ + (omittedCount U ∅:ℝ)/400 + _ ≤ _ at ref
  have budget : WidthIntegral.RowBudget (ordinaryLists U ∅) (rowDeficit U ∅)
      (rowIncidence U ∅) (omittedCount U ∅) α β (Q/α+P/β) := by
    change incidenceSum U ∅/α+deficitSum U ∅/β ≤ Q/α+P/β-((1/200-1/256)/(2*β))*(omittedCount U ∅)
    unfold P
    cases band <;> linarith only [ref,cap,Nat.cast_nonneg (α:=ℝ) (omittedCount U ∅)]
  have failed := forced_width_cost T stage pr hr order no data band budget
  dsimp only [Q,P,mass,incidenceCap] at failed
  unfold margin
  cases band <;> linarith only [failed]

end
end Erdos617.ThirdPruning
