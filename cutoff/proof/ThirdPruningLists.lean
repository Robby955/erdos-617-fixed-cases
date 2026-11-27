import ThirdPruningData

/-! Deficits of the lists constructed from the original or the third pass. -/
namespace Erdos617.ThirdPruning
open Finset ColoredLists PackingLists PruningOverlap PruningOverlap.Trace
open scoped Classical
noncomputable section
variable {V : Type*} [Fintype V] {r : ℕ} (T : Trace V r)

abbrev Lists (E : Finset V) := ListBounds (targetGraph T.color T.target) T.row
    univ (live T) (range r) (qualifying T) E r
def deficitSum (E : Finset V) := ∑ i ∈ ordinaryLists T E, rowDeficit T E i
def incidenceSum (E : Finset V) := ∑ i ∈ ordinaryLists T E, rowIncidence T E i
def ordinaryVertices (E : Finset V) := (ordinaryLists T E).biUnion (rowList T E)
def mass (A : Finset V) := firstRate T+secondRate T+thirdRate T A

structure Stage (A : Finset V) (Δ : ℕ) (u : ℝ) : Prop where
  sub : A ⊆ live T
  removed : ∀ x ∈ live T \ A, (9/25:ℝ)*r ≤ deg T.crossGraph (live T) x
  degree : ∀ x ∈ A, (Transversal.neighbors T.crossGraph A x).card ≤ Δ
  small : Δ ≤ degreeBound r
  rate : (Δ:ℝ) ≤ u*r
  le_tau : u ≤ 199/400
  total : mass T A < 353/100
  paired : mass T A+1/2-(398/400-2*u) < 353/100

theorem Stage.lists {A : Finset V} {Δ : ℕ} {u : ℝ} (stage : Stage T A Δ u) (pr : Pruned T)
    (hr : 2 ≤ r) (order : Fintype.card V = r^2+1) (no : ¬Witness T.color) :
    ∃ E, Lists (restrictLive T A) E := by
  let U := restrictLive T A
  apply (witness_or_lists U (qualifying U) hr order pr.rows ?_).resolve_left no
  rw [restrict_live T A stage.sub]
  exact fun x hx ↦ (stage.degree x hx).trans stage.small

theorem refined_deficit {A E : Finset V} {Δ : ℕ} {u : ℝ} (stage : Stage T A Δ u) (pr : Pruned T)
    (hr : 2 ≤ r) (order : Fintype.card V=r^2+1) (no : ¬Witness T.color)
    (data : Lists (restrictLive T A) E) :
    let U := restrictLive T A
    deficitSum U E + (omittedCount U E:ℝ)/400 + (398/400-2*u)*(E.image T.row).card ≤
      mass T A + chosenExcess A T.row E r - 1/r := by
  let U := restrictLive T A
  have same : live U=A := restrict_live T A stage.sub
  have degOK : ∀ v ∈ live U, (Transversal.neighbors (cross (targetGraph U.color U.target) U.row) (live U) v).card ≤ Δ := by
    rw [same,cross_target U]; exact stage.degree
  have bound := budget_at_degree (targetGraph U.color U.target) U.row univ (live U) (range r) (qualifying U) E r Δ hr (by simpa using order) (subset_univ _)
    (card_range r) data.selected data.packing data.clique data.missing
    (fun v _ ↦ mem_range.mpr (pr.rows v)) (caps_of_no_witness T.color T.target hr no).2 degOK u stage.rate
  have eq : mass T A = ((univ \ A).card:ℝ)/r := (all_deleted T stage.sub).symm
  change deficitSum U E + (omittedCount U E:ℝ)/400 + _ ≤ _
  rw [eq,← same]
  dsimp only at bound
  simp only [omittedCount,Nat.cast_add,deficitSum,ordinaryLists,rowDeficit,rowList,deficit]
  convert! bound using 1


theorem deficit_nonneg {E : Finset V} (hr : 2 ≤ r) (no : ¬Witness T.color) (data : Lists T E)
    (i : ℕ) (hi : i ∈ ordinaryLists T E) : 0 ≤ rowDeficit T E i := by
  have cap := (caps_of_no_witness T.color T.target hr no).2 _ (data.clique i (mem_sdiff.mp
    (mem_sdiff.mp (mem_inter.mp hi).1).1).2)
  apply sub_nonneg.mpr
  apply (div_le_one (by exact_mod_cast (show 0<r by omega))).mpr
  exact_mod_cast cap

theorem deficit_count_cap {A E : Finset V} {Δ : ℕ} {u : ℝ} (stage : Stage T A Δ u) (pr : Pruned T)
    (hr : 2 ≤ r) (order : Fintype.card V=r^2+1) (no : ¬Witness T.color)
    (data : Lists (restrictLive T A) E) :
    let U := restrictLive T A
    deficitSum U E < 353/100 ∧ omittedCount U E ≤ 1411 := by
  let U := restrictLive T A
  let q := (E.image T.row).card
  have budget := refined_deficit T stage pr hr order no data
  have sizes := (global_raw_budgets T hr order pr.rows pr.least pr.pivots no).1
  have into : E.image T.row ⊆ range r := by
    intro i hi; obtain ⟨x,_,rfl⟩ := mem_image.mp hi; exact mem_range.mpr (pr.rows x)
  have excess : chosenExcess A T.row E r ≤ 1/2 := by
    have h := (chosen_le_surplus univ A T.row (range r) (E.image T.row) r (subset_univ _) into).trans sizes
    unfold chosenExcess
    change ((verticesIn A T.row (E.image T.row)).card:ℝ)/r-_ ≤ _
    rw [card_verticesIn,Nat.cast_sum,Finset.sum_div]
    simpa [sum_sub_distrib] using h
  have pos : (0:ℝ)<r := by exact_mod_cast (show 0<r by omega)
  have inv : 0 ≤ 1/(r:ℝ) := by positivity
  change deficitSum U E+(omittedCount U E:ℝ)/400+(398/400-2*u)*q ≤ _ at budget
  have total : deficitSum U E+(omittedCount U E:ℝ)/400 < 353/100 := by
    by_cases empty : E=∅
    · subst E
      have zero : chosenExcess A T.row ∅ r = 0 := by simp [chosenExcess,chosenVertices]
      simp only [q,image_empty,card_empty,Nat.cast_zero,mul_zero,add_zero,zero] at budget
      linarith only [budget,stage.total,inv]
    · have positive : (1:ℝ) ≤ q := by exact_mod_cast card_pos.mpr ((nonempty_iff_ne_empty.mpr empty).image T.row)
      have coeff : 0 ≤ 398/400-2*u := by linarith only [stage.le_tau]
      linarith only [budget,excess,stage.paired,inv,mul_le_mul_of_nonneg_left positive coeff]
  have nn : 0 ≤ deficitSum U E := sum_nonneg (deficit_nonneg U hr no data)
  have cap : (omittedCount U E:ℝ) < 1412 := by linarith only [nn,total]
  exact ⟨by linarith [Nat.cast_nonneg (α:=ℝ) (omittedCount U E)],Nat.le_of_lt_succ (show omittedCount U E < 1412 by exact_mod_cast cap)⟩

theorem ordinary_kept (A E : Finset V) (sub : A ⊆ live T) :
    let U := restrictLive T A
    ordinaryVertices U E ⊆ A ∧ (∀ x ∈ ordinaryVertices U E, T.row x ∉ E.image T.row) := by
  let U := restrictLive T A
  have split (x) (hx : x ∈ ordinaryVertices U E) : x ∈ live U ∧ T.row x ∉ E.image T.row := by
    obtain ⟨i,hi,h⟩ := mem_biUnion.mp hx
    simp only [rowList,available,mem_filter] at h
    obtain ⟨hl,lab,_⟩ := h
    exact ⟨hl,lab ▸ (mem_sdiff.mp (mem_sdiff.mp (mem_inter.mp hi).1).1).2⟩
  exact ⟨fun x hx ↦ (restrict_live T A sub) ▸ (split x hx).1, fun x hx ↦ (split x hx).2⟩

theorem incidence_eq (A E : Finset V) :
    let U := restrictLive T A
    incidenceSum U E = (∑ x ∈ ordinaryVertices U E, unrecordedDegree T x)/(r:ℝ)^2 := by
  let U := restrictLive T A
  change (∑ i ∈ ordinaryLists U E, rowIncidence U E i) = _
  rw [incidence_total,ordinary_total]
  exact congrArg (fun z : ℝ ↦ z/(r:ℝ)^2) (sum_congr rfl fun x _ ↦ restrict_degree T A x)

end
end Erdos617.ThirdPruning
