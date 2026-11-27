import ThirdPruningSelection

namespace Erdos617.ThirdPruning
open Finset ColoredLists PackingLists PruningOverlap PruningOverlap.Trace
open scoped Classical
noncomputable section
variable {V : Type*} [Fintype V] {r : ℕ} (T : Trace V r)

/-- Width failure charges each chosen pair at its actual degree cap, and charges
a new deletion only once even if it lies in a chosen oversized row. -/
theorem stage_failure {A E : Finset V} {Δ : ℕ} {u b α β : ℝ}
    (stage : Stage T A Δ u) (pr : Pruned T) (hr : 2^143 ≤ r)
    (order : Fintype.card V=r^2+1) (no : ¬Witness T.color)
    (data : Lists (restrictLive T A) E) (band : RetainedWidth.Band (incidenceCap T) b α β) :
    margin (firstRate T) (secondRate T) b α β +
      ((398/400-2*u)*(E.image T.row).card-thirdRate T A)/β+
      (2*spentFraction T+(9/25)*thirdRate T A)/α ≤ 0 := by
  let U := restrictLive T A
  let C := E.image T.row
  let B := oversizedRows univ T.row C r
  let O := oversizedExcess univ T.row C r
  let a := ((verticesIn (univ \ A) T.row B).card:ℝ)/r
  let n := omittedCount U E
  let q : ℝ := C.card
  let K := ordinaryVertices U E
  let I := incidenceSum U E
  let D := deficitSum U E
  let Y := incidenceCap T-2*spentFraction T-(9/25)*thirdRate T A
  let P := mass T A-(398/400-2*u)*q
  have rp : (0:ℝ)<r := by exact_mod_cast (show 0<r by omega)
  have r2 := sq_pos_of_pos rp
  obtain ⟨subset,outside⟩ := ordinary_kept T A E stage.sub
  have inc := incidence_after_third T A K C stage.sub subset outside pr.legal stage.removed
  have csub : C ⊆ range r := by intro i h; obtain ⟨x,_,rfl⟩ := mem_image.mp h; exact mem_range.mpr (pr.rows x)
  have forward := forward_floor_of_pivots T (by omega) no pr.pivots C csub
  have eq : (Y-2*(1-1/(r:ℝ))*O+(199/400)*a)*(r:ℝ)^2 =
      2*(T.crossGraph.edgeFinset.card:ℝ) - (r:ℝ)/2*T.firstSources.card -
      ((199/400:ℝ)*r)*T.secondSources.card - ((9/25:ℝ)*r)*(live T \ A).card -
      2*((r:ℝ)-1)*O*r + ((199/400:ℝ)*r)*(verticesIn (univ \ A) T.row B).card := by
    dsimp only [Y,incidenceCap,spentFraction,thirdRate,firstRate,secondRate,a]
    field_simp
    ring
  have incBound : I ≤ Y-2*(1-1/(r:ℝ))*O+(199/400)*a := by
    dsimp only [I]; rw [incidence_eq]; apply (div_le_iff₀ r2).2
    rw [eq]
    change (∑ x ∈ K, unrecordedDegree T x) + _ + _ + _ + _ ≤ _ at inc
    linarith only [inc,forward]
  have chosen := chosen_oversize_bound univ A T.row E r rp (subset_univ _)
  have hsmall : (((C \ B).card):ℝ) ≤ q := by dsimp only [q]; exact_mod_cast card_le_card (sdiff_subset (t:=B) (s:=C))
  have sharp := refined_deficit T stage pr (by omega) order no data
  have deficitBound : D+(n:ℝ)/400 ≤ P+O-a+q/256 := by
    change chosenExcess A T.row E r ≤ O-a+((C \ B).card:ℝ)/256 at chosen
    change D+(n:ℝ)/400+(398/400-2*u)*q ≤ _ at sharp
    unfold P; linarith only [chosen,hsmall,sharp,div_nonneg zero_le_one rp.le]
  have pairs : q ≤ (n:ℝ)/2 := by
    have h := data.pairs_le_short
    let F := shortRows (range r \ E.image U.row) (fun i ↦ (rowList U E i).card) (blockSize r)
    change C.card ≤ F.card at h
    change (C.card:ℝ) ≤ ((F.card+C.card:ℕ):ℝ)/2
    push_cast; apply (le_div_iff₀ (by norm_num)).2
    exact_mod_cast (show C.card*2 ≤ F.card+C.card by omega)
  have posO : 0 ≤ O := by
    apply sum_nonneg; intro i hi
    have h : 257*r < 256*rowCard (univ:Finset V) T.row i := (mem_filter.mp hi).2
    exact sub_nonneg.mpr ((le_div_iff₀ rp).2 (by rw [one_mul]; exact_mod_cast (show r ≤ _ by omega)))
  have posa : 0 ≤ a := div_nonneg (Nat.cast_nonneg _) rp.le
  have hr2 : (2:ℝ) ≤ r := by exact_mod_cast (show 2 ≤ r by omega)
  have inv : 1/(r:ℝ) ≤ 1/2 := (div_le_div_iff₀ rp (by norm_num)).mpr (by linarith only [hr2])
  have incidenceBound : I ≤ Y-O+(199/400)*a := by
    linarith only [incBound,mul_le_mul_of_nonneg_right (show 1 ≤ 2*(1-1/(r:ℝ)) by linarith) posO]
  have budget : WidthIntegral.RowBudget (ordinaryLists U E) (rowDeficit U E)
      (rowIncidence U E) n α β (Y/α+P/β) := by
    change I/α+D/β ≤ Y/α+P/β-((1/200-1/256)/(2*β))*n
    cases band <;> linarith only [incidenceBound,deficitBound,pairs,posO,posa]
  have failed := forced_width_cost T stage pr hr order no data band budget
  dsimp only [margin]
  dsimp only [Y,P,mass,incidenceCap] at failed
  cases band <;> linarith only [failed]

end
end Erdos617.ThirdPruning
