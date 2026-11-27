import ThirdPruningData

/-! The actual clique rows supply the edge counts and moment inequalities in
the zero-pair certificate. The only width input is the inequality on their
largest deficit after short rows have been omitted. -/
namespace Erdos617.ThirdPruning
open Finset PruningOverlap ColoredLists PackingLists
open scoped Classical
noncomputable section
variable {V : Type*} [Fintype V] {r : ℕ} (T : Trace V r)

def liveDef (A : Finset V) (i : ℕ) := 1-(rowCard A T.row i:ℝ)/r

theorem clique_case_impossible {A : Finset V} (pass : Pass T A) (pr : Pruned T) (no : ¬Witness T.color)
    (hr : 2 ≤ r) (order : Fintype.card V=r^2+1)
    (clique : ∀ i < r, (targetGraph T.color T.target).IsClique ((A.filter fun v ↦ T.row v=i):Set V))
    {b α β : ℝ} (band : RetainedWidth.Band (incidenceCap T) b α β)
    (old : margin (firstRate T) (secondRate T) b α β+2*spentFraction T/α ≤ 0)
    (short : ∀ i < r, liveDef T A i-1/400 ≤ thirdRate T A-β*
      (margin (firstRate T) (secondRate T) b α β+
        (spentFraction T+remaining T-survivingFraction T A)/α)) : False := by
  let G := targetGraph T.color T.target
  let s := spentFraction T
  let e := survivingFraction T A
  let k := thirdRate T A
  let p := firstRate T
  let t := secondRate T
  let z := remaining T
  let w := margin p t b α β
  let H : ℝ := (holes G T.row A).card
  let E := edges T.crossGraph A
  let a := fun i ↦ (rowCard (univ \ A) T.row i:ℝ)/r
  let g := fun i ↦ ((T.rowSize i:ℝ)-r)/r
  let M := (∑ i ∈ range r, (a i)^2)/2
  have rp : (0:ℝ)<r := by exact_mod_cast (show 0<r by omega)
  have r2 := sq_pos_of_pos rp
  obtain ⟨j,hj,maximum⟩ := (range r).exists_max_image (liveDef T A) (nonempty_range_iff.mpr (by omega))
  let d := liveDef T A j
  have dc (i) (hi : i < r) := maximum i (mem_range.mpr hi)
  have cap := caps_of_no_witness T.color T.target hr no
  have rowcap (i) (hi : i < r) : rowCard A T.row i ≤ r := cap.2 _ (clique i hi)
  have d0 : 0 ≤ d := by
    apply sub_nonneg.mpr
    exact (div_le_one rp).mpr (Nat.cast_le.mpr (rowcap j (mem_range.mp hj)))
  have d1 : d ≤ 1 := sub_le_self _ (div_nonneg (Nat.cast_nonneg _) rp.le)
  have variance : (∑ i ∈ range r, (g i)^2) = variance T := by simp [g,div_pow,variance,Finset.sum_div]
  obtain ⟨v0,vc,pc,_⟩ := raw_fractions T pr no hr order
  have s0 : 0 ≤ s := v0.trans vc
  have e0 : 0 ≤ e := div_nonneg (Nat.cast_nonneg _) r2.le
  have k0 : 0 ≤ k := div_nonneg (Nat.cast_nonneg _) rp.le
  have h0 : 0 ≤ H := Nat.cast_nonneg _
  have a0 (i) : 0 ≤ a i := div_nonneg (Nat.cast_nonneg _) rp.le
  have asum : (∑ i ∈ range r, a i) = p+t+k := by
    have h := card_eq_sum_card_fiberwise (s:=univ \ A) (t:=range r) (f:=T.row)
      (fun x _ ↦ mem_range.mpr (pr.rows x))
    simpa only [a,rowCard,← Finset.sum_div,← Nat.cast_sum,← h] using all_deleted T pass.sub
  have abe (i) : a i = liveDef T A i+g i := by
    have sub : A.filter (fun v ↦ T.row v=i) ⊆ univ.filter (fun v ↦ T.row v=i) :=
      filter_subset_filter _ (subset_univ _)
    have split : (univ \ A).filter (fun v ↦ T.row v=i) =
        (univ.filter fun v ↦ T.row v=i) \ (A.filter fun v ↦ T.row v=i) := by
      ext x; simp; tauto
    have h := card_sdiff_add_card_eq_card sub
    rw [← split] at h
    change _ + _ = T.rowSize i at h
    have cast : (rowCard (univ \ A) T.row i:ℝ)+rowCard A T.row i=T.rowSize i := by exact_mod_cast h
    dsimp only [a,g,liveDef]
    field_simp
    linarith only [cast]
  have wcap (i) (hi : i < r) : a i ≤ d+Real.sqrt s := by
    have v := (single_le_sum (s:=range r) (fun j _ ↦ sq_nonneg (g j)) (mem_range.mpr hi)).trans (variance.le.trans vc)
    have root : g i ≤ Real.sqrt s := (Real.le_sqrt_of_sq_le v)
    rw [abe]; exact add_le_add (dc i hi) root
  have allsq : (∑ i ∈ range r, (a i)^2)*(r:ℝ)^2 =
      ∑ i ∈ range r, (rowCard (univ \ A) T.row i:ℝ)^2 := by
    rw [sum_mul]
    apply sum_congr rfl; intro i _
    dsimp only [a]; field_simp
  have mass := missing_mass T A pr.rows clique
  have low := missing_floor_of_counts T (by omega) order pr.rows (raw_edge_identity T pr.rows)
    (sparse_edge_cap T.color T.target pr.least)
  have balance : 1/2-s ≤ H/(r:ℝ)^2+M := by
    have h := low.trans mass
    change _ ≤ H + (∑ i ∈ range r, (rowCard (univ \ A) T.row i:ℝ)^2)/2 at h
    rw [← allsq] at h
    dsimp only [s,spentFraction,M]
    apply le_of_mul_le_mul_right _ r2
    field_simp
    linarith only [h]
  obtain ⟨slack,xcost⟩ := normalized_cost T pass (by omega)
  have p0 : 0 ≤ p := div_nonneg (Nat.cast_nonneg _) rp.le
  have t0 : 0 ≤ t := div_nonneg (Nat.cast_nonneg _) rp.le
  apply zero_branch_impossible (w:=w) band (d:=d) (h:=H/(r:ℝ)^2) (m:=M)
    (z:=z) (s:=s) (e:=e) (k:=k) ?_ (rational_margin p0 pc band)
  refine ⟨p0,pc,t0,rfl,s0,e0,k0,by linarith only [slack],old,d0,d1,
    div_nonneg h0 r2.le,div_nonneg (sum_nonneg fun i _ ↦ sq_nonneg (a i)) (by norm_num),
    balance,short j (mem_range.mp hj),?_,?_⟩
  · intro u hu _
    have young := deleted_second_moment (range r) a g (fun i _ ↦ a0 i)
      (fun i hi ↦ (abe i).le.trans (add_le_add_left (dc i (mem_range.mp hi)) _))
      (variance.le.trans vc) hu
    rw [asum] at young
    dsimp only [M]
    linarith only [young]
  · intro pos
    have live_floor (i) (hi : i < r) : (1-d)*r ≤ ((A.filter fun v ↦ T.row v=i).card:ℝ) := by
      have ge : 1-d ≤ (rowCard A T.row i:ℝ)/r := by
        have v : 1-(rowCard A T.row i:ℝ)/r ≤ d := dc i hi
        linarith only [v]
      exact (le_div_iff₀ rp).mp ge
    have gone (i) (hi : i < r) : (((univ \ A).filter fun v ↦ T.row v=i).card:ℝ) ≤ (d+Real.sqrt s)*r :=
      (div_le_iff₀ rp).mp (wcap i hi)
    have cross := cross_target T
    have stop := pass.stop
    rw [← cross] at stop xcost
    have charge := charge_actual_holes G T.row A pr.rows cap.1 (mul_pos pos rp) live_floor
      (fun i hi ↦ Nat.cast_le.mpr (rowcap i hi)) gone rp.le
      (mul_nonneg (add_nonneg d0 (Real.sqrt_nonneg _)) rp.le) stop xcost
    dsimp only at charge
    rw [cross] at charge
    have repr : E=e*(r:ℝ)^2 := by dsimp only [E,e,survivingFraction]; field_simp
    have eq : E/((1-d)*r) = (e/(1-d))*r := by rw [repr]; field_simp
    change (((1-d)*r-E/((1-d)*r)-(199/400:ℝ)*r)*H ≤
      r*((z-s-e-(9/25)*k)*(r:ℝ)^2)+(d+Real.sqrt s)*r*(2*E)) ∧
      (((1-d)*r-E/((1-d)*r)-(199/400:ℝ)*r-(9/25:ℝ)*r)*H ≤ r*((z-s-e-(9/25)*k)*(r:ℝ)^2)) at charge
    rw [eq,repr] at charge
    have normalize {P Q : ℝ} (ineq : (P*(r:ℝ))*H ≤ Q*(r:ℝ)^3) :
        P*(H/(r:ℝ)^2) ≤ Q := by
      apply le_of_mul_le_mul_right _ (pow_pos rp 3)
      calc (P*(H/(r:ℝ)^2))*(r:ℝ)^3 = (P*r)*H := by field_simp
           _ ≤ _ := ineq
    constructor
    · apply normalize
      linarith only [charge.1]
    · apply normalize
      linarith only [charge.2]

end
end Erdos617.ThirdPruning
