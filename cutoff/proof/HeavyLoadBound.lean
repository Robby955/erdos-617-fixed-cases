import HeavyLoadIncidence

/-! The expected number of positive excess loads at a retained row. The
two kinds of target incidence share a single unrecorded edge budget. -/

namespace Erdos617.ColoredLists

open Finset PruningOverlap PackingLists FiniteLaw MarkedSender
open scoped Classical
noncomputable section
variable {V : Type*} {r : ℕ} [Fintype V] (T : Trace V r)

private theorem threshold_le_load (s r t : ℕ) (hs : 0<s) :
    ((9/40:ℝ)/s*r)*ArcRepair.active (ExcessCircle.excess s r t) ≤ t := by
  unfold ArcRepair.active
  split
  · rename_i pos
    have realPos : (0:ℝ) < (ExcessCircle.excess s r t:ℝ) := by exact_mod_cast pos
    rw [ExcessCircle.excess_units hs] at realPos
    by_contra! bad
    rw [mul_one] at bad
    rw [max_eq_right (by linarith only [bad]),mul_zero] at realPos
    exact lt_irrefl _ realPos
  · simp

omit [Fintype V] in
private theorem foreign_nonnegative (G : SimpleGraph V) (C : ℕ → Finset V) (i : ℕ) (o : State V) :
    0 ≤ foreignDegree G C i o := by
  cases o with
  | none => exact le_rfl
  | some a =>
    cases a with
    | none => exact le_rfl
    | some z =>
      change 0 ≤ if z ∈ C i then 0 else SameRowConflicts.degree G (C i) z
      split
      · exact le_rfl
      · exact Nat.cast_nonneg _

/-- Pay exceptional vertices one threshold each. Every remaining direct
load is in the exterior and is counted at a different endpoint from all
foreign representatives. The latter are still counted with multiplicity. -/
theorem threshold_heavy_count (E : Finset V) (I : Finset ℕ) (s : ℕ) (hs : 0<s)
    (p : ℝ) (rate : 100*((9/40:ℝ)/s) ≤ 1) (hp : 0 ≤ p) (hp1 : p ≤ 1) (i : ℕ) :
    let G := targetGraph T.color T.target
    let C := rowList T E
    let L := lowExterior T E I s
    let μ := senderLaw T E I s p rate hp hp1
    let base := (9/40:ℝ)/s*r
    let B := loadExceptions T E i
    let A := loadOutside T E I \ B
    base*heavyLoadMean G C L s r μ i ≤ base*B.card+
      (∑ y ∈ A, SameRowConflicts.degree G (C i) y)+∑ y, (μ y).expect (foreignDegree G C i) := by
  intro G C L μ base B A
  let deg := SameRowConflicts.degree G (C i)
  let load := repairLoad G C L i
  let frac := fun y o ↦ ArcRepair.active (ExcessCircle.excess s r (load y o))
  let fixed := fun y ↦ (if y ∈ B then base else 0)+(if y ∈ A then deg y else 0)
  have base0 : 0 ≤ base := by dsimp [base]; positivity
  have point (w : V → State V) (support : 0 < (product μ).weight w) (y : V) :
      base*frac y (w y) ≤ fixed y+foreignDegree G C i (w y) := by
    by_cases ex : y ∈ B
    · have one : frac y (w y) ≤ 1 := by dsimp [frac,ArcRepair.active]; split <;> norm_num
      have na : y ∉ A := fun h ↦ (mem_sdiff.mp h).2 ex
      simp only [fixed,ite_eq_left ex,ite_eq_right na,add_zero]
      have up := mul_le_mul_of_nonneg_left one base0
      linarith only [up,foreign_nonnegative G C i (w y)]
    · by_cases out : y ∈ loadOutside T E I
      · have ya : y ∈ A := mem_sdiff.mpr ⟨out,ex⟩
        simp only [fixed,ite_eq_right ex,ite_eq_left ya,zero_add]
        apply (threshold_le_load s r (load y (w y)) hs).trans
        by_cases low : y ∈ L
        · change ((repairLoad G C L i y (w y)):ℝ) ≤ _
          unfold repairLoad
          rw [ite_eq_left low]
          exact le_add_of_nonneg_right (foreign_nonnegative ..)
        · cases wx : w y with
          | none => simp [load,repairLoad,low,foreignDegree,deg,SameRowConflicts.degree]
          | some o =>
            cases o with
            | none => simp [load,repairLoad,low,foreignDegree,deg,SameRowConflicts.degree]
            | some z => by_cases own : z ∈ C i <;> simp [load,repairLoad,low,foreignDegree,deg,SameRowConflicts.degree,own]
      · have na : y ∉ A := fun h ↦ out (mem_sdiff.mp h).1
        have low : y ∉ L := fun h ↦ out (mem_sdiff.mpr ⟨mem_univ _,(mem_filter.mp h).2.1⟩)
        have notSender : y ∉ senderSet T E I s := fun h ↦ out (mem_sdiff.mp h).1
        have blank : w y = none := by
          cases eq : w y with
          | none => rfl
          | some o =>
            cases o with
            | none => exact (notSender (moderate_support T support eq).1).elim
            | some z =>
              obtain ⟨_,_,hy,_,_⟩ := represented_support T support eq
              exact (notSender (mem_filter.mp hy).1).elim
        simp [blank,fixed,na,ex,frac,load,repairLoad,low,ExcessCircle.excess,ArcRepair.active,foreignDegree]
  have averaged (y : V) : base*(μ y).expect (frac y) ≤ fixed y+(μ y).expect (foreignDegree G C i) := by
    have per := (product μ).expect_mono_on_support (fun w h ↦ point w h y)
    rw [Law.expect_const_mul,Law.expect_add,Law.expect_const,expect_coord,expect_coord] at per
    exact per
  have total := sum_le_sum (s:=univ) fun y _ ↦ averaged y
  rw [← mul_sum,sum_add_distrib] at total
  have constant : ∑ y, fixed y = base*(B.card:ℝ)+∑ y ∈ A, deg y := by
    simp [fixed,sum_add_distrib,mul_comm]
  rw [constant] at total
  exact total

variable {E : Finset V} {e t : ℕ} {α β M Y b : ℝ}
  (S : WidthIntegral.Selection (ordinaryLists T E) (rowDeficit T E) (rowIncidence T E) e t α β M)

/-- The number of uniquely strong senders is at most twice the deficit of
the receiving clique. This is also the term used in the row test. -/
theorem unique_count_le_deficit (prep : Prepared T) (hr : 3 ≤ r) (no : ¬Witness T.color)
    (lists : ListBounds (targetGraph T.color T.target) T.row univ (live T) (range r) (qualifying T) E r)
    (band : RetainedWidth.Band Y b α β) {i : ℕ} (hi : i ∈ S.retained) :
    ((uniqueGroup T E S.retained S.s i).card:ℝ) ≤ 2*((r:ℝ)-(rowList T E i).card) := by
  have dis : Disjoint (rowList T E i) (uniqueGroup T E S.retained S.s i) :=
    disjoint_left.mpr fun x xc mem ↦ (mem_senderSet T).mp (mem_filter.mp mem).1 |>.1 <|
      mem_biUnion.mpr ⟨i,hi,xc⟩
  have raw := (retained_heavy_senders T prep hr no lists S band hi _ dis
    (fun _ member ↦ (unique_destination T member).2)).1
  have ordinary : i ∈ ordinaryLists T E := by
    rw [S.retained_eq] at hi
    exact (mem_sdiff.mp (mem_filter.mp hi).1).1
  have fits := (caps_of_no_witness T.color T.target (by omega) no).2 _
    (lists.clique i (mem_sdiff.mp (mem_sdiff.mp (mem_inter.mp ordinary).1).1).2)
  rw [← Nat.cast_sub (R:=ℝ) (show (rowList T E i).card ≤ r from fits)]
  exact_mod_cast raw

/-- The expected multiplicity of any point in a foreign retained row is
at most one. Thus all representative loads fit their distinct row cuts. -/
theorem foreign_load_le_distinct_edges (prep : Prepared T) (hr : 3 ≤ r) (no : ¬Witness T.color)
    (lists : ListBounds (targetGraph T.color T.target) T.row univ (live T) (range r) (qualifying T) E r)
    (band : RetainedWidth.Band Y b α β) (p : ℝ) (rate : 100*((9/40:ℝ)/S.s) ≤ 1)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (i : ℕ) :
    let G := targetGraph T.color T.target
    let C := rowList T E
    let μ := senderLaw T E S.retained S.s p rate hp hp1
    (∑ y, (μ y).expect (foreignDegree G C i)) ≤
      ∑ k ∈ S.retained.erase i, ((RepresentativeCut.cut G (C i) (C k)).card:ℝ) := by
  intro G C μ
  have small : 2*β*S.w ≤ 1 := by
    have bet : 0 ≤ β ∧ β ≤ 925/4000 := by cases band <;> norm_num
    linarith only [mul_le_mul_of_nonneg_left S.width_lt.le (show 0 ≤ 2*β by linarith only [bet.1]),bet.2]
  have rp : (0:ℝ)<r := by exact_mod_cast (show 0<r by omega)
  have upper := foreign_load_le_interrow_cut T S (by omega) 1 (by norm_num) (by norm_num) small p rate hp hp1 i
  apply upper.trans
  rw [mul_sum]
  apply sum_le_sum
  intro k hk
  have retained := (mem_erase.mp hk).2
  have count := unique_count_le_deficit T S prep hr no lists band retained
  have floor := (temporary_row_bounds T prep (by omega) E band S retained).1
  have sub : (temporaryRow T E k).card ≤ (C k).card := card_le_card (filter_subset ..)
  have near : (255/256:ℝ)*r ≤ ((C k).card:ℝ) := floor.trans (by exact_mod_cast sub)
  have mass : representativeFactor 1/r*((uniqueGroup T E S.retained S.s k).card:ℝ) ≤ 1 := by
    rw [div_mul_eq_mul_div,div_le_iff₀ rp]
    norm_num [representativeFactor] at ⊢
    change _ ≤ 2*((r:ℝ)-(C k).card) at count
    linarith only [count,near,rp]
  simpa only [← mul_assoc,one_mul] using mul_le_mul_of_nonneg_right mass
    (Nat.cast_nonneg (α:=ℝ) (RepresentativeCut.cut G (C i) (C k)).card)

/-- Normalized height of the row's heavy-load count. The coefficient of
the actual foreign-incidence term is one. All inputs are the original
trace, its retained rows and its admissible sender law. -/
theorem heavy_load_height (prep : Prepared T) (hr : 3 ≤ r) (no : ¬Witness T.color)
    (lists : ListBounds (targetGraph T.color T.target) T.row univ (live T) (range r) (qualifying T) E r)
    (band : RetainedWidth.Band Y b α β) (p : ℝ) (rate : 100*((9/40:ℝ)/S.s) ≤ 1)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) {i : ℕ} (hi : i ∈ S.retained) :
    let G := targetGraph T.color T.target
    let C := rowList T E
    let μ := senderLaw T E S.retained S.s p rate hp hp1
    let n := heavyLoadMean G C (lowExterior T E S.retained S.s) S.s r μ i
    n/r ≤ rowDeficit T E i+rawSurplus T i+assigned T i+rowIncidence T E i/((9/40:ℝ)/S.s) := by
  intro G C μ n
  have sr : 0<S.s := by have := S.scale_lo; omega
  have rp : (0:ℝ)<r := by exact_mod_cast (show 0<r by omega)
  let ρ := (9/40:ℝ)/S.s
  have rho : 0<ρ := by dsimp [ρ]; positivity
  let B := loadExceptions T E i
  let A := loadOutside T E S.retained \ B
  let direct := ∑ y ∈ A, SameRowConflicts.degree G (C i) y
  let cuts := ∑ k ∈ S.retained.erase i, ((RepresentativeCut.cut G (C i) (C k)).card:ℝ)
  let F := ∑ y, (μ y).expect (foreignDegree G C i)
  let total := ∑ x ∈ C i, unrecordedDegree T x
  have charge : ρ*r*n ≤ ρ*r*B.card+direct+F := threshold_heavy_count T E _ _ sr p rate hp hp1 i
  have paid : F ≤ cuts := foreign_load_le_distinct_edges T S prep hr no lists band p rate hp hp1 i
  have combined : direct+cuts ≤ total := disjoint_load_incidence T E _ hi
  have num : ρ*r*(n-B.card) ≤ total := by linarith only [charge,paid,combined]
  have scaled : n/r ≤ (B.card:ℝ)/r+rowIncidence T E i/ρ := by
    change n/r ≤ (B.card:ℝ)/r+(total/(r:ℝ)^2)/ρ
    field_simp [rp.ne',rho.ne']
    nlinarith only [num]
  have ex := load_exceptions_card T E i
  have surplus : (T.rowSize i:ℝ)/r-1 ≤ rawSurplus T i := le_max_left ..
  have exBound : (B.card:ℝ)/r ≤ rowDeficit T E i+rawSurplus T i+assigned T i := by
    have div := div_le_div_of_nonneg_right ex rp.le
    change (B.card:ℝ)/r ≤ ((T.rowSize i:ℝ)-(C i).card+
      ((T.firstSources.filter (fun y ↦ T.destination y=i)).card:ℝ))/r at div
    unfold rowDeficit assigned
    change _ ≤ 1-((C i).card:ℝ)/r+rawSurplus T i+_
    rw [add_div,sub_div] at div
    linarith only [surplus,div]
  exact scaled.trans (add_le_add_left exBound _)

end
end Erdos617.ColoredLists
