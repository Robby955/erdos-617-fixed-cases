import CutInputs
import HeavyLoadTotals
import RecoveredTest

/-! Admissibility of the actual row tests used at a width endpoint. -/

namespace Erdos617.ColoredLists

open Finset PruningOverlap PackingLists FiniteLaw MarkedSender
open scoped Classical
noncomputable section

def testHeight (A X : ℝ) : ℝ :=
  (513/512)*(A/(9/40))+1/256+X/1120+5/1464

def heavyTestWeight (A X : ℝ) : ℝ := min (5/2) ((249/250)/testHeight A X)

def uniqueTestWeight (A X : ℝ) : ℝ := (3/4)*heavyTestWeight A X*representativeFactor X

theorem test_weight_bounds {A X : ℝ} (a0 : 0 ≤ A) (a1 : A ≤ 656/4000)
    (x0 : 0 ≤ X) (x1 : X ≤ 1/2) :
    4/3 < heavyTestWeight A X ∧ heavyTestWeight A X*testHeight A X ≤ 249/250 ∧
      representativeFactor X ≤ uniqueTestWeight A X ∧ uniqueTestWeight A X ≤ 4 := by
  have z : 0 < testHeight A X := by unfold testHeight; positivity
  have small : (4/3)*testHeight A X < 249/250 := by unfold testHeight; linarith only [a1,x1]
  have low : 4/3 < heavyTestWeight A X :=
    lt_min (by norm_num) ((lt_div_iff₀ z).mpr small)
  have high : heavyTestWeight A X ≤ 5/2 := min_le_left ..
  have pay : heavyTestWeight A X*testHeight A X ≤ 249/250 :=
    (le_div_iff₀ z).mp (min_le_right ..)
  have j0 := representativeFactor_one x0 (by linarith only [x1])
  have j2 : representativeFactor X ≤ 2 := by
    apply (div_le_iff₀ (by linarith only [x1] : 0 < 1-X/1120)).mpr
    linarith only [x1]
  have jpos : 0 ≤ representativeFactor X := by linarith only [j0]
  have lower := mul_nonneg (sub_nonneg.mpr low.le) jpos
  have upper := mul_le_mul high j2 jpos (by norm_num : (0:ℝ) ≤ 5/2)
  exact ⟨low,pay,by unfold uniqueTestWeight; linarith only [lower],
    by unfold uniqueTestWeight; linarith only [upper]⟩

/-- The coefficient in the executable width check is written as j(1+1/k),
where k=(4/3)/(a-4/3). -/
theorem uniqueTestWeight_eq (A X : ℝ) :
    uniqueTestWeight A X = representativeFactor X*
      (1+1/((4/3)/(heavyTestWeight A X-4/3))) := by
  unfold uniqueTestWeight
  rw [div_div_eq_mul_div]
  ring

variable {V : Type*} {r : ℕ} [Fintype V] (T : Trace V r)
variable {E : Finset V} {e t : ℕ} {α β M Y ex : ℝ}
  (S : WidthIntegral.Selection (ordinaryLists T E) (rowDeficit T E) (rowIncidence T E) e t α β M)

/-- Every retained row of the coloring gives a valid Bernoulli probability
using the two coefficients of the manuscript's width-endpoint check. -/
theorem manuscript_row_test {Ycap : ℝ} (prep : CutInputs T Ycap) (hr : 3 ≤ r) (no : ¬Witness T.color)
    (lists : ListBounds (targetGraph T.color T.target) T.row univ (live T) (range r) (qualifying T) E r)
    (band : RetainedWidth.Band Y ex α β) (A X : ℝ)
    (a0 : 0 ≤ A) (a1 : A ≤ 656/4000) (x0 : 0 ≤ X) (x1 : X ≤ 1/2)
    (inc : α*S.w ≤ A) (defi : 2*β*S.w ≤ X)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    ∀ i ∈ S.retained, loadTest T E S.retained S.s
      (senderLaw T E S.retained S.s p (retry_rate_of_scale S.scale_lo) hp hp1)
      (heavyTestWeight A X) (uniqueTestWeight A X) i ∈ Set.Icc 0 1 := by
  intro i hi
  let μ := senderLaw T E S.retained S.s p (retry_rate_of_scale S.scale_lo) hp hp1
  let n := heavyLoadMean (targetGraph T.color T.target) (rowList T E)
    (lowExterior T E S.retained S.s) S.s r μ i
  let N := ((uniqueGroup T E S.retained S.s i).card:ℝ)
  let a := heavyTestWeight A X
  let b := uniqueTestWeight A X
  have rp : (0:ℝ)<r := by exact_mod_cast (show 0<r by omega)
  have slo : (1120:ℝ) ≤ S.s := by exact_mod_cast S.scale_lo
  have ordinary : i ∈ ordinaryLists T E := by
    rw [S.retained_eq] at hi
    exact (mem_sdiff.mp (mem_filter.mp hi).1).1
  have qual := (qualifying_bounds T (by omega) (mem_inter.mp ordinary).2).2.1
  have size : (256:ℝ)*T.rowSize i ≤ 257*r := by exact_mod_cast qual
  have extra : rawSurplus T i ≤ 1/256 := by
    change max ((T.rowSize i:ℝ)/r-1) 0 ≤ _
    apply max_le _ (by norm_num)
    apply sub_le_iff_le_add.mpr
    apply (div_le_iff₀ rp).mpr
    linarith only [size]
  have dx : rowDeficit T E i ≤ X/1120 := by
    by_cases h : 0 ≤ rowDeficit T E i
    · linarith only [(S.deficit i hi).trans defi, mul_le_mul_of_nonneg_right slo h]
    · have hz : 0 ≤ X/1120 := by positivity
      linarith only [h,hz]
  have cy : rowIncidence T E i/((9/40:ℝ)/S.s) ≤ A/(9/40) := by
    rw [div_div_eq_mul_div]
    exact div_le_div_of_nonneg_right (by simpa [mul_comm] using (S.incidence i hi).trans inc) (by norm_num)
  have raw := heavy_load_height T S prep hr no lists band p (retry_rate_of_scale S.scale_lo) hp hp1 hi
  change n/r ≤ _ at raw
  have height : n/r ≤ testHeight A X := by
    unfold testHeight
    linarith only [raw,dx,extra,prep.source_cap i,cy,a0]
  have count := unique_count_le_deficit T S prep hr no lists band hi
  have nx : N/r ≤ 2*(X/1120) := by
    have h := div_le_div_of_nonneg_right count rp.le
    rw [mul_div_assoc,sub_div,div_self rp.ne'] at h
    change N/r ≤ 2*rowDeficit T E i at h
    linarith only [dx,h]
  obtain ⟨alow,paid,blow,bhigh⟩ := test_weight_bounds a0 a1 x0 x1
  have ap : 0 ≤ a := by dsimp [a]; linarith only [alow]
  have bp : 0 ≤ b := by dsimp [b]; linarith only [blow,representativeFactor_one x0 (by linarith only [x1])]
  have n0 : 0 ≤ n := by
    apply sum_nonneg
    intro y _
    apply sum_nonneg
    intro o _
    apply mul_nonneg ((μ y).nonneg o)
    simp only [ArcRepair.active]
    split <;> norm_num
  have N0 : 0 ≤ N := Nat.cast_nonneg _
  change (a*n+b*N)/r ∈ Set.Icc 0 1
  refine ⟨by positivity,?_⟩
  rw [add_div,mul_div_assoc,mul_div_assoc]
  have h1 := (mul_le_mul_of_nonneg_left height ap).trans paid
  have h2 := mul_le_mul (show b ≤ 4 from bhigh) nx (div_nonneg N0 rp.le) (by norm_num)
  linarith only [h1,h2,x1]

end
end Erdos617.ColoredLists
