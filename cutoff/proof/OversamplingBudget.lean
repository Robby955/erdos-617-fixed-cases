import CutInputs
import OversamplingPass
import RepairEnvelope

/-! Scale the base repair cost in the units used by the exact endpoint check. -/

namespace Erdos617.ColoredLists

open Finset PruningOverlap PackingLists FiniteLaw MarkedSender RepresentativeRepairs
open scoped Classical
noncomputable section

/-- The numerical repair bound. W and l are in units of ρr. V bounds the
expected number of tested rows divided by s. -/
def normalizedRepairBound (a b κ V W l η : ℝ) : ℝ :=
  ((4/3)/(a-4/3))*((b*W+l)^2/(2-a*κ)+η*(((1+V)^2+V/1120)/2+1/(2*1120)))

theorem oversample_scale_error {r s R : ℝ} (rp : 0 < r) (sp : 0 < s) (Rpos : 0 < R)
    (scale : R*s^4 ≤ r) :
    r*s^2 ≤ (1/(R*(9/40:ℝ)^2))*(((9/40:ℝ)/s)*r)^2 := by
  field_simp [Rpos.ne',sp.ne']
  linarith only [scale]

variable {V : Type*} {r : ℕ} [Fintype V] (T : Trace V r)
variable {E : Finset V} {e t : ℕ} {α β M Y ex : ℝ}
  (S : WidthIntegral.Selection (ordinaryLists T E) (rowDeficit T E) (rowIncidence T E) e t α β M)

/-- The first pass can always use W=2κ, because the very same unique count
is at most twice the deficit in each of the retained cliques. -/
theorem first_pass_unique_weight {Ycap : ℝ} (prep : CutInputs T Ycap) (hr : 3 ≤ r) (no : ¬Witness T.color)
    (lists : ListBounds (targetGraph T.color T.target) T.row univ (live T) (range r) (qualifying T) E r)
    (band : RetainedWidth.Band Y ex α β) (κ : ℝ)
    (squares : 4*β^2*S.w*(1-S.w) ≤ κ*(9/40)) :
    (∑ i ∈ S.retained, ((uniqueGroup T E S.retained S.s i).card:ℝ)*rowDeficit T E i) ≤
      (2*κ)*((9/40:ℝ)/S.s*r) := by
  have rp : (0:ℝ)<r := by exact_mod_cast (show 0<r by omega)
  have sp : (0:ℝ)<S.s := by have := S.scale_lo; exact_mod_cast (show 0<S.s by omega)
  let x := rowDeficit T E
  have ht (i) (hi : i ∈ S.retained) :
      ((uniqueGroup T E S.retained S.s i).card:ℝ)*x i ≤ 2*r*(x i)^2 := by
    let N := ((uniqueGroup T E S.retained S.s i).card:ℝ)
    have cnt := unique_count_le_deficit T S prep hr no lists band hi
    have id : (r:ℝ)*x i = (r:ℝ)-(rowList T E i).card := by
      dsimp [x,rowDeficit]; field_simp
    have paid : N ≤ 2*((r:ℝ)*x i) := id.symm ▸ cnt
    have x0 : 0 ≤ x i := by
      have nz : 0 ≤ N := Nat.cast_nonneg _
      by_contra! neg
      linarith only [nz,paid,mul_neg_of_pos_of_neg rp neg]
    have h := mul_le_mul_of_nonneg_right paid x0
    linarith only [h]
  have total := sum_le_sum ht
  rw [← mul_sum] at total
  have quad : (∑ i ∈ S.retained, (x i)^2) ≤ κ*((9/40:ℝ)/S.s) := by
    rw [← mul_div_assoc,le_div_iff₀ sp,mul_comm _ (S.s:ℝ)]
    exact S.squares.trans squares
  apply total.trans
  linarith only [mul_le_mul_of_nonneg_left quad (show (0:ℝ) ≤ 2*r by positivity)]

/-- The base budget is at most P(W,l)(ρr)² with the same constants as
the endpoint checker. The two passes may supply different bounds W. -/
theorem normalized_repair_budget {Ycap : ℝ} (prep : CutInputs T Ycap) (hr : 3 ≤ r) (no : ¬Witness T.color)
    (order : Fintype.card V = r^2+1)
    (lists : ListBounds (targetGraph T.color T.target) T.row univ (live T) (range r) (qualifying T) E r)
    (band : RetainedWidth.Band Y ex α β) (slots : e+(ordinaryLists T E).card=r)
    (scale : (2:ℝ)^ex*(S.s:ℝ)^4 < r)
    (A X : ℝ) (a0 : 0 ≤ A) (a1 : A ≤ 656/4000) (x0 : 0 ≤ X) (x1 : X ≤ 1/2)
    (inc : α*S.w ≤ A) (defi : 2*β*S.w ≤ X) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (κ : ℝ) (k0 : 0 ≤ κ) (squares : 4*β^2*S.w*(1-S.w) ≤ κ*(9/40))
    (den : 0 < 2-heavyTestWeight A X*κ) (Yhi : ℝ)
    (ymax : Ycap ≤ Yhi)
    (W : ℝ) (Wcap : (∑ i ∈ S.retained, ((uniqueGroup T E S.retained S.s i).card:ℝ)*rowDeficit T E i)
      ≤ W*((9/40:ℝ)/S.s*r)) :
    let I := S.retained
    let s := S.s
    let H := senderSet T E I s
    let L := lowExterior T E I s
    let μ := senderLaw T E I s p (retry_rate_of_scale S.scale_lo) hp hp1
    let a := heavyTestWeight A X
    let b := uniqueTestWeight A X
    let V' := a*((513/512)*Yhi/(9/40)+7/1120)+9*b/1120
    let u := ((s-1:ℕ):ℝ)*r-L.card-(product μ).expect (markCount H)
    let unit := (9/40:ℝ)/s*r
    let η := 1/((2:ℝ)^ex*(9/40)^2)
    0 ≤ u → sampleRepairBudget (targetGraph T.color T.target) I (rowList T E) H
      (uniqueGroup T E I s) L s r μ (representativeFactor X) ≤
        normalizedRepairBound a b κ V' W (u/unit) η * unit^2 := by
  intro I s H L μ a b V' u unit η u0
  let k := (4/3:ℝ)/(a-4/3)
  let q := ∑ i ∈ I, loadTest T E I s μ a b i
  let D := ∑ i ∈ I, ((uniqueGroup T E I s i).card:ℝ)*rowDeficit T E i
  let h := ((s-1:ℕ):ℝ)
  let m := (product μ).expect (markCount H)
  have rp : (0:ℝ)<r := by exact_mod_cast (show 0<r by omega)
  have slo : (1120:ℝ) ≤ s := by exact_mod_cast S.scale_lo
  have sp : (0:ℝ)<s := by linarith only [slo]
  have up : 0 < unit := by dsimp [unit]; positivity
  obtain ⟨alow,_,blow,_⟩ := test_weight_bounds a0 a1 x0 x1
  change 4/3 < a at alow
  have ap : 0 ≤ a := by linarith only [alow]
  have bp : 0 ≤ b := (zero_le_one.trans (representativeFactor_one x0 (by linarith only [x1]))).trans blow
  have kp : 0 ≤ k := div_nonneg (by norm_num) (sub_nonneg.mpr alow.le)
  have hle : h ≤ s := by dsimp only [h]; exact_mod_cast Nat.sub_le s 1
  have mcap : m ≤ s*r := by
    change 0 ≤ h*r-L.card-m at u0
    linarith only [u0,Nat.cast_nonneg (α:=ℝ) L.card,mul_le_mul_of_nonneg_right hle rp.le]
  have msmall : m ≤ r*(s:ℝ)^2/1120 := by
    nlinarith only [mcap,mul_nonneg (sub_nonneg.mpr slo) (mul_nonneg sp.le rp.le)]
  let Y₀ := Ycap
  have y0 : 0 ≤ Y₀ := by
    have inc0 (i : ℕ) : 0 ≤ rowIncidence T E i := by unfold rowIncidence unrecordedDegree; positivity
    exact (sum_nonneg (s:=I) fun i _ ↦ inc0 i).trans (retained_load_budgets T S prep hr no order lists).2.2
  have mass := manuscript_test_mass T prep hr no order lists S band p hp hp1 a b ap bp
  change Y₀ ≤ Yhi at ymax
  have ymax' : Y₀/(9/40) ≤ (513/512)*Yhi/(9/40) := by linarith only [ymax,y0]
  have Vup : a*(Y₀/(9/40)+7/1120)+9*b/1120 ≤ V' := by
    dsimp only [V']; linarith only [mul_le_mul_of_nonneg_left ymax' ap]
  have q1 : q ≤ V'*s := mass.trans (mul_le_mul_of_nonneg_right Vup sp.le)
  have q0 : 0 ≤ q := sum_nonneg fun i hi ↦ (manuscript_row_test T S prep hr no lists band A X
    a0 a1 x0 x1 inc defi p hp hp1 i hi).1
  have v0 : 0 ≤ V' := by_contra fun bad ↦ (not_lt_of_ge (q0.trans q1))
    (mul_neg_of_neg_of_pos (lt_of_not_ge bad) sp)
  have bound : (h+q)^2 ≤ ((1+V')*s)^2 := by
    exact pow_le_pow_left₀ (add_nonneg (Nat.cast_nonneg _) q0)
      (by linarith only [hle,q1]) 2
  have eta0 : 0 ≤ η := by dsimp [η]; positivity
  have err : (r:ℝ)*(s:ℝ)^2 ≤ η*unit^2 := oversample_scale_error rp sp (by positivity) scale.le
  have noise : r*(h+q)^2+m ≤ η*(((1+V')^2+V'/1120)+1/1120)*unit^2 := by
    nlinarith only [mul_le_mul_of_nonneg_left bound rp.le,msmall,err,
      mul_le_mul_of_nonneg_left err (sq_nonneg (1+V')),
      mul_nonneg (mul_nonneg eta0 v0) (sq_nonneg unit)]
  have D0 : 0 ≤ D := by
    apply sum_nonneg
    intro i hi
    have hc := unique_count_le_deficit T S prep hr no lists band hi
    have d0 : 0 ≤ (r:ℝ)-(rowList T E i).card := by
      linarith only [hc,Nat.cast_nonneg (α:=ℝ) (uniqueGroup T E I s i).card]
    apply mul_nonneg (Nat.cast_nonneg _)
    change 0 ≤ 1-((rowList T E i).card:ℝ)/r
    apply sub_nonneg.mpr
    exact (div_le_one rp).mpr (by linarith only [d0])
  have Dbound : (b*D+u)^2 ≤ ((b*W+u/unit)*unit)^2 := by
    apply pow_le_pow_left₀ (add_nonneg (mul_nonneg bp D0) u0) _ 2
    rw [add_mul,div_mul_cancel₀ _ up.ne']
    linarith only [mul_le_mul_of_nonneg_left (show D ≤ W*unit from Wcap) bp]
  have budget := coloring_repair_envelope T prep hr no lists S band slots A X a0 a1 x0 x1
    inc defi p hp hp1 κ k0 squares den u0
  apply budget.trans
  change k*((b*D+u)^2/(2-a*κ)+(r*(h+q)^2+m)/2) ≤ _
  dsimp only [normalizedRepairBound]
  change _ ≤ (k*_)*unit^2
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ kp
  change 0 < 2-a*κ at den
  have positive := div_le_div_of_nonneg_right Dbound den.le
  rw [mul_pow] at positive
  exact (add_le_add positive (div_le_div_of_nonneg_right noise (by norm_num : (0:ℝ) ≤ 2))).trans_eq (by ring)

end
end Erdos617.ColoredLists
