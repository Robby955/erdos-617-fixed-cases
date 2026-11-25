import OversamplingBudget

/-! Remove the two artificial caps on the oversample using uniform inequalities
valid throughout all five width bands. -/

namespace Erdos617.ColoredLists

open Finset PruningOverlap PackingLists FiniteLaw MarkedSender RepresentativeRepairs
open scoped Classical
noncomputable section

/-- Z from either oversampling pass; W is its bound on weighted unique deficits. -/
def oversampleFactor (A X Yhi κ W ex : ℝ) : ℝ :=
  let a := heavyTestWeight A X
  let b := uniqueTestWeight A X
  let V := a*((513/512)*Yhi/(9/40)+7/1120)+9*b/1120
  let η := 1/((2:ℝ)^ex*(9/40)^2)
  8*normalizedRepairBound a b κ V W 0 η+2*η

/-- Uniform guards for unclipping. The endpoint-dependent Z is retained in
the conclusion of the graph theorem; the coarse constants only prove strictness. -/
theorem oversample_guards {Y ex α β A X Yhi κ W : ℝ} (band : RetainedWidth.Band Y ex α β)
    (a0 : 0 ≤ A) (a1 : A ≤ 656/4000) (x0 : 0 ≤ X) (x1 : X ≤ 1/2)
    (y0 : 0 ≤ Yhi) (y1 : Yhi ≤ 2) (k0 : 0 ≤ κ) (k1 : κ ≤ 1/4) (w0 : 0 ≤ W) (w1 : W ≤ 1) :
    0 < 2-heavyTestWeight A X*κ ∧ 0 ≤ oversampleFactor A X Yhi κ W ex ∧
      oversampleFactor A X Yhi κ W ex*((9/40:ℝ)/1120)^2 < min ((3/20:ℝ)/128) (1/16) := by
  let a := heavyTestWeight A X
  let b := uniqueTestWeight A X
  let V := a*((513/512)*Yhi/(9/40)+7/1120)+9*b/1120
  let η := 1/((2:ℝ)^ex*(9/40)^2)
  let k := (4/3)/(a-4/3)
  have height : 0 < testHeight A X := by unfold testHeight; positivity
  have low : (101/75:ℝ) ≤ a := by
    apply le_min (by norm_num)
    apply (le_div_iff₀ height).mpr
    unfold testHeight
    linarith only [a1,x1]
  have ahi : a ≤ 5/2 := min_le_left ..
  have apos : 0 ≤ a := by linarith only [low]
  obtain ⟨_,_,jb,bhi⟩ := test_weight_bounds a0 a1 x0 x1
  have bp : 0 ≤ b := (zero_le_one.trans (representativeFactor_one x0 (by linarith only [x1]))).trans jb
  change b ≤ 4 at bhi
  have ap : 0 < a-4/3 := by linarith only [low]
  have kp : 0 ≤ k := div_nonneg (by norm_num) ap.le
  have klim : k ≤ 100 := (div_le_iff₀ ap).mpr (by linarith only [low])
  have denom : 1 ≤ 2-a*κ := by linarith only [mul_le_mul ahi k1 k0 (by norm_num : (0:ℝ) ≤ 5/2)]
  have dp : 0 < 2-a*κ := lt_of_lt_of_le zero_lt_one denom
  have η0 : 0 ≤ η := by dsimp [η]; positivity
  have η1 : η ≤ 1/500 := by dsimp [η]; cases band <;> norm_num
  have V0 : 0 ≤ V := by dsimp [V]; positivity
  have V1 : V ≤ 24 := by
    have linear : 0 ≤ (513/512)*Yhi/(9/40)+7/1120 := by positivity
    have cap : (513/512)*Yhi/(9/40)+7/1120 ≤ 9 := by linarith only [y1]
    dsimp only [V]
    linarith only [mul_le_mul ahi cap linear (by norm_num : (0:ℝ) ≤ 5/2),bhi]
  have BW : b*W ≤ 4 := by simpa using mul_le_mul bhi w1 w0 (by norm_num : (0:ℝ) ≤ 4)
  have first : (b*W)^2/(2-a*κ) ≤ 16 := by
    apply (div_le_iff₀ dp).mpr
    nlinarith only [pow_le_pow_left₀ (mul_nonneg bp w0) BW 2,denom]
  let tail := (((1+V)^2+V/1120)/2+1/(2*1120))
  have tail0 : 0 ≤ tail := by dsimp [tail]; positivity
  have tail1 : tail ≤ 500 := by
    dsimp only [tail]
    linarith only [pow_le_pow_left₀ (by linarith only [V0] : 0 ≤ 1+V)
      (by linarith only [V1] : 1+V ≤ 25) 2,V1]
  have tailCap : η*tail ≤ 1 := by
    simpa using mul_le_mul η1 tail1 tail0 (by norm_num : (0:ℝ) ≤ 1/500)
  let P := normalizedRepairBound a b κ V W 0 η
  have expr : P = k*((b*W)^2/(2-a*κ)+η*tail) := by simp [P,normalizedRepairBound,k,tail]
  have part0 : 0 ≤ (b*W)^2/(2-a*κ)+η*tail := by positivity
  have P0 : 0 ≤ P := expr ▸ mul_nonneg kp part0
  have P1 : P ≤ 1700 := by
    rw [expr]
    convert mul_le_mul klim (by linarith only [first,tailCap] : (b*W)^2/(2-a*κ)+η*tail ≤ 17) part0 (by norm_num) using 1
    norm_num
  change 0 < 2-a*κ ∧ 0 ≤ 8*P+2*η ∧ (8*P+2*η)*_ < _
  exact ⟨dp,by positivity,lt_min (by linarith only [P1,η1]) (by linarith only [P1,η1])⟩

variable {V : Type*} {r : ℕ} [Fintype V] (T : Trace V r)
variable {E : Finset V} {e t : ℕ} {α β M Y ex : ℝ}
  (S : WidthIntegral.Selection (ordinaryLists T E) (rowDeficit T E) (rowIncidence T E) e t α β M)

/-- On the actual coloring, the number of eligible senders above the exterior
shortage is at most Zρ²r. This uses the full base budget and both oversample
floors. It applies to either pass once its W bound has been proved. -/
theorem eligibility_surplus (prep : Prepared T) (hr : 3 ≤ r) (no : ¬Witness T.color)
    (order : Fintype.card V = r^2+1)
    (lists : ListBounds (targetGraph T.color T.target) T.row univ (live T) (range r) (qualifying T) E r)
    (band : RetainedWidth.Band Y ex α β) (slots : e+(ordinaryLists T E).card=r)
    (scale : (2:ℝ)^ex*(S.s:ℝ)^4 < r)
    (A X : ℝ) (a0 : 0 ≤ A) (a1 : A ≤ 656/4000) (x0 : 0 ≤ X) (x1 : X ≤ 1/2)
    (inc : α*S.w ≤ A) (defi : 2*β*S.w ≤ X)
    (κ Yhi W : ℝ) (k0 : 0 ≤ κ) (k1 : κ ≤ 1/4) (y0 : 0 ≤ Yhi) (y1 : Yhi ≤ 2)
    (w0 : 0 ≤ W) (w1 : W ≤ 1) (squares : 4*β^2*S.w*(1-S.w) ≤ κ*(9/40))
    (ymax : 2-firstRate T/2-(199/400:ℝ)*secondRate T ≤ Yhi)
    (Wcap : (∑ i ∈ S.retained, ((uniqueGroup T E S.retained S.s i).card:ℝ)*rowDeficit T E i)
      ≤ W*((9/40:ℝ)/S.s*r)) :
    let I := S.retained
    let H := senderSet T E I S.s
    let L := lowExterior T E I S.s
    let Δ := ((S.s-1:ℕ):ℝ)*r-L.card
    let total := ∑ y ∈ H, senderEligibility T E I S.s y
    let ρ := (9/40:ℝ)/S.s
    (3/20:ℝ)*r < Δ → max (total-Δ) 0 ≤ oversampleFactor A X Yhi κ W ex*ρ^2*r := by
  intro I H L Δ total ρ shortage
  let Z := oversampleFactor A X Yhi κ W ex
  let a := heavyTestWeight A X
  let b := uniqueTestWeight A X
  let V' := a*((513/512)*Yhi/(9/40)+7/1120)+9*b/1120
  let η := 1/((2:ℝ)^ex*(9/40)^2)
  let P := normalizedRepairBound a b κ V' W 0 η
  have rp : (0:ℝ)<r := by exact_mod_cast (show 0<r by omega)
  have slo : (1120:ℝ) ≤ S.s := by exact_mod_cast S.scale_lo
  have sp : (0:ℝ)<S.s := by linarith only [slo]
  have rhop : 0 ≤ ρ := by dsimp [ρ]; positivity
  have ρcap : ρ ≤ (9/40:ℝ)/1120 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) slo
  obtain ⟨den,Z0,guard⟩ := oversample_guards band a0 a1 x0 x1 y0 y1 k0 k1 w0 w1
  change 0 ≤ Z at Z0
  have guards := lt_of_le_of_lt (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ rhop ρcap 2) Z0) guard
  have cut1 : Z*ρ^2*(r:ℝ)^2 < r*(Δ/128) := by
    have t := mul_lt_mul_of_pos_right (lt_of_lt_of_le guards (min_le_left ..)) (mul_pos rp rp)
    have short := mul_lt_mul_of_pos_left shortage rp
    linarith only [t,short]
  have cut2 : Z*ρ^2*(r:ℝ)^2 < r*((r:ℝ)/16) := by
    have t := mul_lt_mul_of_pos_right (lt_of_lt_of_le guards (min_le_right ..)) (mul_pos rp rp)
    linarith only [t]
  have result := untruncated_eligibility (A:=total) rp (show 0 ≤ Z*ρ^2*(r:ℝ)^2 by positivity) cut1 cut2
  have unit_eq : Z*ρ^2*(r:ℝ)^2/r = Z*ρ^2*r := by field_simp
  rw [unit_eq] at result
  apply result
  intro extra
  have dp : 0 < Δ := by linarith only [shortage,rp]
  let p := Δ/total
  have hp : 0 ≤ p := div_nonneg dp.le (dp.trans extra).le
  have hp1 : p ≤ 1 := (div_le_one (dp.trans extra)).mpr extra.le
  let μ := senderLaw T E I S.s p (retry_rate_of_scale S.scale_lo) hp hp1
  have m : (product μ).expect (markCount H) = Δ := by
    rw [sender_count_at_rate]
    exact div_mul_cancel₀ _ (dp.trans extra).ne'
  let budget := sampleRepairBudget (targetGraph T.color T.target) I (rowList T E) H
    (uniqueGroup T E I S.s) L S.s r μ (representativeFactor X)
  have envelope := normalized_repair_budget T S prep hr no order lists band slots scale
    A X a0 a1 x0 x1 inc defi p hp hp1 κ k0 squares den Yhi ymax W Wcap
  change 0 ≤ Δ-(product μ).expect (markCount H) → budget ≤
    normalizedRepairBound a b κ V' W ((Δ-(product μ).expect (markCount H))/(ρ*r)) η*(ρ*r)^2 at envelope
  simp only [m,sub_self,le_refl,zero_div,true_implies] at envelope
  change budget ≤ P*(ρ*r)^2 at envelope
  have pass := oversampling_pass T prep (by omega) no S band slots scale X x0 (by linarith only [x1]) defi 2 (by norm_num) dp extra
  change r*min (total-Δ) (min (Δ/128) ((r:ℝ)/16)) ≤ 2*(2:ℝ)^2*budget+2*r*(S.s:ℝ)^2 at pass
  have error : r*(S.s:ℝ)^2 ≤ η*(ρ*r)^2 :=
    oversample_scale_error rp sp (by positivity) scale.le
  change _ ≤ (8*P+2*η)*ρ^2*(r:ℝ)^2
  linarith only [pass,envelope,error]

end
end Erdos617.ColoredLists
