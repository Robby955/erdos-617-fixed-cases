import CutInputs
import MixedSenderCapacity

/-! The final signed inequality on the width selection from the coloring. -/

namespace Erdos617.ColoredLists

open Finset PruningOverlap PackingLists FiniteLaw MarkedSender RepresentativeRepairs
open scoped Classical
noncomputable section

def secondPassWeight (A X Y κ ex : ℝ) : ℝ :=
  let g := X/(9/40)
  let Z := oversampleFactor A X Y κ (2*κ) ex
  (1/(1-X/1120)+(501/1000)*g/37)*κ+g*Z*((9/40)/1120)/37

def signedEpsilon (A X Y κ ex l : ℝ) : ℝ :=
  let a := heavyTestWeight A X
  let b := uniqueTestWeight A X
  let V := a*((513/512)*Y/(9/40)+7/1120)+9*b/1120
  let η := 1/((2:ℝ)^ex*(9/40)^2)
  normalizedRepairBound a b κ V (secondPassWeight A X Y κ ex) l η +
    X/(9/40)*l+l^2/2+η*(1/2+1/(2*1120))

def signedMargin (A X Y κ ex l : ℝ) : ℝ :=
  let ρ₀ := (9/40:ℝ)/1120
  let Z := oversampleFactor A X Y κ (secondPassWeight A X Y κ ex) ex
  (1-signedEpsilon A X Y κ ex l)*(3/20-(501/1000)*κ*ρ₀) +
    l-(501/1000)*κ-Z*ρ₀-1/((9/40)*(2:ℝ)^ex*1120^2)

/-- Bound the final additive cost from the variance of the marked count
in units of ρr². -/
private theorem fluctuation_cost {s r R m : ℝ} (slo : 1120 ≤ s) (rp : 0 < r)
    (Rpos : 0 < R) (scale : R*s^4 ≤ r) (mc : m ≤ s*r) :
    m ≤ (1/((9/40)*R*1120^2))*(((9/40)/s*r)*r) := by
  have sp : 0 < s := by linarith
  have sq := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1120) slo 2
  have bound := mul_le_mul_of_nonneg_left sq (show 0 ≤ R*s^2 by positivity)
  apply mc.trans
  field_simp [sp.ne', Rpos.ne']
  linarith only [scale,bound]

variable {V : Type*} {r : ℕ} [Fintype V] (T : Trace V r)

/-- For every box enclosing the actual selected width, a coloring without
a witness supplies an l in the certificate interval. If its one-row cost
is at most one, the manuscript's expression (5) is nonpositive. -/
theorem coloring_signed_cut {Ycap : ℝ} (prep : CutInputs T Ycap) (hr : 3 ≤ r) (no : ¬Witness T.color)
    (order : Fintype.card V = r^2+1) {E : Finset V} {e t : ℕ} {α β M Y ex : ℝ}
    (lists : ListBounds (targetGraph T.color T.target) T.row univ (live T) (range r) (qualifying T) E r)
    (S : WidthIntegral.Selection (ordinaryLists T E) (rowDeficit T E) (rowIncidence T E) e t α β M)
    (band : RetainedWidth.Band Y ex α β) (slots : e+(ordinaryLists T E).card=r)
    (scale : (2:ℝ)^ex*(S.s:ℝ)^4 < r)
    (A X : ℝ) (a0 : 0 ≤ A) (a1 : A ≤ 656/4000) (x0 : 0 ≤ X) (x1 : X ≤ 1/2)
    (inc : α*S.w ≤ A) (defi : 2*β*S.w ≤ X)
    (κ Yhi : ℝ) (k0 : 0 ≤ κ) (k1 : κ ≤ 1/4) (y0 : 0 ≤ Yhi) (y1 : Yhi ≤ 2)
    (squares : 4*β^2*S.w*(1-S.w) ≤ κ*(9/40))
    (ymax : Ycap ≤ Yhi)
    (shortage : (3/20:ℝ)*r < ((S.s-1:ℕ):ℝ)*r-(lowExterior T E S.retained S.s).card) :
    ∃ l : ℝ, 0 ≤ l ∧ l ≤ (501/1000)*κ ∧
      (signedEpsilon A X Yhi κ ex l ≤ 1 → signedMargin A X Yhi κ ex l ≤ 0) := by
  let I := S.retained
  let s := S.s
  let H := senderSet T E I s
  let L := lowExterior T E I s
  let Δ := ((s-1:ℕ):ℝ)*r-L.card
  let total := ∑ y ∈ H, senderEligibility T E I s y
  let p := min 1 (Δ/total)
  let ρ := (9/40:ℝ)/s
  let unit := ρ*r
  let ρ₀ := (9/40:ℝ)/1120
  let R := (2:ℝ)^ex
  let W := secondPassWeight A X Yhi κ ex
  let Z := oversampleFactor A X Yhi κ W ex
  let a := heavyTestWeight A X
  let b := uniqueTestWeight A X
  let V' := a*((513/512)*Yhi/(9/40)+7/1120)+9*b/1120
  let η := 1/(R*(9/40)^2)
  have rp : (0:ℝ)<r := by exact_mod_cast (show 0<r by omega)
  have sn : 0 < s := by have := S.scale_lo; change 0 < S.s; omega
  have slo : (1120:ℝ) ≤ s := by exact_mod_cast S.scale_lo
  have sp : (0:ℝ) < s := by exact_mod_cast sn
  have ρpos : 0 < ρ := by dsimp [ρ]; positivity
  have small : ρ ≤ ρ₀ := div_le_div_of_nonneg_left (by norm_num) (by norm_num) slo
  have up : 0 < unit := mul_pos ρpos rp
  obtain ⟨_,hp,hp1,min_eq,u0,uc,_,mc⟩ :=
    eligible_thinning T prep hr no order lists S band slots shortage
  let laws := senderLaw T E I s p (retry_rate_of_scale S.scale_lo) hp.le hp1
  let μ := product laws
  let m := μ.expect (markCount H)
  let l := (Δ-m)/unit
  have m_eq : m=p*total := sender_count_at_rate T E I s p _ hp.le hp1
  change p*total=min total Δ at min_eq
  rw [← m_eq] at min_eq
  change 0 ≤ Δ-p*total at u0
  change Δ-p*total ≤ (501/1000:ℝ)*(4*β^2*S.w*(1-S.w)/s)*r at uc
  change p*total ≤ (s:ℝ)*r at mc
  rw [← m_eq] at u0 uc mc
  have weighted : 4*β^2*S.w*(1-S.w)/s ≤ κ*ρ := by
    dsimp only [ρ]
    rw [← mul_div_assoc,div_le_div_iff_of_pos_right sp]
    exact squares
  have ucap : Δ-m ≤ (501/1000)*κ*unit := by
    dsimp only [unit]
    linarith only [uc,mul_le_mul_of_nonneg_right weighted rp.le]
  have l0 : 0 ≤ l := div_nonneg u0 up.le
  have l1 : l ≤ (501/1000)*κ := (div_le_iff₀ up).mpr ucap
  refine ⟨l,l0,l1,?_⟩
  let ε := signedEpsilon A X Yhi κ ex l
  intro eps1
  change ε ≤ 1 at eps1
  obtain ⟨_,Wcap,extra⟩ := two_oversampling_passes T prep hr no order lists S band slots scale
    A X a0 a1 x0 x1 inc defi κ Yhi k0 k1 y0 y1 squares ymax shortage
  change max (total-Δ) 0 ≤ Z*ρ^2*r at extra
  have surplus : total-m ≤ Z*ρ^2*r := by
    rw [min_eq]
    rcases le_total total Δ with h | h
    · rw [min_eq_left h,sub_self]; exact (le_max_right ..).trans extra
    · rw [min_eq_right h]; exact (le_max_left ..).trans extra
  have den := (oversample_guards band a0 a1 x0 x1 y0 y1 k0 k1
    (show (0:ℝ) ≤ 2*κ by positivity) (show 2*κ ≤ 1 by linarith only [k1])).1
  let P := normalizedRepairBound a b κ V' W l η
  have budget := normalized_repair_budget T S prep hr no order lists band slots scale
    A X a0 a1 x0 x1 inc defi p hp.le hp1 κ k0 squares den Yhi ymax W Wcap u0
  have cut (i) (hi : i ∈ I) := normalized_one_row_cut T prep (by omega) no lists S band slots
    scale p hp.le hp1 X P x0 (by linarith only [x1]) defi i hi u0 budget
  have ε0 : 0 ≤ ε := by
    obtain ⟨alo,_,blo,_⟩ := test_weight_bounds a0 a1 x0 x1
    have apos : 0 < a-4/3 := sub_pos.mpr alo
    have apositive : 0 ≤ a := by linarith only [apos]
    have bpositive : 0 ≤ b := (zero_le_one.trans (representativeFactor_one x0 (by linarith only [x1]))).trans blo
    have Vpos : 0 ≤ V' := by dsimp only [V']; positivity
    have hd : 0 < 2-a*κ := den
    have ηp : 0 ≤ η := by dsimp [η,R]; positivity
    change 0 ≤ normalizedRepairBound a b κ V' W l η+X/(9/40)*l+l^2/2+η*(1/2+1/(2*1120))
    unfold normalizedRepairBound
    positivity
  have costs := moderate_square_sum T E I s sn (by omega) μ ε ε0 cut
  have cap := mixed_sender_capacity T prep hr no order lists S band slots p hp.le hp1
  let σ := ∑ i ∈ I, ((r:ℝ)-(rowList T E i).card)^2
  let v := fun i ↦ μ.expect (markCount (moderateGroup T E I s i))
  change r*(1+Δ-total)+unit*m ≤ (501/1000:ℝ)*σ+(∑ i ∈ I, (v i)^2)+m at cap
  change (∑ i ∈ I, (v i)^2) ≤ ε*unit*m at costs
  have d_eq (i : ℕ) : (r:ℝ)-(rowList T E i).card = rowDeficit T E i*r := by
    dsimp [rowDeficit]; field_simp
  have σcap : σ ≤ κ*unit*r := by
    dsimp only [σ]
    simp_rw [d_eq,mul_pow,← sum_mul]
    have sqs := S.squares
    change s*(∑ i ∈ I, (rowDeficit T E i)^2) ≤ _ at sqs
    have h : (∑ i ∈ I, (rowDeficit T E i)^2) ≤ κ*ρ := by
      apply le_trans _ weighted
      rw [le_div_iff₀ sp,mul_comm]; exact sqs
    dsimp only [unit]
    linarith only [mul_le_mul_of_nonneg_right h (sq_nonneg (r:ℝ))]
  have Rpos : 0 < R := by dsimp [R]; positivity
  have mcost := fluctuation_cost slo rp Rpos scale.le mc
  change m ≤ 1/((9/40)*R*1120^2)*(unit*r) at mcost
  have lower : (3/20-(501/1000)*κ*ρ₀)*r ≤ m := by
    change (3/20:ℝ)*r < Δ at shortage
    change Δ-m ≤ (501/1000)*κ*(ρ*r) at ucap
    have cmp : κ*ρ*(r:ℝ) ≤ κ*ρ₀*r :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left small k0) rp.le
    linear_combination shortage.le + ucap + (501/1000:ℝ)*cmp
  have Znon : 0 ≤ Z := nonneg_of_mul_nonneg_left
    (show 0 ≤ Z*(ρ^2*r) by linarith only [(le_max_right (total-Δ) 0).trans extra]) (by positivity)
  have loss : (total-m)*r ≤ Z*ρ₀*(unit*r) := by
    dsimp only [unit]
    linarith only [mul_le_mul_of_nonneg_right surplus rp.le,
      mul_le_mul_of_nonneg_right small (show 0 ≤ Z*ρ*(r:ℝ)^2 by positivity)]
  have lunit : l*unit=Δ-m := div_mul_cancel₀ _ up.ne'
  have positive : 0 < unit*(r:ℝ) := mul_pos up rp
  change (1-ε)*(3/20-(501/1000)*κ*ρ₀)+l-(501/1000)*κ-Z*ρ₀-1/((9/40)*R*1120^2) ≤ 0
  apply le_of_mul_le_mul_right _ positive
  have base := mul_le_mul_of_nonneg_left lower (mul_nonneg (sub_nonneg.mpr eps1) up.le)
  have balance := congrArg (fun x:ℝ ↦ x*(r:ℝ)) lunit
  linear_combination cap + costs + (501/1000:ℝ)*σcap + mcost + loss + base + balance + rp.le

end
end Erdos617.ColoredLists
