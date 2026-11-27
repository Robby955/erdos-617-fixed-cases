import RowWidth
import WidthEndpoint
import RetainedWidth
import WeightedWidth

/-! One threshold for the three bounds in Appendix A, equation (4). -/

open Set
open Erdos617.WidthEndpoint

namespace Erdos617.WidthIntegral

variable {ι : Type*}

/-- The row budget pays for the integral at both ends. Here k is the fraction
of reserved rows, v is n/1120, and the rebate includes the logarithmic change
of normalization. B is the total budget after that change. -/
private theorem choose_level (rows : Finset ι) (a q : ι → ℝ) {m l u p k v rebate B : ℝ}
    (hm : 0 < m) (hl : 0 < l) (hl' : l ≤ 1/8) (hu : 0 ≤ u)
    (ha : ∀ i ∈ rows, 0 ≤ a i) (hq : ∀ i ∈ rows, 0 ≤ q i)
    (cap : ∀ i ∈ rows, q i ≤ (a i)^2/m) (upper : ∀ i ∈ rows, a i ≤ u)
    (hp : 0 ≤ p) (hp' : p ≤ 125/61)
    (hv : 0 ≤ v) (hk : min (fraction p) (1/2) ≤ k)
    (hk' : fraction p-v ≤ k) (hr : 3/5*v ≤ rebate)
    (budget : (∑ i ∈ rows, (a i/m + q i/a i)) + k*u + rebate ≤ B)
    (margin : B-saving p < -Real.log l) :
    ∃ t ∈ Icc l 1, t + ∑ i ∈ rows, load m (a i) (q i) t < 1 := by
  by_contra! failure
  let C := ∑ i ∈ rows, (a i/m + q i/a i)
  let A := ∑ i ∈ rows, q i
  have hcost : C + k*u + rebate ≤ B := budget
  have integral (h : ℝ) (lh : l ≤ h) (hh : h ≤ 1) :=
    failure_budget rows a q hm hl lh ha hq cap
      (fun x hx ↦ failure x ⟨hx.1, hx.2.trans hh⟩)
  have past (h : ℝ) (lh : l ≤ h) (uh : u ≤ h) (hh : h ≤ 1) :
      -Real.log l ≤ C - (1-h+A/h+Real.log h) := by
    have he : (∑ i ∈ rows, tail m (a i) (q i) h) = A/h := by
      rw [show A/h = ∑ i ∈ rows, q i/h by rw [← Finset.sum_div]]
      apply Finset.sum_congr rfl
      intro i hi
      simp [tail, max_eq_right ((upper i hi).trans uh)]
    simpa only [he] using integral h lh hh
  have at_level (h : ℝ) (lh : l ≤ h) (uh : u ≤ h) (hh : h ≤ 1) : 1 ≤ h + A/h := by
    have he : (∑ i ∈ rows, load m (a i) (q i) h) = A/h := by
      rw [show A/h = ∑ i ∈ rows, q i/h by rw [← Finset.sum_div]]
      apply Finset.sum_congr rfl
      intro i hi
      simp [load, not_lt.mpr ((upper i hi).trans uh)]
    simpa only [he] using failure h ⟨lh, hh⟩
  have basic : -Real.log l ≤ C := by
    have hs : 0 ≤ ∑ i ∈ rows, tail m (a i) (q i) 1 := by
      apply Finset.sum_nonneg
      intro i hi
      exact add_nonneg (div_nonneg (sub_nonneg.mpr (le_max_right _ _)) hm.le)
        (div_nonneg (hq i hi) (le_trans zero_le_one (le_max_right _ _)))
    have h := integral 1 (by linarith) le_rfl
    simp only [sub_self, zero_add, Real.log_one, add_zero] at h
    change -Real.log l ≤ C - _ at h
    linarith
  have hk₀ : 0 ≤ k := by
    exact (le_min (by dsimp [fraction]; linarith) (by norm_num)).trans hk
  have hr₀ : 0 ≤ rebate := by linarith
  have hhigh : saving p ≤ k+rebate := by
    by_cases low : fraction p ≤ 1/2
    · rw [min_eq_left low] at hk
      exact (min_le_left _ _).trans (by linarith)
    · rw [min_eq_right (le_of_not_ge low)] at hk
      have hb := RetainedWidth.reserved_endpoint hk hk' hr
      apply (min_le_right _ _).trans (le_trans ?_ hb)
      dsimp [fraction,affine] at *
      push Not at low
      linarith only [low, hp']
  have hhalf : u ≤ 1/2 → 1/4 ≤ A := by
    intro hu'
    have h := at_level (1/2) (by linarith) hu' (by norm_num)
    linarith
  have hreb {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1/2) :
      fraction p*x ≤ k*x+rebate := by
    nlinarith only [mul_le_mul_of_nonneg_right hk' hx,
      mul_le_mul_of_nonneg_left hx' hv, hr, hv]
  by_cases first : u ≤ 1/8
  · have hs := past (1/8) hl' first (by norm_num)
    have hA := hhalf (by linarith)
    have hlog : Real.log (1/8) = -3*Real.log 2 := by
      rw [one_div, Real.log_inv, show (8:ℝ) = 2^3 by norm_num, Real.log_pow]
      ring
    rw [hlog] at hs
    have hsav : saving p ≤ 3/4 := (min_le_right _ _).trans (by dsimp [affine]; linarith)
    linarith only [hs, hA, hsav, margin, hcost, mul_nonneg hk₀ hu, hr₀, Real.log_two_lt_d9]
  by_cases second : u ≤ 1/2
  · have hu₀ : 0 < u := by linarith
    have hs := past u (by linarith) le_rfl (by linarith)
    have hA : 1/(4*u) ≤ A/u := by
      rw [← div_div]
      exact div_le_div_of_nonneg_right (hhalf second) hu₀.le
    have hsmall := small hu₀ second hp hp'
    have hsav : saving p ≤ affine p := min_le_right _ _
    linarith only [hs, hA, hsmall, hsav, margin, hcost, hreb hu second]
  by_cases third : u ≤ 1
  · have hs := past u (by linarith) le_rfl third
    have he := at_level u (by linarith) le_rfl third
    have hmid : saving p ≤ 1+Real.log (1/2)+k*(1/2)+rebate := by
      have h := small (u := 1/2) (by norm_num) le_rfl hp hp'
      have hr' := hreb (x := 1/2) (by norm_num) le_rfl
      apply (min_le_right _ _).trans
      linarith only [h, hr']
    have hsec := log_secant (le_of_not_ge second) third
    have hmix := add_nonneg
      (mul_nonneg (show 0 ≤ 2*(1-u) by linarith) (sub_nonneg.mpr hmid))
      (mul_nonneg (show 0 ≤ 2*u-1 by linarith) (sub_nonneg.mpr hhigh))
    linarith only [hmix, hsec, hs, he, margin, hcost]
  · have hku : k ≤ k*u := by nlinarith only [mul_nonneg hk₀ (sub_nonneg.mpr (le_of_not_ge third))]
    linarith only [basic, margin, hcost, hku, hhigh]


/-- The combined budget in Appendix A (3). All ordinary rows enter the sum
before the heaviest rows are reserved. -/
def RowBudget (rows : Finset ι) (x y : ι → ℝ) (n : ℕ) (α β C : ℝ) : Prop :=
  (∑ i ∈ rows, y i)/α + (∑ i ∈ rows, x i)/β ≤
    C - ((1/200-1/256)/(2*β))*n


/-- Combine the corrected incidence count and the deficit count (2) into
budget (3). The incidence input accepts the stronger first-stage rebate from
the overlap proof. q counts chosen pairs, and n counts chosen and short rows. -/
theorem budget_of_counts (rows : Finset ι) (x y : ι → ℝ) (n r : ℕ)
    {Y b α β p t O a v a₁ q : ℝ} (band : RetainedWidth.Band Y b α β)
    (hr : 2 ≤ r) (hO : 0 ≤ O) (ha : 0 ≤ a) (hv : 0 ≤ v) (ha₁ : 0 ≤ a₁)
    (hq : q ≤ n/2)
    (incidence : (∑ i ∈ rows, y i) ≤ Y-2*v-2*(1-1/(r:ℝ))*O+(199/400)*a-(99/400)*a₁)
    (deficit : (∑ i ∈ rows, x i) + n/400 ≤ p+t+O-a+q/256) :
    RowBudget rows x y n α β (Y/α+(p+t)/β) := by
  have hα : 0 < α := by cases band <;> norm_num
  have hβ : 0 < β := by cases band <;> norm_num
  have hαβ : α ≤ β := by cases band <;> norm_num
  have hτ : (199/400)*β ≤ α := by cases band <;> norm_num
  have hr' : (2:ℝ) ≤ r := by exact_mod_cast hr
  have hinv : 1/(r:ℝ) ≤ 1/2 := (div_le_iff₀ (by linarith : (0:ℝ) < r)).2 (by linarith)
  have hpay := mul_le_mul_of_nonneg_right (show 1 ≤ 2*(1-1/(r:ℝ)) by linarith) hO
  have hi : (∑ i ∈ rows, y i) ≤ Y-O+(199/400)*a := by
    linarith only [incidence, hpay, hv, ha₁]
  have hd : (∑ i ∈ rows, x i) ≤ p+t+O-a+(n:ℝ)/512-n/400 := by
    linarith only [deficit,hq]
  have hc := WeightedWidth.omitted_incidences (Y := ∑ i ∈ rows, y i) (D := ∑ i ∈ rows, x i)
    (Y₀ := Y) (D₀ := p+t) (k := 1) (t := 199/400) (cost := ((1/200-1/256)/2)*n)
    (by simpa using hi) (by linarith only [hd]) hα.le hβ.le hO ha
    (by simpa using hαβ) (by linarith only [hτ])
  unfold RowBudget
  apply le_of_mul_le_mul_right _ (mul_pos hα hβ)
  field_simp
  linarith only [hc]

variable [DecidableEq ι]

/-- Extraction from the unpartitioned finite family. The log margin and scale
are numerical inputs, later discharged for the five bands. -/
theorem at_scale (rows : Finset ι) (x y : ι → ℝ) (e₀ n : ℕ) {p α β S C : ℝ}
    (hp : 0 ≤ p) (hp' : p ≤ 125/61) (hα : 0 < α) (hβ : 0 < β)
    (hx : ∀ i ∈ rows, 0 ≤ x i) (hy : ∀ i ∈ rows, 0 ≤ y i)
    (slots : 1120+2*n ≤ e₀+rows.card+1)
    (omissions : (e₀:ℝ)+1 ≤ 729-(1464/5)*p+n)
    (budget : RowBudget rows x y n α β C)
    (rate : (2+3/5)/1120 ≤ (1/200-1/256)/(2*β))
    (scale : 8*(1120+2*(n:ℝ)) ≤ S)
    (margin : C-saving p < Real.log (S/1120)) :
    Nonempty (Selection rows x y e₀ n α β S) := by
  classical
  let m : ℝ := 1120+2*(n:ℝ)
  have hm : 0 < m := by dsimp [m]; positivity
  have hS : 0 < S := by change 8*m ≤ S at scale; linarith
  let b := fun i ↦ y i/α
  let d := fun i ↦ x i/(2*β)
  let a := fun i ↦ weight m (b i) (d i)
  let q := fun i ↦ m*(d i)^2
  have hb (i) (hi : i ∈ rows) : 0 ≤ b i := div_nonneg (hy i hi) hα.le
  have hd (i) (hi : i ∈ rows) : 0 ≤ d i := div_nonneg (hx i hi) (by positivity)
  have hr (i) (hi : i ∈ rows) := row_cost hm (hb i hi) (hd i hi)
  have he₀ : e₀+1 ≤ 1120+2*n := by
    have h : (e₀:ℝ)+1 ≤ 1120+2*(n:ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) n]
    exact_mod_cast h
  obtain ⟨R, hR, hcR, horder⟩ := exists_heaviest rows a (1120+2*n-e₀-1) (by omega)
  have hcount : R.card+e₀+1 = 1120+2*n := by omega
  have hcountR : (R.card:ℝ)+e₀+1 = m := by dsimp [m]; exact_mod_cast hcount
  let pool := rows \ R
  have sub : pool ⊆ rows := Finset.sdiff_subset
  obtain ⟨u, hu, huu, hru⟩ : ∃ u : ℝ, 0 ≤ u ∧ (∀ i ∈ pool, a i ≤ u) ∧
      (∀ j ∈ R, u ≤ a j) := by
    by_cases h : pool.Nonempty
    · obtain ⟨i, hi, hmax⟩ := pool.exists_max_image a h
      exact ⟨a i, (hr i (sub hi)).1, hmax, horder i hi⟩
    · refine ⟨0, le_rfl, ?_, fun i hi ↦ (hr i (hR hi)).1⟩
      simp [Finset.not_nonempty_iff_eq_empty.mp h]
  let k := (R.card:ℝ)/m
  let v := (n:ℝ)/1120
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hl₁ : fraction p ≤ 1 := by dsimp [fraction]; linarith
  have floor : 1120*fraction p+(n:ℝ) ≤ (R.card:ℝ) := by
    dsimp [m] at hcountR
    dsimp [fraction]
    linarith only [hcountR, omissions]
  have hk : min (fraction p) (1/2) ≤ k := by
    apply (le_div_iff₀ hm).2
    dsimp [m]
    by_cases h : fraction p ≤ 1/2
    · rw [min_eq_left h]
      nlinarith only [floor, mul_le_mul_of_nonneg_right h (Nat.cast_nonneg (α := ℝ) n)]
    · rw [min_eq_right (le_of_not_ge h)]
      linarith only [floor, le_of_not_ge h]
  have hk' : fraction p-v ≤ k := by
    apply (le_div_iff₀ hm).2
    dsimp [v,m]
    nlinarith only [floor, mul_le_mul_of_nonneg_right hl₁ (Nat.cast_nonneg (α := ℝ) n),
      sq_nonneg (n:ℝ)]
  have paid : (∑ i ∈ pool, (a i/m+q i/a i)) + k*u ≤
      (∑ i ∈ rows, y i)/α + (∑ i ∈ rows, x i)/β := by
    have hp₁ := Finset.sum_le_sum (s := pool) (fun i hi ↦ (hr i (sub hi)).2.2)
    have hp₂ : k*u ≤ ∑ i ∈ R, (b i+2*d i) := by
      calc k*u = ∑ _i ∈ R, u/m := by simp [k]; ring
           _ ≤ _ := by
            apply Finset.sum_le_sum
            intro i hi
            have hh := div_le_div_of_nonneg_right (hru i hi) hm.le
            have hin : 0 ≤ q i/a i :=
              div_nonneg (mul_nonneg hm.le (sq_nonneg _)) (hr i (hR hi)).1
            have hc := (hr i (hR hi)).2.2
            change a i/m+q i/a i ≤ b i+2*d i at hc
            linarith only [hh, hin, hc]
    have hsum : (∑ i ∈ pool, (b i+2*d i)) + (∑ i ∈ R, (b i+2*d i)) =
        (∑ i ∈ rows, y i)/α+(∑ i ∈ rows, x i)/β := by
      rw [Finset.sum_sdiff hR, Finset.sum_add_distrib, Finset.sum_div, Finset.sum_div]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      dsimp [d]
      ring
    exact (add_le_add hp₁ hp₂).trans hsum.le
  let B := C-Real.log (m/1120)
  have hcharge : (∑ i ∈ pool, (a i/m+q i/a i)) + k*u + 3/5*v ≤ B := by
    have hl := Real.log_le_sub_one_of_pos (div_pos hm (by norm_num) : 0 < m/1120)
    change _ ≤ C-_*n at budget
    have h := mul_le_mul_of_nonneg_right rate (Nat.cast_nonneg (α := ℝ) n)
    dsimp [B,v]
    dsimp [m] at hl ⊢
    linarith only [paid, budget, h, hl]
  have hmargin : B-saving p < -Real.log (m/S) := by
    dsimp [B]
    rw [Real.log_div hm.ne' hS.ne', Real.log_div hm.ne' (by norm_num)]
    rw [Real.log_div hS.ne' (by norm_num)] at margin
    linarith only [margin]
  obtain ⟨t, ht, hs⟩ := choose_level pool a q hm (div_pos hm hS)
    ((div_le_iff₀ hS).2 (by change 8*m ≤ S at scale; linarith)) hu
    (fun i hi ↦ (hr i (sub hi)).1) (fun i _ ↦ mul_nonneg hm.le (sq_nonneg _))
    (fun i hi ↦ (hr i (sub hi)).2.1) huu hp hp' hv hk hk' le_rfl hcharge hmargin
  exact selection_of_level rows R x y e₀ n hα hβ hS hR hcount ht.1 ht.2 hs

/-- Appendix A (4) for the actual five bands. The input family satisfies (3)
and the omitted-slot count; no threshold, sorted family or integral inequality
is supplied. The last conclusion gives the scale bound used after (4). -/
theorem width_at_144 (rows : Finset ι) (x y : ι → ℝ) (e₀ n : ℕ)
    {p t Y b α β : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 125/61)
    (hpt : p/4+(199/400)*t ≤ 1) (hY : Y=2-p/2-(199/400)*t)
    (band : RetainedWidth.Band Y b α β) (hn : n ≤ 1411)
    (hx : ∀ i ∈ rows, 0 ≤ x i) (hy : ∀ i ∈ rows, 0 ≤ y i)
    (slots : 1120+2*n ≤ e₀+rows.card+1)
    (omissions : (e₀:ℝ)+1 ≤ 729-(1464/5)*p+n)
    (budget : RowBudget rows x y n α β (Y/α+(p+t)/β)) :
    ∃ T : Selection rows x y e₀ n α β ((2:ℝ)^((144-b)/4)),
      (2:ℝ)^b*(T.s:ℝ)^4 < 2^144 := by
  let S := (2:ℝ)^((144-b)/4)
  have ha : 0 < α := by cases band <;> norm_num
  have hb : 0 < β := by cases band <;> norm_num
  have rate : (2+3/5)/1120 ≤ (1/200-1/256)/(2*β) := by cases band <;> norm_num
  have hsize : 8*(1120+2*(n:ℝ)) ≤ S := by
    calc 8*(1120+2*(n:ℝ)) ≤ (2:ℝ)^(15:ℕ) := by
          have h : (n:ℝ) ≤ 1411 := by exact_mod_cast hn
          norm_num; linarith
         _ = (2:ℝ)^(15:ℝ) := (Real.rpow_natCast ..).symm
         _ ≤ S := Real.rpow_le_rpow_of_exponent_le (by norm_num)
           (by cases band <;> norm_num)
  have hm := RetainedWidth.five_width_comparisons hp' hpt hY band
  obtain ⟨T⟩ := at_scale rows x y e₀ n hp hp' ha hb hx hy slots omissions budget rate hsize
    (by dsimp [S,saving,fraction,affine]; linarith only [hm])
  refine ⟨T, ?_⟩
  have hpow : S^(4:ℕ) = (2:ℝ)^(144-b) := by
    dsimp [S]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
    congr 1
    ring
  calc (2:ℝ)^b*(T.s:ℝ)^4 < (2:ℝ)^b*S^4 :=
         mul_lt_mul_of_pos_left (pow_lt_pow_left₀ T.scale_hi (by positivity) (by norm_num)) (by positivity)
       _ = _ := by rw [hpow, ← Real.rpow_add (by norm_num : (0:ℝ) < 2),
                      show b+(144-b) = 144 by ring]; norm_num


/-- At the supplement's scale, the theorem also chooses the band from the
pruning parameters. The inputs are the scalar pruning bounds, the actual row
count, and the joint row budget for the available bands. -/
theorem width_at_reduced_cutoff (rows : Finset ι) (x y : ι → ℝ) (e₀ n r : ℕ)
    {p t : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 125/61) (ht : 0 ≤ t)
    (hpt : p/4+(199/400)*t ≤ 1) (hn : n ≤ 1411) (hr : 15*2^140 ≤ r)
    (hx : ∀ i ∈ rows, 0 ≤ x i) (hy : ∀ i ∈ rows, 0 ≤ y i)
    (count : e₀+rows.card = r) (omissions : (e₀:ℝ)+1 ≤ 729-(1464/5)*p+n)
    (budgets : ∀ b α β, RetainedWidth.Band (2-p/2-(199/400)*t) b α β →
      RowBudget rows x y n α β ((2-p/2-(199/400)*t)/α+(p+t)/β)) :
    ∃ b α β, RetainedWidth.Band (2-p/2-(199/400)*t) b α β ∧
      ∃ T : Selection rows x y e₀ n α β
        ((2:ℝ)^((144-b)/4) / ((16:ℝ)/15)^(1/4:ℝ)),
        (2:ℝ)^b*(T.s:ℝ)^4 < 15*(2:ℝ)^140 ∧ (2:ℝ)^b*(T.s:ℝ)^4 < r := by
  obtain ⟨b, α, β, band, cmp⟩ := RetainedWidth.reduced_width_for_every_pruning_pair hp hp' ht hpt
  let factor := ((16:ℝ)/15)^(1/4:ℝ)
  let S := (2:ℝ)^((144-b)/4) / factor
  have hfac : 0 < factor := by dsimp [factor]; positivity
  have hfac' : factor ≤ 2 := by
    calc factor ≤ ((16:ℝ)/15)^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
         _ ≤ 2 := by norm_num
  have ha : 0 < α := by cases band <;> norm_num
  have hb : 0 < β := by cases band <;> norm_num
  have rate : (2+3/5)/1120 ≤ (1/200-1/256)/(2*β) := by cases band <;> norm_num
  have size : 8*(1120+2*(n:ℝ)) ≤ S := by
    apply (le_div_iff₀ hfac).2
    calc 8*(1120+2*(n:ℝ))*factor ≤ 8*(1120+2*(n:ℝ))*2 :=
            mul_le_mul_of_nonneg_left hfac' (by positivity)
         _ ≤ (2:ℝ)^(16:ℕ) := by
           have h : (n:ℝ) ≤ 1411 := by exact_mod_cast hn
           norm_num; linarith
         _ = (2:ℝ)^(16:ℝ) := (Real.rpow_natCast ..).symm
         _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by cases band <;> norm_num)
  have slots : 1120+2*n ≤ e₀+rows.card+1 := by omega
  have he : S/1120 = (2:ℝ)^((144-b)/4) / (1120 * factor) := by dsimp [S]; ring
  obtain ⟨T⟩ := at_scale rows x y e₀ n hp hp' ha hb hx hy slots omissions
    (budgets _ _ _ band) rate size (by rw [he]; dsimp [saving,fraction,affine,factor]; linarith only [cmp])
  have hfinal : (2:ℝ)^b*(T.s:ℝ)^4 < 15*(2:ℝ)^140 := by
    calc (2:ℝ)^b*(T.s:ℝ)^4 < (2:ℝ)^b*S^4 :=
           mul_lt_mul_of_pos_left (pow_lt_pow_left₀ T.scale_hi (by positivity) (by norm_num)) (by positivity)
         _ = _ := RetainedWidth.fourth_power_of_reduced_scale b
  exact ⟨b, α, β, band, T, hfinal, hfinal.trans_le (by exact_mod_cast hr)⟩


/-- End-to-end row statement. The individual pruning charges and the two
vertex/edge counts supply both aggregate budgets. The theorem chooses the
band, reserved family and common threshold. -/
theorem width_from_row_counts {κ : Type*} [DecidableEq κ]
    (raw : Finset κ) (surplus U assigned : κ → ℝ)
    (rows : Finset ι) (x y : ι → ℝ) (e₀ n r : ℕ) {p t O a v a₁ q : ℝ}
    (hp : 0 ≤ p) (hp' : p ≤ 125/61) (ht : 0 ≤ t) (hpt : p/4+(199/400)*t ≤ 1)
    (hn : n ≤ 1411) (hr : 15*2^140 ≤ r) (count : e₀+rows.card = r)
    (hsurplus : ∀ i ∈ raw, 0 ≤ surplus i) (hassigned : ∀ i ∈ raw, 0 ≤ assigned i)
    (sizes : ∑ i ∈ raw, surplus i ≤ 1/2) (costs : ∑ i ∈ raw, U i ≤ 1/2)
    (loads : ∑ i ∈ raw, assigned i = p)
    (localCost : ∀ i ∈ raw, (61/250)*assigned i ≤ U i)
    (destination : ∀ i ∈ raw, 0 < assigned i → surplus i ≤ 1/256 ∧ U i ≤ 1/1200)
    (omitted : e₀ ≤ (unqualified raw surplus U).card+n)
    (hx : ∀ i ∈ rows, 0 ≤ x i) (hy : ∀ i ∈ rows, 0 ≤ y i)
    (hO : 0 ≤ O) (ha : 0 ≤ a) (hv : 0 ≤ v) (ha₁ : 0 ≤ a₁) (hq : q ≤ n/2)
    (incidence : (∑ i ∈ rows, y i) ≤
      (2-p/2-(199/400)*t)-2*v-2*(1-1/(r:ℝ))*O+(199/400)*a-(99/400)*a₁)
    (deficit : (∑ i ∈ rows, x i) + n/400 ≤ p+t+O-a+q/256) :
    ∃ b α β, RetainedWidth.Band (2-p/2-(199/400)*t) b α β ∧
      ∃ T : Selection rows x y e₀ n α β
        ((2:ℝ)^((144-b)/4) / ((16:ℝ)/15)^(1/4:ℝ)),
        (2:ℝ)^b*(T.s:ℝ)^4 < 15*(2:ℝ)^140 ∧ (2:ℝ)^b*(T.s:ℝ)^4 < r := by
  have hslots := omitted_slots_of_row_charges raw surplus U assigned e₀ n
    hsurplus hassigned sizes costs loads localCost destination omitted
  exact width_at_reduced_cutoff rows x y e₀ n r hp hp' ht hpt hn hr hx hy count hslots
    (fun _ _ _ band ↦ budget_of_counts rows x y n r band (by omega) hO ha hv ha₁ hq incidence deficit)

end Erdos617.WidthIntegral
