import ThirdPruningCells
import CommonWidth

/-! The exponent-143 scale, and the two width comparisons for a stopped
trace with at least one independent pair. -/
namespace Erdos617.ThirdPruning
open Finset WidthIntegral WidthEndpoint
noncomputable section

def scale (b : ℝ) := (2:ℝ)^((143-b)/4)
def margin (p t b α β : ℝ) := Real.log (scale b /1120) -
  ((2-p/2-(199/400)*t)/α + (p+t)/β) + WidthEndpoint.saving p

private theorem logK : Real.log 1120 ≤ 10*Real.log 2 + 8963/100000 := by
  have small : Real.log (35/32) ≤ 8963/100000 := by
    apply (Real.log_le_iff_le_exp (by norm_num)).2
    have exp := Real.sum_le_exp_of_nonneg (x := (8963:ℝ)/100000) (by norm_num) 4
    norm_num [Finset.sum_range_succ,Nat.factorial] at exp
    linarith
  rw [show (1120:ℝ) = 2^10*(35/32) by norm_num,Real.log_mul (by norm_num) (by norm_num),Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  linarith only [small]

theorem rational_margin {p t b α β : ℝ} (hp : 0 ≤ p) (hpc : p ≤ 125/61)
    (band : RetainedWidth.Band (2-p/2-(199/400)*t) b α β) :
    ((143-b)/4-10)*(69314718/100000000)-8963/100000-
      (2-p/2-(199/400)*t)/α-(p+t)/β+(349+114*p)/1000 ≤ margin p t b α β := by
  have reb : (349+114*p)/1000 ≤ WidthEndpoint.saving p := rebate_line hp hpc
  have lo := Real.log_two_gt_d9
  unfold margin scale
  rw [Real.log_div (by positivity) (by norm_num),Real.log_rpow (by norm_num)]
  cases band <;> linarith only [logK,reb,lo]

theorem paired_margin {p t b α β z s e k : ℝ} (hp : 0 ≤ p) (hpc : p ≤ 125/61)
    (ht : 0 ≤ t) (hz : z = 1-p/4-(199/400)*t) (hs : 0 ≤ s) (he : 0 ≤ e)
    (spent : s+e+(9/25)*k ≤ z) (band : RetainedWidth.Band (2-p/2-(199/400)*t) b α β)
    (old : margin p t b α β+2*s/α ≤ 0) :
    0 < margin p t b α β + (2*(199/400-9/25)-k)/β + (2*s+(9/25)*k)/α ∧
    p+t+k+(1/2-2*(199/400-9/25)) < 353/100 := by
  have estimate := rational_margin hp hpc band
  cases band <;> constructor <;> linarith

theorem scale_fourth (b : ℝ) : (2:ℝ)^b*(scale b)^4 = (2:ℝ)^143 := by
  unfold scale
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2),
    ← Real.rpow_add (by norm_num : (0:ℝ)<2)]
  norm_num

/-- Any verified improvement in the incidence/deficit budget can be applied
to the existing width selection at the new scale. -/
theorem selected_at_143 {ι : Type*} [DecidableEq ι] (rows : Finset ι) (x y : ι → ℝ)
    (e₀ n r : ℕ) {p t b α β C : ℝ} (band : RetainedWidth.Band (2-p/2-(199/400)*t) b α β)
    (hp : 0 ≤ p) (hpc : p ≤ 125/61) (hn : n ≤ 1411) (hr : 2^143 ≤ r)
    (hx : ∀ i ∈ rows, 0 ≤ x i) (hy : ∀ i ∈ rows, 0 ≤ y i)
    (slots : e₀+rows.card=r) (omissions : (e₀:ℝ)+1 ≤ 729-(1464/5)*p+n)
    (budget : RowBudget rows x y n α β C)
    (width : C-saving p < Real.log (scale b/1120)) :
    ∃ S : Selection rows x y e₀ n α β (scale b), (2:ℝ)^b*(S.s:ℝ)^4 < r := by
  have hs : 8*(1120+2*(n:ℝ)) ≤ scale b := by
    calc
      _ ≤ (2:ℝ)^(16:ℕ) := by
        have h : (n:ℝ) ≤ 1411 := by exact_mod_cast hn
        norm_num; linarith
      _ = (2:ℝ)^(16:ℝ) := (Real.rpow_natCast ..).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by cases band <;> norm_num)
  obtain ⟨S⟩ := at_scale rows x y e₀ n hp hpc (by cases band <;> norm_num)
    (by cases band <;> norm_num) hx hy (by omega) omissions budget
    (by cases band <;> norm_num) hs width
  refine ⟨S,?_⟩
  calc (2:ℝ)^b*(S.s:ℝ)^4 < (2:ℝ)^b*(scale b)^4 :=
         mul_lt_mul_of_pos_left (pow_lt_pow_left₀ S.scale_hi (by positivity) (by norm_num)) (by positivity)
       _ = _ := scale_fourth b
       _ ≤ _ := by exact_mod_cast hr

end
end Erdos617.ThirdPruning
