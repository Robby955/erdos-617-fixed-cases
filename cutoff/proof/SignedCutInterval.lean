import FinalSignedCut

/-! Positivity at both endpoints excludes the entire shortage interval. -/

namespace Erdos617.ColoredLists

noncomputable section

private theorem square_chord {t : ℝ} (t0 : 0 ≤ t) (t1 : t ≤ 1) (d h : ℝ) :
    (d+t*h)^2 ≤ (1-t)*d^2+t*(d+h)^2 := by
  linarith only [mul_nonneg (mul_nonneg t0 (sub_nonneg.mpr t1)) (sq_nonneg h)]

/-- Every possible normalized shortage is a convex combination of the two
endpoints. The one-row cost lies below its chord and the margin above its chord. -/
theorem signed_interval {A X Y κ ex l : ℝ}
    (a0 : 0 ≤ A) (a1 : A ≤ 656/4000) (x0 : 0 ≤ X) (x1 : X ≤ 1/2)
    (k0 : 0 ≤ κ) (k1 : κ ≤ 1/4) (l0 : 0 ≤ l) (l1 : l ≤ (501/1000)*κ)
    (left : signedEpsilon A X Y κ ex 0 < 1 ∧ 0 < signedMargin A X Y κ ex 0)
    (right : signedEpsilon A X Y κ ex ((501/1000)*κ) < 1 ∧
      0 < signedMargin A X Y κ ex ((501/1000)*κ)) :
    signedEpsilon A X Y κ ex l ≤ 1 ∧ 0 < signedMargin A X Y κ ex l := by
  let h := (501/1000:ℝ)*κ
  by_cases pos : 0 < h
  · let t := l/h
    have t0 : 0 ≤ t := div_nonneg l0 pos.le
    have t1 : t ≤ 1 := (div_le_one pos).mpr l1
    have lt_eq : t*h=l := div_mul_cancel₀ _ pos.ne'
    let a := heavyTestWeight A X
    let b := uniqueTestWeight A X
    let W := secondPassWeight A X Y κ ex
    let V := a*((513/512)*Y/(9/40)+7/1120)+9*b/1120
    let η := 1/((2:ℝ)^ex*(9/40)^2)
    let k := (4/3)/(a-4/3)
    let D := 2-a*κ
    let g := X/(9/40)
    let tail := η*(((1+V)^2+V/1120)/2+1/(2*1120))
    let slack := η*(1/2+1/(2*1120))
    let ε := signedEpsilon A X Y κ ex
    have apos : 0 < a-4/3 := sub_pos.mpr (test_weight_bounds a0 a1 x0 x1).1
    have dpos : 0 < D := by
      have cap : a ≤ 5/2 := min_le_left ..
      dsimp only [D]
      linarith only [mul_le_mul cap k1 k0 (by norm_num : (0:ℝ) ≤ 5/2)]
    have coeff : 0 ≤ k/D := by dsimp only [k]; positivity
    have expand (z : ℝ) : ε z = (k/D)*(b*W+z)^2+k*tail+g*z+z^2/2+slack := by
      change k*((b*W+z)^2/D+tail)+g*z+z^2/2+slack = _
      ring
    have chord : ε l ≤ (1-t)*ε 0+t*ε h := by
      rw [← lt_eq]
      simp only [expand]
      have first := mul_le_mul_of_nonneg_left (square_chord t0 t1 (b*W) h) coeff
      have second := square_chord t0 t1 0 h
      linarith only [first,second]
    have left_e : ε 0 ≤ 1 := left.1.le
    have right_e : ε h ≤ 1 := right.1.le
    have low : 0 ≤ 1-t := sub_nonneg.mpr t1
    refine ⟨by linarith only [chord,mul_le_mul_of_nonneg_left left_e low,
      mul_le_mul_of_nonneg_left right_e t0],?_⟩
    let c := (3/20:ℝ)-(501/1000)*κ*((9/40)/1120)
    have c0 : 0 ≤ c := by dsimp [c]; linarith only [k1]
    let z := oversampleFactor A X Y κ W ex*((9/40)/1120)+1/((9/40)*(2:ℝ)^ex*1120^2)
    let margin := fun w ↦ (1-ε w)*c+w-h-z
    have ml : 0 < margin 0 := by
      have h' := left.2
      change 0 < (1-ε 0)*c+0-h-_-_ at h'
      dsimp only [margin,z]
      linarith only [h']
    have mr : 0 < margin h := by
      have h' := right.2
      change 0 < (1-ε h)*c+h-h-_-_ at h'
      dsimp only [margin,z]
      linarith only [h']
    have below : (1-t)*margin 0+t*margin h ≤ margin l := by
      dsimp only [margin]
      linarith only [mul_le_mul_of_nonneg_right chord c0,lt_eq]
    have posMix : 0 < (1-t)*margin 0+t*margin h := by
      by_cases tz : t=0
      · simpa [tz] using ml
      · exact add_pos_of_nonneg_of_pos (mul_nonneg low ml.le)
          (mul_pos (lt_of_le_of_ne t0 (Ne.symm tz)) mr)
    have final := posMix.trans_le below
    change 0 < (1-ε l)*c+l-h-_-_
    dsimp only [margin,z] at final
    linarith only [final]
  · have hl : l=0 := le_antisymm (l1.trans (le_of_not_gt pos)) l0
    rw [hl]
    exact ⟨left.1.le,left.2⟩

end
end Erdos617.ColoredLists
