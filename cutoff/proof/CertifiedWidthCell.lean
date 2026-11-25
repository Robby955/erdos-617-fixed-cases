import SignedCutInterval
import CutoffCells

/-! Place the real width chosen on the coloring in a checked rational cell. -/

namespace Erdos617.CutoffCells

open ColoredLists
noncomputable section

/-- The boundaries cover the closed unit interval, including all shared endpoints. -/
theorem locate_width {w : ℝ} (lo : 0 ≤ w) (hi : w ≤ 1) :
    ∃ j : Fin 9, (left j : ℝ) ≤ w ∧ w ≤ (right j : ℝ) := by
  by_contra! none
  have walk : ∀ k : Fin 10, (boundaries k : ℝ) ≤ w := Fin.induction
    (by simpa [boundaries] using lo)
    (fun j before ↦ (none j before).le)
  have atLast := none 8 (walk (8 : Fin 9).castSucc)
  have last : right 8 = 1 := by decide +kernel
  rw [last,Rat.cast_one] at atLast
  exact (not_lt_of_ge hi) atLast

theorem band_index {Y ex α β : ℝ} (band : RetainedWidth.Band Y ex α β) :
    ∃ i : Fin 5, ex=((bandData i).exponent:ℝ) ∧ α=((bandData i).α:ℝ) ∧
      β=((bandData i).β:ℝ) ∧ Y ≤ ((bandData i).y:ℝ) := by
  cases band with
  | first _ hi => exact ⟨0, by norm_num [bandData], by norm_num [bandData], by norm_num [bandData], by simpa [bandData] using hi⟩
  | second _ hi => exact ⟨1, by norm_num [bandData], by norm_num [bandData], by norm_num [bandData], by simpa [bandData] using hi⟩
  | third _ hi => exact ⟨2, by norm_num [bandData], by norm_num [bandData], by norm_num [bandData], by simpa [bandData] using hi⟩
  | fourth _ hi => exact ⟨3, by norm_num [bandData], by norm_num [bandData], by norm_num [bandData], by simpa [bandData] using hi⟩
  | fifth _ hi => exact ⟨4, by norm_num [bandData], by norm_num [bandData], by norm_num [bandData], by simpa [bandData] using hi⟩

private theorem values_cast (A X Y κ R l : ℚ) :
    ((values A X Y κ R l).1:ℝ) = (values (A:ℝ) X Y κ R l).1 ∧
    ((values A X Y κ R l).2:ℝ) = (values (A:ℝ) X Y κ R l).2 := by
  dsimp only [values]
  push_cast [Rat.cast_min]
  exact ⟨rfl,rfl⟩

/-- Transfer both rational endpoint comparisons to exactly the functions
in the graph inequality, including the real power of two in its error term. -/
theorem real_endpoints (i : Fin 5) (j : Fin 9) :
    let d := bandData i
    let A := (incidence d j : ℝ)
    let X := (deficit d j : ℝ)
    let κ := (kappa d j : ℝ)
    let test := fun l ↦ signedEpsilon A X d.y κ d.exponent l < 1 ∧
      0 < signedMargin A X d.y κ d.exponent l
    test 0 ∧ test ((501/1000)*κ) := by
  intro d A X κ test
  have transfer (l : ℚ) (h : (endpoint d j l).1 < 1 ∧ 0 < (endpoint d j l).2) : test l := by
    have eps : ((endpoint d j l).1:ℝ) < 1 := by exact_mod_cast h.1
    have margin : 0 < ((endpoint d j l).2:ℝ) := by exact_mod_cast h.2
    unfold endpoint at eps margin
    obtain ⟨eq1,eq2⟩ := values_cast (incidence d j) (deficit d j) d.y (kappa d j) (2^d.exponent) l
    rw [eq1] at eps
    rw [eq2] at margin
    push_cast at eps margin
    change signedEpsilon A X d.y κ d.exponent l < 1 ∧ 0 < signedMargin A X d.y κ d.exponent l
    simp only [signedMargin,signedEpsilon,secondPassWeight,oversampleFactor,Real.rpow_natCast]
    exact ⟨eps,margin⟩
  obtain ⟨start,finish⟩ := all_cells_pass i j
  constructor
  · simpa only [Rat.cast_zero] using transfer 0 start
  · have endpt := transfer ((501/1000)*kappa d j) finish
    push_cast at endpt
    exact endpt

theorem width_envelopes (d : BandData) (j : Fin 9) {w : ℝ}
    (α0 : 0 ≤ d.α) (β0 : 0 ≤ d.β) (lo : (left j:ℝ) ≤ w) (hi : w ≤ (right j:ℝ)) :
    d.α*w ≤ (incidence d j:ℝ) ∧ 2*d.β*w ≤ (deficit d j:ℝ) ∧
      4*(d.β:ℝ)^2*w*(1-w) ≤ (kappa d j:ℝ)*(9/40) := by
  have ar : 0 ≤ (d.α:ℝ) := by exact_mod_cast α0
  have br : 0 ≤ (d.β:ℝ) := by exact_mod_cast β0
  have top : w*(1-w) ≤ (peak j:ℝ)*(1-(peak j:ℝ)) := by
    rcases peak_side j with ⟨eq,h⟩ | ⟨eq,h⟩
    · rw [eq]
      have above : (1/2:ℝ) ≤ (left j:ℝ) := by simpa using (Rat.cast_mono (K:=ℝ) h)
      linarith only [mul_nonneg (sub_nonneg.mpr lo)
        (by linarith only [lo,above] : 0 ≤ w+(left j:ℝ)-1)]
    · rw [eq]
      have below : (right j:ℝ) ≤ 1/2 := by simpa using (Rat.cast_mono (K:=ℝ) h)
      linarith only [mul_nonneg (sub_nonneg.mpr hi)
        (by linarith only [hi,below] : 0 ≤ 1-w-(right j:ℝ))]
  unfold incidence deficit kappa
  push_cast
  refine ⟨mul_le_mul_of_nonneg_left hi ar,mul_le_mul_of_nonneg_left hi (by positivity),?_⟩
  linarith only [mul_le_mul_of_nonneg_left top (show 0 ≤ 4*(d.β:ℝ)^2 by positivity)]

end
end Erdos617.CutoffCells
