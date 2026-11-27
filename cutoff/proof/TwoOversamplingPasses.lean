import RetryDeficit

/-! Both oversampling estimates of Appendix A, §5 on one coloring and one
width selection. The second pass retains the first pass's retry credit. -/

namespace Erdos617.ColoredLists

open Finset PruningOverlap PackingLists FiniteLaw MarkedSender
open scoped Classical
noncomputable section
variable {V : Type*} {r : ℕ} [Fintype V] (T : Trace V r)

/-- The manuscript bounds in one common notation. -/
def TwoPassBounds (E : Finset V) (I : Finset ℕ) (s : ℕ) (A X Yhi κ ex : ℝ) : Prop :=
  let ρ := (9/40:ℝ)/s
  let H := senderSet T E I s
  let Δ := ((s-1:ℕ):ℝ)*r-(lowExterior T E I s).card
  let total := ∑ y ∈ H, senderEligibility T E I s y
  let Z₁ := oversampleFactor A X Yhi κ (2*κ) ex
  let g := X/(9/40)
  let W₁ := (1/(1-X/1120)+(501/1000)*g/37)*κ + g*Z₁*((9/40)/1120)/37
  let Z₂ := oversampleFactor A X Yhi κ W₁ ex
  max (total-Δ) 0 ≤ Z₁*ρ^2*r ∧
    (∑ i ∈ I, ((uniqueGroup T E I s i).card:ℝ)*rowDeficit T E i) ≤ W₁*(ρ*r) ∧
    max (total-Δ) 0 ≤ Z₂*ρ^2*r

/-- The certificate bins supply only upper envelopes on the width. The bounds
on individual senders and the larger thinning probabilities are derived here. -/
theorem two_oversampling_passes (prep : Prepared T) (hr : 3 ≤ r) (no : ¬Witness T.color)
    (order : Fintype.card V = r^2+1) {E : Finset V} {e t : ℕ} {α β M Y ex : ℝ}
    (lists : ListBounds (targetGraph T.color T.target) T.row univ (live T) (range r) (qualifying T) E r)
    (S : WidthIntegral.Selection (ordinaryLists T E) (rowDeficit T E) (rowIncidence T E) e t α β M)
    (band : RetainedWidth.Band Y ex α β) (slots : e+(ordinaryLists T E).card=r)
    (scale : (2:ℝ)^ex*(S.s:ℝ)^4 < r)
    (A X : ℝ) (a0 : 0 ≤ A) (a1 : A ≤ 656/4000) (x0 : 0 ≤ X) (x1 : X ≤ 1/2)
    (inc : α*S.w ≤ A) (defi : 2*β*S.w ≤ X)
    (κ Yhi : ℝ) (k0 : 0 ≤ κ) (k1 : κ ≤ 1/4) (y0 : 0 ≤ Yhi) (y1 : Yhi ≤ 2)
    (squares : 4*β^2*S.w*(1-S.w) ≤ κ*(9/40))
    (ymax : 2-firstRate T/2-(199/400:ℝ)*secondRate T ≤ Yhi)
    (shortage : (3/20:ℝ)*r < ((S.s-1:ℕ):ℝ)*r-(lowExterior T E S.retained S.s).card) :
    TwoPassBounds T E S.retained S.s A X Yhi κ ex := by
  let Z₁ := oversampleFactor A X Yhi κ (2*κ) ex
  let g := X/(9/40)
  let W₁ := (1/(1-X/1120)+(501/1000)*g/37)*κ + g*Z₁*((9/40)/1120)/37
  have w0 : 0 ≤ 2*κ := by positivity
  have w1 : 2*κ ≤ 1 := by linarith only [k1]
  have first := eligibility_surplus T S prep hr no order lists band slots scale
    A X a0 a1 x0 x1 inc defi κ Yhi (2*κ) k0 k1 y0 y1 w0 w1 squares ymax
    (first_pass_unique_weight T S prep hr no lists band κ squares) shortage
  obtain ⟨_,Z0,guard⟩ := oversample_guards band a0 a1 x0 x1 y0 y1 k0 k1 w0 w1
  change 0 ≤ Z₁ at Z0
  have secondWeight := retry_deficit_weight T S prep hr no order lists band slots
    X κ Z₁ x0 x1 Z0 defi squares ((le_max_left _ _).trans first)
  have gp : 0 ≤ g := by dsimp [g]; positivity
  have gcap : g ≤ 5/2 := by dsimp [g]; linarith only [x1]
  have denom : 0 < 1-X/1120 := by linarith only [x1]
  have inv : 1/(1-X/1120) ≤ 2 := (div_le_iff₀ denom).mpr (by linarith only [x1])
  have good : Z₁*((9/40:ℝ)/1120) ≤ 6 := by
    have cap := lt_of_lt_of_le guard (min_le_left ..)
    change Z₁*_ < (3/20:ℝ)/128 at cap
    linarith only [cap]
  have left0 : 0 ≤ 1/(1-X/1120)+(501/1000)*g/37 := by positivity
  have left1 : 1/(1-X/1120)+(501/1000)*g/37 ≤ 21/10 := by linarith only [inv,gcap]
  have new0 : 0 ≤ W₁ := add_nonneg (mul_nonneg left0 k0) (by positivity)
  have new1 : W₁ ≤ 1 := by
    dsimp only [W₁]
    linarith only [mul_le_mul left1 k1 k0 (by norm_num : (0:ℝ) ≤ 21/10),
      mul_le_mul gcap good (show 0 ≤ Z₁*((9/40:ℝ)/1120) by positivity) (by norm_num : (0:ℝ) ≤ 5/2)]
  exact ⟨first,secondWeight,eligibility_surplus T S prep hr no order lists band slots scale
    A X a0 a1 x0 x1 inc defi κ Yhi W₁ k0 k1 y0 y1 new0 new1 squares ymax secondWeight shortage⟩

/-- From the original coloring alone, either a color is already missing or
the retained rows satisfy both oversampling bounds at their selected width. -/
theorem witness_or_two_passes (color : {e : Sym2 V // ¬e.IsDiag} → Fin r)
    (hr : 15*2^140 ≤ r) (order : Fintype.card V = r^2+1) :
    Witness color ∨ ∃ T : Trace V r, T.color=color ∧ Prepared T ∧
      ∃ E : Finset V, ListBounds (targetGraph T.color T.target) T.row univ (live T)
        (range r) (qualifying T) E r ∧
      ∃ ex α β, RetainedWidth.Band (2-firstRate T/2-(199/400)*secondRate T) ex α β ∧
      ∃ S : WidthIntegral.Selection (ordinaryLists T E) (rowDeficit T E) (rowIncidence T E)
          (range r \ ordinaryLists T E).card (omittedCount T E) α β
          ((2:ℝ)^((144-ex)/4) / ((16:ℝ)/15)^(1/4:ℝ)),
        (2:ℝ)^ex*(S.s:ℝ)^4 < r ∧
        (3/20:ℝ)*r < ((S.s-1:ℕ):ℝ)*r-((lowExterior T E S.retained S.s).card:ℝ) ∧
        TwoPassBounds T E S.retained S.s (α*S.w) (2*β*S.w) (2-firstRate T/2-(199/400)*secondRate T)
          (4*β^2*S.w*(1-S.w)/(9/40)) ex := by
  by_cases yes : Witness color
  · exact Or.inl yes
  obtain ⟨T,eq,prep,E,lists,ex,α,β,band,S,_,scale,short⟩ :=
    (witness_or_exterior_shortage color hr order).resolve_left yes
  have sub : ordinaryLists T E ⊆ range r := fun _ hi ↦
    (mem_sdiff.mp (mem_sdiff.mp (mem_inter.mp hi).1).1).1
  have slots := card_sdiff_add_card_eq_card sub
  rw [card_range] at slots
  have co : 0 ≤ α ∧ α ≤ 656/4000 ∧ 0 ≤ β ∧ β ≤ 925/4000 := by cases band <;> norm_num
  have y : 0 ≤ 2-firstRate T/2-(199/400)*secondRate T ∧
      2-firstRate T/2-(199/400)*secondRate T ≤ 2 := by cases band <;> constructor <;> linarith
  have a1 := (mul_le_of_le_one_right co.1 S.width_lt.le).trans co.2.1
  have x1 : 2*β*S.w ≤ 1/2 := by
    linarith only [mul_le_of_le_one_right (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) co.2.2.1) S.width_lt.le,co.2.2.2]
  let B := 4*β^2*S.w*(1-S.w)
  have B0 : 0 ≤ B := mul_nonneg (mul_nonneg (by positivity) S.width_pos.le) (sub_nonneg.mpr S.width_lt.le)
  have k1 : B/(9/40) ≤ 1/4 := by
    dsimp only [B]
    nlinarith only [mul_nonneg (sq_nonneg β) (sq_nonneg (2*S.w-1)),
      pow_le_pow_left₀ co.2.2.1 co.2.2.2 2]
  refine Or.inr ⟨T,eq,prep,E,lists,ex,α,β,band,S,scale,short,?_⟩
  exact two_oversampling_passes T prep (by omega) (eq ▸ yes) order lists S band slots scale
    _ _ (mul_nonneg co.1 S.width_pos.le) a1 (by have := co.2.2.1; have := S.width_pos; positivity)
    x1 le_rfl le_rfl _ _ (div_nonneg B0 (by norm_num)) k1 y.1 y.2 (by linarith) le_rfl short

end
end Erdos617.ColoredLists
