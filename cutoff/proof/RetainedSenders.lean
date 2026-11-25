import ExteriorShortage
import SenderPopulation
import SenderRetry

/-! The heavy-sender trial on the same retained rows that witness the strict shortage. -/

namespace Erdos617.ColoredLists

open Finset PackingLists PruningOverlap SenderRetry
open scoped Classical
noncomputable section
variable {V : Type*} {r : ℕ} [Fintype V] (T : Trace V r)

/-- The width estimates supply the actual retry probability, its domain and
the row-deficit allowance in the local surplus calculation. -/
theorem retained_retry_surplus (hr : 2 ≤ r) (no : ¬Witness T.color)
    {E : Finset V} {e n : ℕ} {α β M Y b : ℝ}
    (lists : ListBounds (targetGraph T.color T.target) T.row univ (live T)
      (range r) (qualifying T) E r)
    (S : WidthIntegral.Selection (ordinaryLists T E) (rowDeficit T E) (rowIncidence T E) e n α β M)
    (band : RetainedWidth.Band Y b α β) {i : ℕ} (hi : i ∈ S.retained) (y : V)
    (heavy : (r:ℝ)/2 < (((rowList T E i).filter ((targetGraph T.color T.target).Adj y)).card:ℝ)) :
    let G := targetGraph T.color T.target
    let C := rowList T E i
    let ρ := (9/40:ℝ)/S.s
    let q := neighborFraction G C y
    let v := successIn G C y (100*ρ) (fun _ ↦ True)
    (r:ℝ)*(1-v+ρ*v)+2*((r:ℝ)-C.card)*(1-q)+37*ρ*r*(1-q) ≤
      ((C.filter (G.Adj y)).card:ℝ)+((r:ℝ)-C.card) := by
  let G := targetGraph T.color T.target
  let C := rowList T E i
  let ρ := (9/40:ℝ)/S.s
  have rp : (0:ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hs : (1120:ℝ) ≤ S.s := by exact_mod_cast S.scale_lo
  have sp : (0:ℝ) < S.s := by linarith only [hs]
  have ordinary : i ∈ ordinaryLists T E := by
    rw [S.retained_eq] at hi
    exact (mem_sdiff.mp (mem_filter.mp hi).1).1
  have unused := (mem_sdiff.mp (mem_sdiff.mp (mem_inter.mp ordinary).1).1).2
  have fits : C.card ≤ r := (caps_of_no_witness T.color T.target hr no).2 _ (lists.clique i unused)
  have deg : (r:ℝ)/2 < ((C.filter (G.Adj y)).card:ℝ) := heavy
  have degCap : ((C.filter (G.Adj y)).card:ℝ) ≤ C.card := by exact_mod_cast card_le_card (filter_subset ..)
  have cp : (0:ℝ) < C.card := by linarith only [deg,degCap,rp]
  have cb : (C.card:ℝ) ≤ r := by exact_mod_cast fits
  have qhalf : 1/2 ≤ neighborFraction G C y := (le_div_iff₀ cp).2 (by linarith only [deg,cb])
  have frac : ρ ≤ 1/1000 := (div_le_iff₀ sp).2 (by linarith only [hs])
  have hβ : 0 ≤ β := by cases band <;> norm_num
  have βcap : β ≤ 924/4000 := by cases band <;> norm_num
  have bound := S.deficit i hi
  change (S.s:ℝ)*(1-(C.card:ℝ)/r) ≤ 2*β*S.w at bound
  have num : (1-(C.card:ℝ)/r)*(S.s:ℝ) ≤ 3*(9/40:ℝ) := by
    nlinarith only [bound,mul_le_mul_of_nonneg_left S.width_lt.le hβ,βcap]
  have src : 1-(C.card:ℝ)/r ≤ 3*ρ := by
    dsimp only [ρ]; rw [← mul_div_assoc]; exact (le_div_iff₀ sp).2 num
  have deficit := mul_le_mul_of_nonneg_right src rp.le
  rw [sub_mul,one_mul,div_mul_cancel₀ _ rp.ne'] at deficit
  exact source_surplus G C y r ρ 3 (card_pos.mp (by exact_mod_cast cp)) (by omega)
    (by dsimp only [ρ]; positivity) (by linarith only [frac]) qhalf deficit (by linarith only [frac])

/-- Counting every strong incidence before assigning it to a sender gives a
strict lower bound on the moderate population plus the original deficits. -/
theorem distinct_sender_shortfall (prep : Prepared T) (hr : 3 ≤ r) (no : ¬Witness T.color)
    (order : Fintype.card V = r^2+1) {E : Finset V} {e n : ℕ} {α β M Y b : ℝ}
    (lists : ListBounds (targetGraph T.color T.target) T.row univ (live T)
      (range r) (qualifying T) E r)
    (S : WidthIntegral.Selection (ordinaryLists T E) (rowDeficit T E) (rowIncidence T E) e n α β M)
    (band : RetainedWidth.Band Y b α β) (slots : e+(ordinaryLists T E).card = r)
    (shortage : (3/20:ℝ)*r < ((S.s-1:ℕ):ℝ)*r-((lowExterior T E S.retained S.s).card:ℝ)) :
    let H := senderSet T E S.retained S.s
    let N := strongRows T E S.retained
    1+(3/20:ℝ)*r+((H.filter fun v ↦ 2 ≤ (N v).card).card:ℝ) <
      ((H.filter fun v ↦ (N v).card = 0).card:ℝ) + ∑ i ∈ S.retained, ((r:ℝ)-(rowList T E i).card) := by
  exact (add_lt_add_left (add_lt_add_right shortage 1) _).trans_le
    (sender_population T prep hr no order lists S band slots)

end
end Erdos617.ColoredLists
