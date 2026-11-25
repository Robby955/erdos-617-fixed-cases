import EligibilitySurplus

/-! The first pass bounds the missing-neighbor mass of the unique senders.
This gives the improved input W₁ for a second application on the same rows. -/

namespace Erdos617.ColoredLists

open Finset PruningOverlap PackingLists FiniteLaw MarkedSender RepresentativeRepairs SenderRetry
open scoped Classical
noncomputable section
variable {V : Type*} {r : ℕ} [Fintype V] (T : Trace V r)

/-- Sum of the original missing-neighbor fractions over unique senders in row i. -/
def uniqueMiss (E : Finset V) (I : Finset ℕ) (s i : ℕ) : ℝ :=
  ∑ y ∈ uniqueGroup T E I s i, (1-neighborFraction (targetGraph T.color T.target) (rowList T E i) y)

omit [Fintype V] in
theorem one_sub_neighborFraction_nonneg (G : SimpleGraph V) (C : Finset V) (y : V) :
    0 ≤ 1-neighborFraction G C y := by
  by_cases empty : C = ∅
  · simp [neighborFraction,empty]
  · apply sub_nonneg.mpr
    exact (div_le_one (by exact_mod_cast card_pos.mpr (nonempty_iff_ne_empty.mpr empty))).mpr
      (by exact_mod_cast card_le_card (filter_subset (G.Adj y) C))

/-- Distinct unique destinations give disjoint groups. Their retry charges
can therefore be summed against the single charge ledger on all senders. -/
theorem unique_miss_charge (E : Finset V) (I : Finset ℕ) (s : ℕ) (slo : 1120 ≤ s) :
    let ρ := (9/40:ℝ)/s
    37*ρ*r*(∑ i ∈ I, uniqueMiss T E I s i) ≤
      ∑ y ∈ senderSet T E I s, senderRetryCharge T E I s y := by
  intro ρ
  let U := uniqueGroup T E I s
  let G := targetGraph T.color T.target
  let C := rowList T E
  let charge := senderRetryCharge T E I s
  have point (i y) (hy : y ∈ U i) :
      37*ρ*r*(1-neighborFraction G (C i) y) ≤ charge y := by
    have one := (mem_filter.mp hy).2
    have mass : 0 ≤ rowSuccess T E s y i := by
      unfold rowSuccess successIn
      apply mass_nonnegative
      · positivity
      · exact retry_rate_of_scale slo
      · intro a
        cases a <;> simp
    have spare : 0 ≤ ρ*r*rowSuccess T E s y i := by dsimp [ρ]; positivity
    dsimp only [charge,senderRetryCharge,uniqueCharge]
    rw [one]
    simp only [card_singleton,ite_true,sum_singleton]
    dsimp only [G,C,ρ] at *
    linarith only [spare]
  have dis : (I:Set ℕ).PairwiseDisjoint U :=
    fun _ _ _ _ ne ↦ disjoint_unique_groups T E I (s:=s) ne
  have inside : I.biUnion U ⊆ senderSet T E I s := by
    intro y hy
    obtain ⟨i,_,member⟩ := mem_biUnion.mp hy
    exact (mem_filter.mp member).1
  calc
    _ ≤ ∑ i ∈ I, ∑ y ∈ U i, charge y := by
      rw [mul_sum]
      apply sum_le_sum
      intro i _
      dsimp only [uniqueMiss]
      rw [mul_sum]
      exact sum_le_sum fun y hy ↦ point i y hy
    _ = ∑ y ∈ I.biUnion U, charge y := (sum_biUnion dis).symm
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg inside (fun y _ _ ↦ senderRetryCharge_nonneg T E I slo y)

variable {E : Finset V} {e t : ℕ} {α β M Y ex : ℝ}
  (S : WidthIntegral.Selection (ordinaryLists T E) (rowDeficit T E) (rowIncidence T E) e t α β M)

/-- A unique sender contributes its neighbor fraction and its missing
fraction to its count. The edge budget bounds the former in each row. -/
private theorem unique_weight_row (prep : Prepared T) (hr : 3 ≤ r) (no : ¬Witness T.color)
    (lists : ListBounds (targetGraph T.color T.target) T.row univ (live T) (range r) (qualifying T) E r)
    (band : RetainedWidth.Band Y ex α β) (X : ℝ) (x1 : X ≤ 1/2) (width : 2*β*S.w ≤ X)
    {i : ℕ} (hi : i ∈ S.retained) :
    let x := rowDeficit T E i
    let U := uniqueGroup T E S.retained S.s i
    ((U.card:ℝ)*x) ≤ (r:ℝ)*x^2/(1-X/1120)+(X/S.s)*uniqueMiss T E S.retained S.s i := by
  intro x U
  let C := rowList T E i
  let G := targetGraph T.color T.target
  let d := (r:ℝ)-C.card
  let q := neighborFraction G C
  let miss := uniqueMiss T E S.retained S.s i
  have rp : (0:ℝ)<r := by exact_mod_cast (show 0<r by omega)
  have slo : (1120:ℝ) ≤ S.s := by exact_mod_cast S.scale_lo
  have sp : (0:ℝ)<S.s := by linarith only [slo]
  have d_id : (r:ℝ)*x = d := by dsimp [x,rowDeficit,d,C]; field_simp
  have d0 : 0 ≤ d := by
    have cnt := unique_count_le_deficit T S prep hr no lists band hi
    change (U.card:ℝ) ≤ 2*d at cnt
    linarith only [cnt,Nat.cast_nonneg (α:=ℝ) U.card]
  have x0 : 0 ≤ x := by
    by_contra! bad
    linarith only [d0,d_id,mul_neg_of_pos_of_neg rp bad]
  have dx := (S.deficit i hi).trans width
  have xSmall : x ≤ X/1120 := by linarith only [dx,mul_le_mul_of_nonneg_right slo x0]
  have lo : 0 < 1-X/1120 := by linarith only [x1]
  have floor : (1-X/1120)*(r:ℝ) ≤ C.card := by dsimp only [d] at d_id; linarith only [d_id,mul_le_mul_of_nonneg_right xSmall rp.le]
  have cp : (0:ℝ)<C.card := lt_of_lt_of_le (mul_pos lo rp) floor
  have fits : C.card ≤ r := by exact_mod_cast (show (C.card:ℝ) ≤ r by dsimp only [d] at d0; linarith only [d0])
  have dis : Disjoint C U := disjoint_left.mpr fun y hc mem ↦
    (mem_senderSet T).mp (mem_filter.mp mem).1 |>.1 <| mem_biUnion.mpr ⟨i,hi,hc⟩
  have edges := (retained_heavy_senders T prep hr no lists S band hi U dis
    (fun _ member ↦ (unique_destination T member).2)).2
  change _ ≤ (r:ℝ)*((r-C.card:ℕ):ℝ) at edges
  rw [Nat.cast_sub fits] at edges
  have q0 : 0 ≤ ∑ y ∈ U, q y := sum_nonneg fun _ _ ↦ div_nonneg (Nat.cast_nonneg _) cp.le
  have paid : (∑ y ∈ U, q y)*C.card ≤ (r:ℝ)*d := by
    dsimp only [q,neighborFraction]
    rw [← sum_div,div_mul_cancel₀ _ cp.ne']
    exact edges
  have spare := mul_le_mul_of_nonneg_left floor q0
  have weight : (∑ y ∈ U, q y) ≤ d/(1-X/1120) := by
    apply (le_div_iff₀ lo).mpr
    apply le_of_mul_le_mul_right (a:=(r:ℝ)) _ rp
    linarith only [paid,spare]
  have count : (U.card:ℝ) = (∑ y ∈ U, q y)+miss := by
    change _ = (∑ y ∈ U, q y)+∑ y ∈ U, (1-q y)
    rw [sum_sub_distrib]; simp
  have mpos : 0 ≤ miss := sum_nonneg fun y _ ↦ one_sub_neighborFraction_nonneg G C y
  have hsmall : x ≤ X/S.s := (le_div_iff₀ sp).mpr (by linarith only [dx])
  rw [count,add_mul]
  have win := add_le_add (mul_le_mul_of_nonneg_right weight x0) (mul_le_mul_of_nonneg_right hsmall mpos)
  rw [mul_comm miss x]
  refine win.trans_eq ?_
  rw [← d_id]; ring

/-- The improved W₁. Here Z bounds the first pass surplus in units of ρ²r. -/
theorem retry_deficit_weight (prep : Prepared T) (hr : 3 ≤ r) (no : ¬Witness T.color)
    (order : Fintype.card V = r^2+1)
    (lists : ListBounds (targetGraph T.color T.target) T.row univ (live T) (range r) (qualifying T) E r)
    (band : RetainedWidth.Band Y ex α β) (slots : e+(ordinaryLists T E).card=r)
    (X κ Z : ℝ) (x0 : 0 ≤ X) (x1 : X ≤ 1/2) (Z0 : 0 ≤ Z)
    (width : 2*β*S.w ≤ X) (squares : 4*β^2*S.w*(1-S.w) ≤ κ*(9/40)) :
    let I := S.retained
    let s := S.s
    let ρ := (9/40:ℝ)/s
    let unit := ρ*r
    let H := senderSet T E I s
    let Δ := ((s-1:ℕ):ℝ)*r-(lowExterior T E I s).card
    let total := ∑ y ∈ H, senderEligibility T E I s y
    let g := X/(9/40)
    let W₁ := (1/(1-X/1120)+(501/1000)*g/37)*κ + g*Z*((9/40)/1120)/37
    total-Δ ≤ Z*ρ^2*r →
      (∑ i ∈ I, ((uniqueGroup T E I s i).card:ℝ)*rowDeficit T E i) ≤ W₁*unit := by
  intro I s ρ unit H Δ total g W₁ first
  let x := rowDeficit T E
  let miss := ∑ i ∈ I, uniqueMiss T E I s i
  have rp : (0:ℝ)<r := by exact_mod_cast (show 0<r by omega)
  have slo : (1120:ℝ) ≤ s := by exact_mod_cast S.scale_lo
  have sp : (0:ℝ)<s := by linarith only [slo]
  have rhop : 0 < ρ := by dsimp [ρ]; positivity
  have ρcap : ρ ≤ (9/40:ℝ)/1120 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) slo
  have denom : 0 < 1-X/1120 := by linarith only [x1]
  have quad : (∑ i ∈ I, (x i)^2) ≤ κ*ρ := by
    dsimp only [ρ]
    rw [← mul_div_assoc,le_div_iff₀ sp,mul_comm _ (s:ℝ)]
    exact S.squares.trans squares
  have d_id (i) : (r:ℝ)-(rowList T E i).card = r*x i := by dsimp [x,rowDeficit]; field_simp
  have eq : (∑ i ∈ I, ((r:ℝ)-(rowList T E i).card)^2) = (r:ℝ)^2*(∑ i ∈ I, (x i)^2) := by
    simp_rw [d_id,mul_pow]; rw [mul_sum]
  have sum := eligible_mass_with_surplus T prep hr no order lists S band slots
  have charge := unique_miss_charge T E I s S.scale_lo
  change (r:ℝ)*(1+Δ-total)+(∑ y ∈ H, senderRetryCharge T E I s y) ≤ (501/1000)*_ at sum
  rw [eq] at sum
  change 37*ρ*r*miss ≤ _ at charge
  have missing : 37*miss ≤ (501/1000)*κ*r+Z*ρ*r := by
    apply le_of_mul_le_mul_left (a:=ρ*r) _ (mul_pos rhop rp)
    linarith only [charge,sum,mul_le_mul_of_nonneg_left first rp.le,
      mul_le_mul_of_nonneg_left quad (show 0 ≤ (501/1000:ℝ)*(r:ℝ)^2 by positivity),rp]
  have weights := sum_le_sum (s:=I) (fun i hi ↦ unique_weight_row T S prep hr no lists band X x1 width hi)
  change _ ≤ ∑ i ∈ I, ((r:ℝ)*(x i)^2/(1-X/1120)+(X/s)*uniqueMiss T E I s i) at weights
  simp only [sum_add_distrib,← sum_div,← mul_sum] at weights
  apply weights.trans
  change (r:ℝ)*(∑ i ∈ I, (x i)^2)/(1-X/1120)+(X/s)*miss ≤ _
  have relation : X/(s:ℝ) = g*ρ := by dsimp [g,ρ]; ring
  rw [relation]
  have parts := add_le_add (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left quad rp.le) denom.le)
    (mul_le_mul_of_nonneg_left missing (show 0 ≤ g*ρ/37 by dsimp [g]; positivity))
  have remain := mul_le_mul_of_nonneg_right ρcap (show 0 ≤ g*Z*ρ*r/37 by dsimp [g]; positivity)
  dsimp only [W₁,unit]
  simp only [div_eq_mul_inv] at parts remain ⊢
  linarith only [parts,remain]

end
end Erdos617.ColoredLists
