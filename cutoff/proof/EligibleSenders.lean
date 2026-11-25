import StrongAssignments
import RetainedSenders

/-! The mass of eligible senders on the particular rows supplying the strict shortage. -/

namespace Erdos617.ColoredLists

open Finset PackingLists PruningOverlap SenderRetry
open scoped Classical
noncomputable section
variable {V : Type*} {r : ℕ} [Fintype V] (T : Trace V r)

/-- Success at the retry stage of a sender's own retained row. -/
def rowSuccess (E : Finset V) (s : ℕ) (y : V) (i : ℕ) : ℝ :=
  successIn (targetGraph T.color T.target) (rowList T E i) y (100*((9/40:ℝ)/s)) (fun _ ↦ True)

def senderEligibility (E : Finset V) (parts : Finset ℕ) (s : ℕ) (y : V) : ℝ :=
  eligibleWeight (strongRows T E parts y) (rowSuccess T E s y)

/-- The extra two terms recovered from a successful attempt and from the
nonneighbor fraction of a sender with one strong row. -/
def senderRetryCharge (E : Finset V) (parts : Finset ℕ) (s : ℕ) (y : V) : ℝ :=
  let ρ := (9/40:ℝ)/s
  uniqueCharge (strongRows T E parts y) fun i ↦
    ρ*r*rowSuccess T E s y i+37*ρ*r*(1-neighborFraction (targetGraph T.color T.target) (rowList T E i) y)

private theorem retained_charge_capacity (prep : Prepared T) (hr : 3 ≤ r) (no : ¬Witness T.color)
    {E : Finset V} {e n : ℕ} {α β M Y b : ℝ}
    (lists : ListBounds (targetGraph T.color T.target) T.row univ (live T)
      (range r) (qualifying T) E r)
    (S : WidthIntegral.Selection (ordinaryLists T E) (rowDeficit T E) (rowIncidence T E) e n α β M)
    (band : RetainedWidth.Band Y b α β) {i : ℕ} (hi : i ∈ S.retained)
    (Z : Finset V) (dis : Disjoint (rowList T E i) Z)
    (heavy : ∀ y ∈ Z, (r:ℝ)/2 < (((rowList T E i).filter ((targetGraph T.color T.target).Adj y)).card:ℝ)) :
    let C := rowList T E i
    let G := targetGraph T.color T.target
    let d := (r:ℝ)-C.card
    (∑ y ∈ Z, (((C.filter (G.Adj y)).card:ℝ)+d-2*d*(1-neighborFraction G C y))) ≤
      (r:ℝ)*d+(501/1000:ℝ)*d^2 := by
  let C := rowList T E i
  let G := targetGraph T.color T.target
  let d := (r:ℝ)-C.card
  let deg := fun y ↦ ((C.filter (G.Adj y)).card:ℝ)
  let J := ∑ y ∈ Z, 2*d*(1-neighborFraction G C y)
  have ordinary : i ∈ ordinaryLists T E := by
    rw [S.retained_eq] at hi
    exact (mem_sdiff.mp (mem_filter.mp hi).1).1
  have unused := (mem_sdiff.mp (mem_sdiff.mp (mem_inter.mp ordinary).1).1).2
  have cl : G.IsClique (C:Set V) := lists.clique i unused
  have fits : C.card ≤ r := (caps_of_no_witness T.color T.target (by omega) no).2 _ cl
  have capacity := clique_arrival_capacity T.color T.target C Z (by omega) no dis cl
  change (∑ y ∈ Z, deg y)+(Z.card:ℝ)*d ≤ ((r:ℝ)-1)*d+(Z.card:ℝ)*((Z.card:ℝ)+1)/2 at capacity
  have variance := retained_row_charge T prep hr no lists S band hi Z dis heavy 0 le_rfl
  change (Z.card:ℝ)^2/2 + ((Z.card:ℝ)-d)*0 - J ≤ (501/1000:ℝ)*d^2+0^2/2 at variance
  have maxCount := (retained_heavy_senders T prep hr no lists S band hi Z dis heavy).1
  have count : (Z.card:ℝ) ≤ 2*d := by
    dsimp only [d]; rw [← Nat.cast_sub (R := ℝ) fits]; exact_mod_cast maxCount
  change (∑ y ∈ Z, (deg y+d-2*d*(1-neighborFraction G C y))) ≤ _
  rw [sum_sub_distrib,sum_add_distrib,sum_const,nsmul_eq_mul]
  change (∑ y ∈ Z, deg y)+(Z.card:ℝ)*d-J ≤ (r:ℝ)*d+501/1000*d^2
  nlinarith only [capacity,variance,count]

/-- Each strong sender chooses at most two of its original rows. Summing their
actual payments in row order proves the eligibility estimate and keeps the
additional 37ρr(1−q) and ρrv from every unique strong sender. -/
theorem eligible_mass_with_surplus (prep : Prepared T) (hr : 3 ≤ r) (no : ¬Witness T.color)
    (order : Fintype.card V = r^2+1) {E : Finset V} {e n : ℕ} {α β M Y b : ℝ}
    (lists : ListBounds (targetGraph T.color T.target) T.row univ (live T)
      (range r) (qualifying T) E r)
    (S : WidthIntegral.Selection (ordinaryLists T E) (rowDeficit T E) (rowIncidence T E) e n α β M)
    (band : RetainedWidth.Band Y b α β) (slots : e+(ordinaryLists T E).card = r) :
    let H := senderSet T E S.retained S.s
    let Δ := ((S.s-1:ℕ):ℝ)*r-((lowExterior T E S.retained S.s).card:ℝ)
    (r:ℝ)*(1+Δ-∑ y ∈ H, senderEligibility T E S.retained S.s y)+
      (∑ y ∈ H, senderRetryCharge T E S.retained S.s y) ≤
      (501/1000:ℝ)*∑ i ∈ S.retained, ((r:ℝ)-(rowList T E i).card)^2 := by
  let H := senderSet T E S.retained S.s
  let G := targetGraph T.color T.target
  let C := rowList T E
  let d := fun i ↦ (r:ℝ)-(C i).card
  let ρ := (9/40:ℝ)/S.s
  let deg := fun y i ↦ (((C i).filter (G.Adj y)).card:ℝ)
  let q := fun y i ↦ neighborFraction G (C i) y
  let N := strongRows T E S.retained
  let assignments := fun y ↦ assignedStrong (N y)
  let Z := fun i ↦ H.filter fun y ↦ i ∈ assignments y
  let pay := fun y i ↦ deg y i+d i-2*d i*(1-q y i)
  have rows (y i) (h : i ∈ N y) : i ∈ S.retained ∧ (r:ℝ)/2 < deg y i := mem_filter.mp h
  have cost (i) (hi : i ∈ S.retained) :
      (∑ y ∈ Z i, pay y i) ≤ (r:ℝ)*d i+(501/1000:ℝ)*(d i)^2 := by
    have dis : Disjoint (C i) (Z i) := disjoint_left.mpr fun y inC inZ ↦
      ((mem_senderSet T).mp (mem_filter.mp inZ).1).1 (mem_biUnion.mpr ⟨i,hi,inC⟩)
    apply retained_charge_capacity T prep hr no lists S band hi _ dis
    exact fun y hy ↦ (rows y i (assignedStrong_subset _ (mem_filter.mp hy).2)).2
  have sender (y : V) (_ : y ∈ H) :
      (r:ℝ)*(1-senderEligibility T E S.retained S.s y)+senderRetryCharge T E S.retained S.s y ≤
        ∑ i ∈ assignments y, pay y i := by
    apply assignment_payment
    · intro i h
      obtain ⟨hi,heavy⟩ := rows y i h
      have v := retained_retry_surplus T (by omega) no lists S band hi y heavy
      change (r:ℝ)*(1-rowSuccess T E S.s y i+ρ*rowSuccess T E S.s y i)+
          2*d i*(1-q y i)+37*ρ*r*(1-q y i) ≤ deg y i+d i at v
      change (r:ℝ)*(1-rowSuccess T E S.s y i)+
        (ρ*r*rowSuccess T E S.s y i+37*ρ*r*(1-q y i)) ≤ deg y i+d i-2*d i*(1-q y i)
      linarith only [v]
    · intro i h
      obtain ⟨hi,heavy⟩ := rows y i h
      have ordinary : i ∈ ordinaryLists T E := by
        rw [S.retained_eq] at hi
        exact (mem_sdiff.mp (mem_filter.mp hi).1).1
      have unused := (mem_sdiff.mp (mem_sdiff.mp (mem_inter.mp ordinary).1).1).2
      have fit : (C i).card ≤ r := (caps_of_no_witness T.color T.target (by omega) no).2 _
        (lists.clique i unused)
      have dc : 0 ≤ d i := sub_nonneg.mpr (by exact_mod_cast fit)
      have degCap : deg y i ≤ (C i).card := by
        dsimp only [deg]; exact_mod_cast card_le_card (filter_subset (G.Adj y) (C i))
      have rp : (0:ℝ) < r := by exact_mod_cast (show 0 < r by omega)
      have cp : (0:ℝ) < (C i).card := by linarith only [heavy,degCap,rp]
      have qhalf : 1/2 ≤ q y i := (le_div_iff₀ cp).mpr
        (by linarith only [heavy,(show ((C i).card:ℝ) ≤ r by exact_mod_cast fit)])
      dsimp only [pay]
      nlinarith only [heavy,mul_nonneg dc (sub_nonneg.mpr qhalf)]
  have transpose (y) : (∑ i ∈ assignments y, pay y i) =
      ∑ i ∈ S.retained, if i ∈ assignments y then pay y i else 0 := by
    rw [← sum_filter]
    congr 1
    ext i
    simp only [mem_filter]
    exact ⟨fun hi ↦ ⟨(rows y i (assignedStrong_subset _ hi)).1,hi⟩,And.right⟩
  have upper := sum_le_sum cost
  have lower := sum_le_sum sender
  simp_rw [transpose] at lower
  rw [sum_comm] at lower
  have row_eq (i) : (∑ y ∈ H, if i ∈ assignments y then pay y i else 0) =
      ∑ y ∈ Z i, pay y i := (sum_filter ..).symm
  simp_rw [row_eq] at lower
  have paid := lower.trans upper
  simp only [sum_add_distrib,← mul_sum,sum_sub_distrib,sum_const,nsmul_eq_mul,mul_one] at paid
  have ledger := sender_ledger T S order slots
  change (H.card:ℝ) = _ + ∑ i ∈ S.retained, d i at ledger
  dsimp only
  change (r:ℝ)*(1+_ - ∑ y ∈ H, senderEligibility T E S.retained S.s y)+
    (∑ y ∈ H, senderRetryCharge T E S.retained S.s y) ≤ (501/1000:ℝ)*∑ i ∈ S.retained, (d i)^2
  nlinarith only [paid,congrArg (fun z : ℝ ↦ (r:ℝ)*z) ledger]

/-- The extra charge in the eligibility bound is nonnegative on every sender,
including vertices with no assigned retry. -/
theorem senderRetryCharge_nonneg (E : Finset V) (parts : Finset ℕ) {s : ℕ} (hs : 1120 ≤ s) (y : V) :
    0 ≤ senderRetryCharge T E parts s y := by
  let ρ := (9/40:ℝ)/s
  have sp : (1120:ℝ) ≤ s := by exact_mod_cast hs
  have pos : (0:ℝ) < s := by linarith
  have low : 0 ≤ ρ := by dsimp [ρ]; positivity
  have high : ρ ≤ 1/100 := (div_le_iff₀ pos).2 (by linarith)
  unfold senderRetryCharge uniqueCharge
  split
  · apply sum_nonneg
    intro i hi
    let C := rowList T E i
    let G := targetGraph T.color T.target
    have ok : 0 ≤ rowSuccess T E s y i := by
      change 0 ≤ successIn G C y (100*ρ) _
      unfold successIn
      apply mass_nonnegative G C y (100*ρ) (by linarith only [low]) (by linarith only [high])
      intro a
      cases a <;> simp
    have qmax : neighborFraction G C y ≤ 1 := by
      by_cases empty : C = ∅
      · simp [neighborFraction,empty]
      · have cp : (0:ℝ)<C.card := by exact_mod_cast card_pos.mpr (nonempty_iff_ne_empty.mpr empty)
        exact (div_le_one cp).2 (by exact_mod_cast card_le_card (filter_subset (G.Adj y) C))
    change 0 ≤ ρ*r*rowSuccess T E s y i+37*ρ*r*(1-neighborFraction G C y)
    exact add_nonneg (mul_nonneg (mul_nonneg low (Nat.cast_nonneg _)) ok)
      (mul_nonneg (by positivity) (sub_nonneg.mpr qmax))
  · exact le_rfl

/-- Before thinning, only the row-variance allowance can pay for the shortage
of eligible destinations. The sender set and the exterior shortage use the
same choice of ordinary cliques. -/
theorem eligible_mass_budget (prep : Prepared T) (hr : 3 ≤ r) (no : ¬Witness T.color)
    (order : Fintype.card V = r^2+1) {E : Finset V} {e n : ℕ} {α β M Y b : ℝ}
    (lists : ListBounds (targetGraph T.color T.target) T.row univ (live T)
      (range r) (qualifying T) E r)
    (S : WidthIntegral.Selection (ordinaryLists T E) (rowDeficit T E) (rowIncidence T E) e n α β M)
    (band : RetainedWidth.Band Y b α β) (slots : e+(ordinaryLists T E).card = r) :
    let H := senderSet T E S.retained S.s
    let Δ := ((S.s-1:ℕ):ℝ)*r-((lowExterior T E S.retained S.s).card:ℝ)
    (r:ℝ)*(1+Δ-∑ y ∈ H, senderEligibility T E S.retained S.s y) ≤
      (501/1000:ℝ)*∑ i ∈ S.retained, ((r:ℝ)-(rowList T E i).card)^2 := by
  apply le_trans _ (eligible_mass_with_surplus T prep hr no order lists S band slots)
  apply le_add_of_nonneg_right
  exact sum_nonneg fun y _ ↦ senderRetryCharge_nonneg T E S.retained S.scale_lo y

/-- Substitute the actual width square bound into the eligibility estimate.
This is the scale used for choosing the thinning probability. -/
theorem eligible_mass_width (prep : Prepared T) (hr : 3 ≤ r) (no : ¬Witness T.color)
    (order : Fintype.card V = r^2+1) {E : Finset V} {e n : ℕ} {α β M Y b : ℝ}
    (lists : ListBounds (targetGraph T.color T.target) T.row univ (live T)
      (range r) (qualifying T) E r)
    (S : WidthIntegral.Selection (ordinaryLists T E) (rowDeficit T E) (rowIncidence T E) e n α β M)
    (band : RetainedWidth.Band Y b α β) (slots : e+(ordinaryLists T E).card = r) :
    let H := senderSet T E S.retained S.s
    let Δ := ((S.s-1:ℕ):ℝ)*r-((lowExterior T E S.retained S.s).card:ℝ)
    1+Δ-∑ y ∈ H, senderEligibility T E S.retained S.s y ≤
      (501/1000:ℝ)*(4*β^2*S.w*(1-S.w)/S.s)*r := by
  have rp : (0:ℝ)<r := by exact_mod_cast (show 0<r by omega)
  have sp : (0:ℝ)<S.s := by exact_mod_cast (show 0<S.s by have := S.scale_lo; omega)
  have id (i : ℕ) : ((r:ℝ)-(rowList T E i).card)^2 = (rowDeficit T E i)^2*(r:ℝ)^2 := by
    have eq : (r:ℝ)-(rowList T E i).card = rowDeficit T E i*(r:ℝ) := by
      rw [rowDeficit,sub_mul,one_mul,div_mul_cancel₀ _ rp.ne']
    rw [eq,mul_pow]
  have paid := eligible_mass_budget T prep hr no order lists S band slots
  dsimp only at paid ⊢
  simp_rw [id,← sum_mul] at paid
  have normalized : (∑ i ∈ S.retained, (rowDeficit T E i)^2) ≤ 4*β^2*S.w*(1-S.w)/S.s :=
    (le_div_iff₀ sp).2 (by rw [mul_comm]; exact S.squares)
  have total := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right normalized (sq_nonneg (r:ℝ)))
    (by norm_num : (0:ℝ) ≤ 501/1000)
  apply le_of_mul_le_mul_right _ rp
  linarith only [paid,total]

/-- Thinning the eligible mass at min(1,Δ/A) is well defined at the
strict shortage. It loses at most the normalized variance allowance and
selects at most sr vertices in expectation. -/
theorem eligible_thinning (prep : Prepared T) (hr : 3 ≤ r) (no : ¬Witness T.color)
    (order : Fintype.card V = r^2+1) {E : Finset V} {e n : ℕ} {α β M Y b : ℝ}
    (lists : ListBounds (targetGraph T.color T.target) T.row univ (live T)
      (range r) (qualifying T) E r)
    (S : WidthIntegral.Selection (ordinaryLists T E) (rowDeficit T E) (rowIncidence T E) e n α β M)
    (band : RetainedWidth.Band Y b α β) (slots : e+(ordinaryLists T E).card = r)
    (shortage : (3/20:ℝ)*r < ((S.s-1:ℕ):ℝ)*r-((lowExterior T E S.retained S.s).card:ℝ)) :
    let H := senderSet T E S.retained S.s
    let Δ := ((S.s-1:ℕ):ℝ)*r-((lowExterior T E S.retained S.s).card:ℝ)
    let A := ∑ y ∈ H, senderEligibility T E S.retained S.s y
    let p := min 1 (Δ/A)
    let m := p*A
    let bound := (501/1000:ℝ)*(4*β^2*S.w*(1-S.w)/S.s)*r
    0 < A ∧ 0 < p ∧ p ≤ 1 ∧ m = min A Δ ∧
      0 ≤ Δ-m ∧ Δ-m ≤ bound ∧ (3/20:ℝ)*r-bound < m ∧ m ≤ (S.s:ℝ)*r := by
  let H := senderSet T E S.retained S.s
  let Δ := ((S.s-1:ℕ):ℝ)*r-((lowExterior T E S.retained S.s).card:ℝ)
  let A := ∑ y ∈ H, senderEligibility T E S.retained S.s y
  let p := min 1 (Δ/A)
  let m := p*A
  let B := 4*β^2*S.w*(1-S.w)
  let loss := (501/1000:ℝ)*(B/S.s)*r
  have rp : (0:ℝ)<r := by exact_mod_cast (show 0<r by omega)
  have hs : (1120:ℝ) ≤ S.s := by exact_mod_cast S.scale_lo
  have sp : (0:ℝ) < S.s := by linarith only [hs]
  have small : 0 ≤ β ∧ β ≤ 1 := by cases band <;> norm_num
  have square : β^2 ≤ 1 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr small.2) (show 0 ≤ 1+β by linarith only [small.1])]
  have peak : 4*S.w*(1-S.w) ≤ 1 := by nlinarith only [sq_nonneg (2*S.w-1)]
  have b0 : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg (mul_nonneg (by positivity) S.width_pos.le) (sub_nonneg.mpr S.width_lt.le)
  have b1 : B ≤ 1 := by
    dsimp only [B]
    nlinarith only [mul_le_mul_of_nonneg_left peak (sq_nonneg β),square]
  have tiny : B/(S.s:ℝ) ≤ 1/1120 := (div_le_iff₀ sp).mpr (by linarith only [b1,hs])
  have cap : 0 ≤ loss := mul_nonneg (mul_nonneg (by norm_num) (div_nonneg b0 sp.le)) rp.le
  have tinyLoss : loss ≤ (501/1000:ℝ)*(1/1120)*r :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left tiny (by norm_num)) rp.le
  have paid : 1+Δ-A ≤ loss := eligible_mass_width T prep hr no order lists S band slots
  have large : (3/20:ℝ)*r < Δ := shortage
  have apos : 0 < A := by linarith only [tinyLoss,paid,large,rp]
  have dpos : 0 < Δ := by linarith only [large,rp]
  have ppos : 0 < p := lt_min (by norm_num) (div_pos dpos apos)
  have expected : m = min A Δ := by
    dsimp only [m,p]
    rw [min_mul_of_nonneg _ _ apos.le,one_mul,div_mul_cancel₀ _ apos.ne']
  have under : 0 ≤ Δ-m := by rw [expected]; exact sub_nonneg.mpr (min_le_right ..)
  have near : Δ-m ≤ loss := by
    rw [expected]
    rcases le_total A Δ with h | h
    · rw [min_eq_left h]; linarith only [paid]
    · rw [min_eq_right h,sub_self]; exact cap
  have scale : (Δ:ℝ) ≤ (S.s:ℝ)*r := by
    have prev : ((S.s-1:ℕ):ℝ) ≤ S.s := by exact_mod_cast Nat.sub_le S.s 1
    exact (sub_le_self _ (Nat.cast_nonneg _)).trans (mul_le_mul_of_nonneg_right prev rp.le)
  have low : (3/20:ℝ)*r-loss < m := by linarith only [large,near]
  have high : m ≤ (S.s:ℝ)*r := by linarith only [under,scale]
  exact ⟨apos,ppos,min_le_left ..,expected,under,near,low,high⟩

end
end Erdos617.ColoredLists
