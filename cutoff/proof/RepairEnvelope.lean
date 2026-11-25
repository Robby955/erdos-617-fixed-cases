import ManuscriptRowTest

/-! Turning the coloring's signed cut into an upper bound on the base repair
budget. The squared deficits are used on precisely the rows in that cut. -/

namespace Erdos617.ColoredLists

open Finset PruningOverlap PackingLists FiniteLaw MarkedSender RepresentativeRepairs
open scoped Classical
noncomputable section

/-- Absorb the heavy-load square for a signed remainder z, including κ=0. -/
private theorem absorb_square {a κ t H z : ℝ} (ha : 0 ≤ a) (hk : 0 ≤ κ)
    (hH : 0 ≤ H) (cs : t^2 ≤ κ*H) (den : 0 < 2-a*κ) :
    (a*t+z)^2/2-a*H ≤ z^2/(2-a*κ) := by
  apply (le_div_iff₀ den).mpr
  rcases hk.eq_or_lt with k0|kp
  · rw [← k0,zero_mul] at cs
    have t0 : t=0 := by nlinarith only [cs,sq_nonneg t]
    rw [← k0,t0]
    nlinarith only [mul_nonneg ha hH]
  · have credit := mul_nonneg ha (add_nonneg (sq_nonneg ((2-a*κ)*t-κ*z))
      (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) den.le) (sub_nonneg.mpr cs)))
    apply le_of_mul_le_mul_left (a:=κ) _ kp
    linarith only [credit]

private theorem pay_repairs {a b j r Q H T K t z D κ : ℝ}
    (ha : 4/3 < a) (bdef : b=3/4*a*j) (hj : 0 ≤ j)
    (hK : 0 ≤ K) (hH : 0 ≤ H) (hk : 0 ≤ κ) (cs : t^2 ≤ κ*H) (den : 0 < 2-a*κ)
    (cut : 2*((a-4/3)*Q+(b-j)*T+((b/r)^2-(j/r)^2)*K+(4/3)*H) ≤ D+(a*t+z)^2) :
    let k := (4/3)/(a-4/3)
    (4/3)*(Q-H)+j*T+(j/r)^2*K ≤ k*(z^2/(2-a*κ)+D/2) := by
  intro k
  have ap : 0 ≤ a := by linarith only [ha]
  have kp : 0 ≤ k := div_nonneg (by norm_num) (sub_nonneg.mpr ha.le)
  have id1 : k*(a-4/3) = 4/3 := div_mul_cancel₀ _ (sub_ne_zero.mpr ha.ne')
  have id2 : k*(b-j) = j := by rw [bdef]; linear_combination (3/4*j)*id1
  have paid : (j/r)^2 ≤ k*((b/r)^2-(j/r)^2) := by
    rw [div_pow,div_pow,← sub_div,← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ (sq_nonneg r)
    have bj : 0 ≤ b*j := by rw [bdef]; positivity
    nlinarith only [bj,congrArg (fun x : ℝ ↦ x*(b+j)) id2]
  have all := mul_le_mul_of_nonneg_right paid hK
  have square := absorb_square (z:=z) ap hk hH cs den
  have cut' : (a-4/3)*(Q-H)+(b-j)*T+((b/r)^2-(j/r)^2)*K ≤ z^2/(2-a*κ)+D/2 := by
    linarith only [cut,square]
  have transfer := mul_le_mul_of_nonneg_left cut' kp
  simp only [mul_add,← mul_assoc,id1,id2] at transfer
  linarith only [transfer,all]

variable {V : Type*} {r : ℕ} [Fintype V] (T : Trace V r)

/-- In edge units the base cost is controlled by the tested-row mass, the
mark count, and the weighted deficits of the unique senders. The width
selection itself supplies the squared-deficit estimate for Cauchy–Schwarz. -/
theorem coloring_repair_envelope (prep : Prepared T) (hr : 3 ≤ r) (no : ¬Witness T.color)
    {E : Finset V} {e t : ℕ} {α β M Y ex : ℝ}
    (lists : ListBounds (targetGraph T.color T.target) T.row univ (live T) (range r) (qualifying T) E r)
    (S : WidthIntegral.Selection (ordinaryLists T E) (rowDeficit T E) (rowIncidence T E) e t α β M)
    (band : RetainedWidth.Band Y ex α β) (slots : e+(ordinaryLists T E).card=r)
    (A X : ℝ) (a0 : 0 ≤ A) (a1 : A ≤ 656/4000) (x0 : 0 ≤ X) (x1 : X ≤ 1/2)
    (inc : α*S.w ≤ A) (defi : 2*β*S.w ≤ X) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (κ : ℝ) (k0 : 0 ≤ κ) (squares : 4*β^2*S.w*(1-S.w) ≤ κ*(9/40))
    (den : 0 < 2-heavyTestWeight A X*κ) :
    let I := S.retained
    let s := S.s
    let h := ((s-1:ℕ):ℝ)
    let C := rowList T E
    let G := targetGraph T.color T.target
    let H := senderSet T E I s
    let L := lowExterior T E I s
    let U := uniqueGroup T E I s
    let μ := senderLaw T E I s p (retry_rate_of_scale S.scale_lo) hp hp1
    let a := heavyTestWeight A X
    let b := uniqueTestWeight A X
    let k := (4/3)/(a-4/3)
    let m := (product μ).expect (markCount H)
    let u := h*r-L.card-m
    let W := ∑ i ∈ I, ((U i).card:ℝ)*rowDeficit T E i
    let q := ∑ i ∈ I, loadTest T E I s μ a b i
    0 ≤ u → sampleRepairBudget G I C H U L s r μ (representativeFactor X) ≤
      k*((b*W+u)^2/(2-a*κ)+(r*(h+q)^2+m)/2) := by
  intro I s h C G H L U μ a b k m u W q u0
  let j := representativeFactor X
  let n := heavyLoadMean G C L s r μ
  let ρ := (9/40:ℝ)/s
  let energy := ρ*(∑ i ∈ I, (n i)^2)
  let E' := fun i ↦ (product μ).expect fun w ↦ rowToExterior T E (exterior H L w) i
  let F := fun i ↦ ∑ y, (μ y).expect (foreignDegree G C i)
  let Q := ∑ i ∈ I, n i*(E' i+F i)/r
  let T₁ := ∑ i ∈ I, ((U i).card:ℝ)*E' i/r
  let K := ∑ t ∈ rowPairs I, ((U t.1).card:ℝ)*(U t.2).card*betweenRows T E t
  let π := loadTest T E I s μ a b
  let d := fun i ↦ (r:ℝ)-(C i).card
  let B := ∑ i ∈ I, π i*d i
  let x := rowDeficit T E
  let t' := ∑ i ∈ I, n i*x i
  have rp : (0:ℝ)<r := by exact_mod_cast (show 0<r by omega)
  have sp : (0:ℝ)<s := by have := S.scale_lo; exact_mod_cast (show 0<S.s by omega)
  have quad : (∑ i ∈ I, (x i)^2) ≤ κ*ρ := by
    dsimp only [ρ]
    rw [← mul_div_assoc,le_div_iff₀ sp,mul_comm _ (s:ℝ)]
    exact S.squares.trans squares
  have n2 := sum_nonneg (s:=I) fun i _ ↦ sq_nonneg (n i)
  have cs : t'^2 ≤ κ*energy := by
    have bound := (sum_mul_sq_le_sq_mul_sq I n x).trans (mul_le_mul_of_nonneg_left quad n2)
    dsimp only [energy]; linarith only [bound]
  have eq (i) : d i/(r:ℝ) = x i := by
    dsimp only [d,x,rowDeficit,C]
    rw [sub_div, div_self rp.ne']
  have split : B = a*t'+b*W := by
    dsimp only [B,t',W]
    rw [mul_sum,mul_sum,← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    change ((a*n i+b*((U i).card:ℝ))/r)*d i = a*(n i*x i)+b*(((U i).card:ℝ)*x i)
    rw [← eq]
    ring
  have main := manuscript_tested_cut T prep hr no lists S band slots A X a0 a1 x0 x1 inc defi p hp hp1
  change 2*((a-4/3)*Q+(b-j)*T₁+((b/r)^2-(j/r)^2)*K+(4/3)*ρ*(∑ i ∈ I,(n i)^2)) ≤
    r*(h*(h-1)+2*h*q+q^2-(∑ i ∈ I,(π i)^2))+(B+u)^2+m-u-(∑ i ∈ I,(π i*d i)^2) at main
  have slotcap : (r:ℝ)*(h*(h-1)+2*h*q+q^2-(∑ i ∈ I,(π i)^2)) ≤ r*(h+q)^2 := by
    apply mul_le_mul_of_nonneg_left _ rp.le
    have h0 : 0 ≤ h := Nat.cast_nonneg _
    linarith only [h0,sum_nonneg (s:=I) fun i _ ↦ sq_nonneg (π i)]
  have cut : 2*((a-4/3)*Q+(b-j)*T₁+((b/r)^2-(j/r)^2)*K+(4/3)*energy) ≤
      (r*(h+q)^2+m)+(a*t'+(b*W+u))^2 := by
    rw [split,mul_assoc (4/3:ℝ) ρ] at main
    change 2*(_+ (4/3)*energy) ≤ _ at main
    linarith only [main,slotcap,u0,sum_nonneg (s:=I) fun i _ ↦ sq_nonneg (π i*d i)]
  have low := (test_weight_bounds a0 a1 x0 x1).1
  have j0 : 0 ≤ j := zero_le_one.trans (representativeFactor_one x0 (by linarith only [x1]))
  have K0 : 0 ≤ K := sum_nonneg fun _ _ ↦ by dsimp only [betweenRows]; positivity
  have E0 : 0 ≤ energy := mul_nonneg (by dsimp [ρ]; positivity) n2
  have paid := pay_repairs low (show b=3/4*a*j by rfl) j0 K0 E0 k0 cs den cut
  change (4/3:ℝ)*(Q-energy)+(∑ i ∈ I,(j/r)*(U i).card*E' i)+(j/r)^2*K ≤ _
  have rep : (∑ i ∈ I,(j/r)*(U i).card*E' i) = j*T₁ := by
    dsimp [T₁]
    rw [mul_sum]
    exact sum_congr rfl fun _ _ ↦ by ring
  rw [rep]
  exact paid

end
end Erdos617.ColoredLists
