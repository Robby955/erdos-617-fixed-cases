import CircleStartLaw

/-! Expected arc conflicts under independent local loads and independent uniform circle starts. -/

namespace Erdos617.ArcRepair

open Finset FiniteLaw ExcessCircle
open scoped Classical
noncomputable section

variable {I Ω : Type*} [Fintype I] [Fintype Ω]

/-- The conditional graph uses all pairs of distinct senders; the expectation
averages first over the starts for the actual observed loads, then over the sender states. -/
def expectedEdges (μ : I → Law Ω) (N : ℕ) [NeZero N] (len : I → Ω → ℕ) : ℝ :=
  (product μ).expect fun w ↦ (starts I N).expect fun z ↦
    ((graph z (fun i ↦ len i (w i))).edgeFinset.card:ℝ)

def active (t : ℕ) : ℝ := if 0<t then 1 else 0

/-- Each distinct pair has two possible length charges. At each endpoint
the positive-length indicator is multiplied only by the other sender's
length. Charging all ordered pairs then costs n times total expected length. -/
theorem expected_edges_bound (μ : I → Law Ω) (N : ℕ) [NeZero N] (len : I → Ω → ℕ) :
    expectedEdges μ N len ≤
      (∑ i, (μ i).expect (fun a ↦ active (len i a)))*
      (∑ i, (μ i).expect (fun a ↦ (len i a:ℝ)))/N := by
  let act := fun i => (μ i).expect fun a ↦ active (len i a)
  let leng := fun i => (μ i).expect fun a ↦ (len i a:ℝ)
  let pair := fun (i j : I) (w : I → Ω) (z : I → ZMod N) ↦
    if (graph z (fun k ↦ len k (w k))).Adj i j then (1:ℝ) else 0
  have pos : (0:ℝ) < N := by exact_mod_cast NeZero.pos N
  have pairBound (i j : I) :
      (product μ).expect (fun w ↦ (starts I N).expect (pair i j w)) ≤
      (act i*leng j+act j*leng i)/N := by
    by_cases eq : i=j
    · subst j
      have hp (w : I → Ω) : (starts I N).expect (pair i i w) = 0 := by
        simp [pair,Law.expect_const]
      simp_rw [hp,Law.expect_const]
      have act0 : 0≤act i := sum_nonneg fun a _ ↦ mul_nonneg ((μ i).nonneg a)
        (by dsimp only [active]; split <;> norm_num)
      have len0 : 0≤leng i := sum_nonneg fun a _ ↦ mul_nonneg ((μ i).nonneg a) (Nat.cast_nonneg _)
      positivity
    · have point (w : I → Ω) : (starts I N).expect (pair i j w) ≤
          (active (len i (w i))*(len j (w j):ℝ)+active (len j (w j))*(len i (w i):ℝ))*(N:ℝ)⁻¹ := by
        have pr := starts_pair_bound (N:=N) i j eq (len i (w i)) (len j (w j))
        have ne : i ≠ j := eq
        simpa only [pair,graph,and_iff_right ne,active,ite_mul,one_mul,zero_mul,div_eq_mul_inv] using pr
      have upper := (product μ).expect_mono point
      rw [Law.expect_mul_const,Law.expect_add,expect_pair μ eq
        (fun a ↦ active (len i a)) (fun a ↦ (len j a:ℝ)),expect_pair μ (Ne.symm eq)
        (fun a ↦ active (len j a)) (fun a ↦ (len i a:ℝ))] at upper
      exact upper
  have count (w : I → Ω) (z : I → ZMod N) :
      ((graph z (fun i ↦ len i (w i))).edgeFinset.card:ℝ) = (∑ i, ∑ j, pair i j w z)*(2:ℝ)⁻¹ :=
    edge_mass _
  unfold expectedEdges
  simp_rw [count,Law.expect_mul_const,Law.expect_sum]
  have all := sum_le_sum (s := univ) fun i _ ↦ sum_le_sum (s := univ) fun j _ ↦ pairBound i j
  apply (mul_le_mul_of_nonneg_right all (by norm_num : 0 ≤ (2:ℝ)⁻¹)).trans_eq
  simp only [div_eq_mul_inv,← sum_mul,sum_add_distrib,← mul_sum]
  ring

/-- n counts the heavy loads in expectation. L is total expected sender-local
load. On the circle of circumference 3r/4 the arc repair charge is at most
(4/3r)n(L−ρrn), with no charge for loads below the baseline. -/
theorem expected_excess_edges (μ : I → Law Ω) (s r : ℕ) (hs : 0<s) (hr : 0<r)
    (load : I → Ω → ℕ) :
    letI : NeZero (30*s*r) := ⟨by positivity⟩
    let n := ∑ i, (μ i).expect (fun a ↦ active (excess s r (load i a)))
    let L := ∑ i, (μ i).expect (fun a ↦ (load i a:ℝ))
    expectedEdges μ (30*s*r) (fun i a ↦ excess s r (load i a)) ≤
      (4/3:ℝ)/r*n*(L-((9/40:ℝ)/s*r)*n) := by
  let _ : NeZero (30*s*r) := ⟨by positivity⟩
  let base := (9/40:ℝ)/s*r
  let m := fun i a ↦ active (excess s r (load i a))
  let n := ∑ i, (μ i).expect (m i)
  let L := ∑ i, (μ i).expect (fun a ↦ (load i a:ℝ))
  have sp : (0:ℝ)<s := by exact_mod_cast hs
  have rp : (0:ℝ)<r := by exact_mod_cast hr
  have n0 : 0 ≤ n := sum_nonneg fun i _ ↦ sum_nonneg fun a _ ↦
    mul_nonneg ((μ i).nonneg a) (by dsimp only [m,active]; split <;> norm_num)
  have per (i : I) (a : Ω) : (excess s r (load i a):ℝ) ≤
      (40*(s:ℝ))*((load i a:ℝ)-m i a*base) := by
    by_cases heavy : 0 < excess s r (load i a)
    · have el := excess_units (r:=r) (t:=load i a) hs
      have strict : 0 < (excess s r (load i a):ℝ) := by exact_mod_cast heavy
      have diff : 0 < (load i a:ℝ)-base := by
        by_contra! bad
        change (excess s r (load i a):ℝ) = _*max ((load i a:ℝ)-base) 0 at el
        rw [max_eq_right bad,mul_zero] at el
        linarith only [strict,el]
      change _ ≤ _ * ((load i a:ℝ)-(if 0<excess s r (load i a) then 1 else 0)*base)
      rw [ite_eq_left heavy,one_mul,excess_units hs,max_eq_left diff.le]
    · have zero : excess s r (load i a)=0 := by omega
      simp [m,active,zero]; positivity
  have upper (i : I) : (μ i).expect (fun a ↦ (excess s r (load i a):ℝ)) ≤
      40*(s:ℝ)*((μ i).expect (fun a ↦ (load i a:ℝ))-(μ i).expect (m i)*base) := by
    apply ((μ i).expect_mono (per i)).trans_eq
    have h := (μ i).expect_add (fun a ↦ (load i a:ℝ)) (fun a ↦ m i a*(-base))
    rw [Law.expect_mul_const] at h
    rw [Law.expect_const_mul]
    simp only [mul_neg,← sub_eq_add_neg] at h
    rw [h]
  have sum := sum_le_sum (s:=univ) fun i _ ↦ upper i
  rw [← mul_sum,sum_sub_distrib,← sum_mul] at sum
  have initial := expected_edges_bound μ (30*s*r) (fun i a ↦ excess s r (load i a))
  change expectedEdges _ _ _ ≤ n*_/_ at initial
  apply initial.trans
  apply (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left sum n0) (Nat.cast_nonneg _)).trans_eq
  change n*(40*(s:ℝ)*(L-n*base))/(30*s*r:ℕ) = (4/3:ℝ)/r*n*(L-base*n)
  push_cast; field_simp
  ring

end
end Erdos617.ArcRepair
