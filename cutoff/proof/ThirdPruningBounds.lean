import RetainedWidth

/-! Real inequalities supplied by the row counts in the zero-pair branch. -/
namespace Erdos617.ThirdPruning
noncomputable section

/-- The bounds keep all normalized edge-count variables in a single system.
The four last fields are the upper deficit, total holes, the deleted/deleted
charge and the two deleted/surviving charges from the third-pass note. -/
structure ZeroBounds (p t z s e k d h m w α β : ℝ) : Prop where
  p0 : 0 ≤ p
  p1 : p ≤ 125/61
  t0 : 0 ≤ t
  edge_eq : z = 1-p/4-(199/400)*t
  s0 : 0 ≤ s
  e0 : 0 ≤ e
  k0 : 0 ≤ k
  spent : s+e+(9/25)*k ≤ z
  old : w+2*s/α ≤ 0
  d0 : 0 ≤ d
  d1 : d ≤ 1
  h0 : 0 ≤ h
  m0 : 0 ≤ m
  holes : 1/2-s ≤ h+m
  deficit : d-1/400 ≤ k-β*(w+(s+z-e)/α)
  young : ∀ u : ℝ, 0 < u → u < 1 → 2*(1-u)*m ≤ d*(p+t+k)+s/(4*u)
  charge : 0 < 1-d →
    (1-d-e/(1-d)-199/400)*h ≤ z-s-e-(9/25)*k+2*(d+Real.sqrt s)*e ∧
    (1-d-e/(1-d)-199/400-9/25)*h ≤ z-s-e-(9/25)*k

theorem ZeroBounds.linear_young {p t z s e k d h m w α β : ℝ}
    (B : ZeroBounds p t z s e k d h m w α β) {D u : ℝ}
    (cap : d ≤ D) (hu : 0 < u) (hu' : u < 1) :
    2*(1-u)*m ≤ D*(p+t+k)+s/(4*u) :=
  (B.young u hu hu').trans (add_le_add_left
    (mul_le_mul_of_nonneg_right cap (by linarith only [B.p0,B.t0,B.k0])) _)

theorem ZeroBounds.linear_charge {p t z s e k d h m w α β : ℝ}
    (B : ZeroBounds p t z s e k d h m w α β) {D E U : ℝ}
    (hd : d ≤ D) (hD : D < 1) (he : e ≤ E) (hu : s ≤ U^2) (hu0 : 0 ≤ U) :
    (1-D-E/(1-D)-199/400)*h ≤ z-s-e-(9/25)*k+2*(D+U)*e ∧
    (1-D-E/(1-D)-199/400-9/25)*h ≤ z-s-e-(9/25)*k := by
  have hp : 0 < 1-D := by linarith
  have hdpos : 0 < 1-d := by linarith only [hd,hp]
  have sq := Real.sqrt_le_sqrt hu
  rw [Real.sqrt_sq hu0] at sq
  have frac : e/(1-d) ≤ E/(1-D) :=
    div_le_div₀ (B.e0.trans he) he hp (by linarith)
  have ht : 1-D-E/(1-D)-199/400 ≤ 1-d-e/(1-d)-199/400 := by linarith only [hd,frac]
  have real := B.charge hdpos
  refine ⟨(mul_le_mul_of_nonneg_right ht B.h0).trans (real.1.trans ?_),
    (mul_le_mul_of_nonneg_right (sub_le_sub_right ht _) B.h0).trans real.2⟩
  linarith only [mul_le_mul_of_nonneg_right (add_le_add hd sq) B.e0]

/-- A single affine lower support for the minimum of the two endpoint rebates. -/
theorem rebate_line {p : ℝ} (low : 0 ≤ p) (high : p ≤ 125/61) :
    (349+114*p)/1000 ≤ min ((391+(1464/5)*p)/1120) ((4333+737*p)/10000) := by
  apply le_min <;> linarith

end
end Erdos617.ThirdPruning
