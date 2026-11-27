import Mathlib.Tactic

/-! A rational certificate for the last signed cut. The nine width intervals
in each band use the same formulas as the manuscript's finer grid. -/

namespace Erdos617.CutoffCells

structure BandData where
  α : ℚ
  β : ℚ
  y : ℚ
  exponent : ℕ

def bandData : Fin 5 → BandData := ![
  ⟨656/4000,925/4000,501/1000,14⟩,
  ⟨656/4000,923/4000,55/100,14⟩,
  ⟨653/4000,918/4000,65/100,14⟩,
  ⟨652/4000,916/4000,1,15⟩,
  ⟨654/4000,918/4000,2,17⟩]

def boundaries : Fin 10 → ℚ := ![0, 1/2, 72/128, 80/128, 96/128, 112/128,
  120/128, 124/128, 126/128, 1]

def left (j : Fin 9) := boundaries j.castSucc
def right (j : Fin 9) := boundaries j.succ
def peak (j : Fin 9) := max (1/2) (left j)

def incidence (d : BandData) (j : Fin 9) := d.α*right j
def deficit (d : BandData) (j : Fin 9) := 2*d.β*right j
def kappa (d : BandData) (j : Fin 9) := 4*d.β^2*peak j*(1-peak j)/(9/40)

/-- Evaluate ε and the signed margin in an ordered field. The same expression
is evaluated in ℚ for checking and in ℝ for use in the coloring theorem. -/
def values {K : Type*} [Field K] [LinearOrder K] (A X Y κ R l : K) : K × K :=
  let f : K := 9/40
  let ρ₀ := f/1120
  let g := X/f
  let j := (1+100*ρ₀)/(1-X/1120)
  let a := min (5/2) ((249/250)/((513/512)*(A/f)+1/256+X/1120+5/1464))
  let b := (3/4)*a*j
  let V := a*((513/512)*Y/f+7/1120)+9*b/1120
  let η := 1/(R*f^2)
  let repair := fun W l' ↦ ((4/3)/(a-4/3))*((b*W+l')^2/(2-a*κ)+η*(((1+V)^2+V/1120)/2+1/(2*1120)))
  let Z := fun W ↦ 8*repair W 0+2*η
  let W := (1/(1-X/1120)+(501/1000)*g/37)*κ+g*(Z (2*κ))*ρ₀/37
  let ε := repair W l+g*l+l^2/2+η*(1/2+1/(2*1120))
  (ε,(1-ε)*(3/20-(501/1000)*κ*ρ₀)+l-(501/1000)*κ-Z W*ρ₀-1/(f*R*1120^2))

def endpoint (d : BandData) (j : Fin 9) (l : ℚ) :=
  values (incidence d j) (deficit d j) d.y (kappa d j) (2^d.exponent) l

/-- Both ends of the interval of possible normalized shortages pass. -/
def passes (i : Fin 5) (j : Fin 9) : Prop :=
  let d := bandData i
  let test := fun l ↦ (endpoint d j l).1 < 1 ∧ 0 < (endpoint d j l).2
  test 0 ∧ test ((501/1000)*kappa d j)
instance (i : Fin 5) (j : Fin 9) : Decidable (passes i j) := by
  unfold passes
  infer_instance

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem all_cells_pass : ∀ (i : Fin 5) (j : Fin 9), passes i j := by decide +kernel

theorem cell_ranges : ∀ (i : Fin 5) (j : Fin 9),
    let d := bandData i
    0 ≤ d.α ∧ 0 ≤ d.β ∧ 0 ≤ incidence d j ∧ incidence d j ≤ 656/4000 ∧
    0 ≤ deficit d j ∧ deficit d j ≤ 1/2 ∧ 0 ≤ kappa d j ∧ kappa d j ≤ 1/4 ∧
    0 ≤ d.y ∧ d.y ≤ 2 := by decide +kernel

theorem peak_side : ∀ j : Fin 9,
    (peak j = left j ∧ 1/2 ≤ left j) ∨ (peak j = right j ∧ right j ≤ 1/2) := by decide +kernel

end Erdos617.CutoffCells
