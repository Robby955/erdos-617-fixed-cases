import Mathlib.Data.Finset.Card
import Mathlib.Data.Sym.Sym2

namespace Erdos617

/-- The vertices are exactly the r² + 1 points of the complete graph. An
edge is an unordered pair of distinct vertices, so a coloring assigns no
colors to loops. -/
def BalancedColoringAt (r : ℕ) : Prop :=
  ∀ color : {e : Sym2 (Fin (r^2 + 1)) // ¬ e.IsDiag} → Fin r,
    ∃ (S : Finset (Fin (r^2 + 1))) (j : Fin r), S.card = r + 1 ∧
      ∀ x ∈ S, ∀ y ∈ S, ∀ h : x ≠ y, color ⟨s(x,y), fun d => h (Sym2.mk_isDiag_iff.mp d)⟩ ≠ j

/-- The statement of Theorem A in the November 24 paper. -/
def CutoffStatement : Prop := ∀ r : ℕ, 2^144 ≤ r → BalancedColoringAt r

end Erdos617
