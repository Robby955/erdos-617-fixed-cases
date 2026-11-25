import ExteriorRowEdges
import AuxiliaryDeficitCaps

/-! A sender with exactly two large rows must cover the target cut between
their nonneighbor lists. Three or more large incidences pay directly for the sender.
-/

namespace Erdos617.ColoredLists

open Finset
open scoped Classical
noncomputable section

/-- The threshold and fractional upper deficit for an original (unenlarged)
clique. The auxiliary bound uses the stronger joint square budget. -/
def ArrivalRow (θ d : ℝ) : Prop :=
  (θ = 81/200 ∧ d ≤ 317/2000) ∨ (θ = 369/1000 ∧ d ≤ 1/256)

/-- The two normalized row-degree thresholds leave a nonneighbor rectangle
larger than the maximum target cut, unless the combined degree exceeds the
price for a combined deficit of 213/1000. This same price works for every
ordered pair of types. -/
theorem two_arrival_degree_fraction {a b d e θ φ : ℝ}
    (left : ArrivalRow θ d) (right : ArrivalRow φ e)
    (largeL : θ < a) (largeR : φ < b)
    (rectangle : (1-d-a)*(1-e-b) ≤ (317/2000:ℝ)^2+1/2^20) :
    1+(77/100:ℝ)*(213/1000)+2/10000 < a+b := by
  by_contra! total
  have reduce (D E : ℝ) (dD : d ≤ D) (eE : e ≤ E)
      (hD : 0 ≤ 1-D-a) (hE : 0 ≤ 1-E-b) :
      (1-D-a)*(1-E-b) ≤ (317/2000:ℝ)^2+1/2^20 :=
    (mul_le_mul (by linarith only [dD] : 1-D-a ≤ 1-d-a)
      (by linarith only [eE]) hE (by linarith only [hD,dD])).trans rectangle
  have product := mul_nonneg (sub_nonneg.mpr largeL.le) (sub_nonneg.mpr largeR.le)
  rcases left with ⟨rfl,dD⟩|⟨rfl,dD⟩ <;> rcases right with ⟨rfl,eE⟩|⟨rfl,eE⟩ <;>
    have bound := reduce _ _ dD eE (by linarith only [total,largeR])
      (by linarith only [total,largeL]) <;>
    nlinarith only [bound,total,largeL,largeR,product]

variable {V : Type*} {r : ℕ}

/-- A complete rectangle of target edges between the two lists of
nonneighbors charges one actual edge for every ordered choice of endpoints. -/
theorem nonneighbor_rectangle (G : SimpleGraph V) (C D : Finset V) (x : V)
    (complete : ∀ u ∈ C, ¬G.Adj x u → ∀ v ∈ D, ¬G.Adj x v → G.Adj u v) :
    ((C.filter (fun u ↦ ¬G.Adj x u)).card:ℝ)*(D.filter (fun v ↦ ¬G.Adj x v)).card ≤
      ∑ v ∈ D, ((C.filter (G.Adj v)).card:ℝ) := by
  let N := C.filter fun u ↦ ¬G.Adj x u
  let M := D.filter fun v ↦ ¬G.Adj x v
  have per (v) (hv : v ∈ M) : (N.card:ℝ) ≤ (C.filter (G.Adj v)).card := by
    apply Nat.cast_le.mpr (card_le_card ?_)
    intro u hu
    obtain ⟨uC,xu⟩ := mem_filter.mp hu
    obtain ⟨vD,xv⟩ := mem_filter.mp hv
    exact mem_filter.mpr ⟨uC,G.adj_symm (complete u uC xu v vD xv)⟩
  calc _ = ∑ _v ∈ M, (N.card:ℝ) := by simp [M,N]; ring
       _ ≤ ∑ v ∈ M, ((C.filter (G.Adj v)).card:ℝ) := sum_le_sum per
       _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset ..) (fun _ _ _ ↦ Nat.cast_nonneg _)

/-- In the original edge coloring, two large rows joined completely on
their nonneighbor lists force a combined degree larger than the two arrival
prices and r. Both rows are the original cliques used to prescribe representatives. -/
theorem two_large_row_price (color : {e : Sym2 V // ¬e.IsDiag} → Fin r)
    (j : Fin r) (C D : Finset V) (x : V) (hr : 2^20 ≤ r) (no : ¬Witness color)
    (dis : Disjoint C D) (clC : (targetGraph color j).IsClique (C:Set V))
    (clD : (targetGraph color j).IsClique (D:Set V)) (θ φ : ℝ)
    (typeC : ArrivalRow θ (((r:ℝ)-C.card)/r)) (typeD : ArrivalRow φ (((r:ℝ)-D.card)/r))
    (largeC : θ*r < ((C.filter ((targetGraph color j).Adj x)).card:ℝ))
    (largeD : φ*r < ((D.filter ((targetGraph color j).Adj x)).card:ℝ))
    (complete : ∀ u ∈ C, ¬(targetGraph color j).Adj x u →
      ∀ v ∈ D, ¬(targetGraph color j).Adj x v → (targetGraph color j).Adj u v) :
    (1+(77/100:ℝ)*(213/1000)+2/10000)*r <
      ((C.filter ((targetGraph color j).Adj x)).card:ℝ)+(D.filter ((targetGraph color j).Adj x)).card := by
  let G := targetGraph color j
  let deg (S : Finset V) : ℝ := (S.filter (G.Adj x)).card
  let rem (S : Finset V) : ℝ := (S.filter (fun v ↦ ¬G.Adj x v)).card
  let defic (S : Finset V) : ℝ := (r:ℝ)-S.card
  have pos : (0:ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hlarge : (2:ℝ)^20 ≤ r := by exact_mod_cast hr
  have hr' : 2 ≤ r := by omega
  have div (S : Finset V) : 1-(defic S)/r-deg S/r = rem S/r := by
    have count := card_filter_add_card_filter_not (s := S) (G.Adj x)
    have add : deg S+rem S = (S.card:ℝ) := by
      dsimp only [deg,rem]
      exact_mod_cast count
    dsimp [defic]
    field_simp
    linarith only [add]
  have capped (S : Finset V) (θ : ℝ) (hS : ArrivalRow θ (defic S/r)) :
      defic S ≤ (317/2000:ℝ)*r := by
    apply (div_le_iff₀ pos).mp
    rcases hS with ⟨_,h⟩|⟨_,h⟩
    · exact h
    · linarith only [h]
  have cap := (caps_of_no_witness color j hr' no).2
  have d0 : 0 ≤ defic C := sub_nonneg.mpr (by exact_mod_cast cap C clC)
  have e0 : 0 ≤ defic D := sub_nonneg.mpr (by exact_mod_cast cap D clD)
  have rect := (nonneighbor_rectangle G C D x complete).trans (clique_pair_capacity color j C D hr' no dis clC clD)
  change rem C*rem D ≤ (r:ℝ)-defic C-defic D+defic C*defic D at rect
  have dc := capped C θ typeC
  have ed := capped D φ typeD
  have mult := mul_le_mul dc ed e0 (by positivity)
  have round : (r:ℝ) ≤ (1/2^20:ℝ)*(r:ℝ)^2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hlarge) pos.le]
  have budget : (1-defic C/r-deg C/r)*(1-defic D/r-deg D/r) ≤ (317/2000:ℝ)^2+1/2^20 := by
    rw [div,div,div_mul_div_comm]
    apply (div_le_iff₀ (mul_pos pos pos)).mpr
    nlinarith only [mult,rect,d0,e0,round]
  have yes := two_arrival_degree_fraction typeC typeD
    ((lt_div_iff₀ pos).mpr largeC) ((lt_div_iff₀ pos).mpr largeD) budget
  rw [← add_div] at yes
  exact (lt_div_iff₀ pos).mp yes

/-- The exact pooled deficits of any two tagged rows are within the uniform
fraction used in the two-row graph theorem. -/
theorem two_tagged_price_cap (J : Finset (ℕ ⊕ ℕ)) (count : J.card = 2) :
    AuxiliaryMoments.peeledCap J.toLeft.card+(J.toRight.card:ℝ)/256 ≤ 213/1000 := by
  have total : J.toLeft.card+J.toRight.card = 2 := card_toLeft_add_card_toRight.trans count
  generalize hj : J.toLeft.card = j at *
  generalize hk : J.toRight.card = k at *
  have hjMax : j ≤ 2 := by omega
  have hkMax : k ≤ 2 := by omega
  interval_cases j <;> interval_cases k <;> norm_num [AuxiliaryMoments.peeledCap] at *

def arrivalThreshold (i : ℕ ⊕ ℕ) : ℝ :=
  i.elim (fun _ ↦ 81/200) (fun _ ↦ 369/1000)

/-- Three large incidences cover r after paying the prices of all three rows.
The input deficit sum is in vertex units and can use the enlarged rows. -/
theorem three_large_rows_price (J : Finset (ℕ ⊕ ℕ)) (count : J.card = 3)
    (r : ℝ) (hr : 0 < r) (degree deficit : ℕ ⊕ ℕ → ℝ)
    (large : ∀ i ∈ J, arrivalThreshold i*r ≤ degree i)
    (joint : ∑ i ∈ J, deficit i ≤ r*(AuxiliaryMoments.peeledCap J.toLeft.card+
      (J.toRight.card:ℝ)/256)) :
    r < ∑ i ∈ J, (degree i-((77/100:ℝ)*deficit i+(1/10000)*r)) := by
  have total : J.toLeft.card+J.toRight.card = 3 := card_toLeft_add_card_toRight.trans count
  have cmp : 1 < (J.toLeft.card:ℝ)*(81/200)+(J.toRight.card:ℝ)*(369/1000)-
      ((77/100)*(AuxiliaryMoments.peeledCap J.toLeft.card+(J.toRight.card:ℝ)/256)+3/10000) := by
    generalize hj : J.toLeft.card = j at *
    generalize hk : J.toRight.card = k at *
    have hjMax : j ≤ 3 := by omega
    have hkMax : k ≤ 3 := by omega
    interval_cases j <;> interval_cases k <;> norm_num [AuxiliaryMoments.peeledCap] at *
  have payment := mul_lt_mul_of_pos_right cmp hr
  have gross := sum_le_sum large
  have prices : (∑ i ∈ J, arrivalThreshold i*r) =
      ((J.toLeft.card:ℝ)*(81/200)+(J.toRight.card:ℝ)*(369/1000))*r := by
    rw [← sum_mul, sum_sum_eq_sum_toLeft_add_sum_toRight]
    simp [arrivalThreshold]
  rw [prices] at gross
  rw [sum_sub_distrib,sum_add_distrib,← mul_sum,sum_const,nsmul_eq_mul,count]
  push_cast
  linarith only [gross,joint,payment]

/-- Every further large incidence contributes positively even after its
enlarged row is priced at its largest permitted deficit. -/
theorem additional_large_price {r d θ degree : ℝ} (hr : 0 < r)
    (kind : ArrivalRow θ (d/r)) (large : θ*r ≤ degree) :
    0 < degree-((77/100)*d+(1/10000)*r) := by
  rcases kind with ⟨rfl,h⟩|⟨rfl,h⟩ <;>
    linarith only [hr,large,(div_le_iff₀ hr).mp h]

end
end Erdos617.ColoredLists
