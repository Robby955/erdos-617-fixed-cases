import WidthIntegral
import Mathlib.Data.Finset.Max

/-! Finite row selection and translation back to the units of equation (4). -/

namespace Erdos617.WidthIntegral

variable {ι : Type*} [DecidableEq ι]

/-- Select exactly k heaviest rows. Tied rows can be put on either side. -/
theorem exists_heaviest (rows : Finset ι) (a : ι → ℝ) (k : ℕ) (hk : k ≤ rows.card) :
    ∃ R ⊆ rows, R.card = k ∧ ∀ i ∈ rows \ R, ∀ j ∈ R, a i ≤ a j := by
  induction k generalizing rows with
  | zero => exact ⟨∅, Finset.empty_subset _, rfl, by simp⟩
  | succ k ih =>
    obtain ⟨j, hj, hm⟩ := rows.exists_max_image a (Finset.card_pos.mp (by omega))
    obtain ⟨U, hU, hcard, horder⟩ := ih (rows.erase j) (by rw [Finset.card_erase_of_mem hj]; omega)
    have hjU : j ∉ U := fun h ↦ (Finset.mem_erase.mp (hU h)).1 rfl
    refine ⟨insert j U, Finset.insert_subset hj (hU.trans (Finset.erase_subset ..)),
      by rw [Finset.card_insert_of_notMem hjU, hcard], ?_⟩
    intro i hi b hb
    obtain ⟨hir, hi'⟩ := Finset.mem_sdiff.mp hi
    rcases Finset.mem_insert.mp hb with rfl | hb
    · exact hm _ hir
    · apply horder _ (Finset.mem_sdiff.mpr ⟨Finset.mem_erase.mpr ⟨fun h ↦ hi' (h ▸ Finset.mem_insert_self ..), hir⟩,
        fun h ↦ hi' (Finset.mem_insert_of_mem h)⟩) _ hb


/-- Parts failing either raw destination test. The size argument is the
positive part of (|Rᵢ|−r)/r, and U is the normalized unused incidence budget. -/
noncomputable def unqualified (raw : Finset ι) (surplus U : ι → ℝ) : Finset ι :=
  raw.filter fun i ↦ 1/256 < surplus i ∨ 1/1200 < U i

/-- Recover the omitted-slot bound of the cutoff chapter from the two raw
row sums. The load at i counts first-stage sources assigned to i, in units
of r. A destination receiving a positive load passes both tests. -/
theorem omitted_slots_of_row_charges (raw : Finset ι) (surplus U assigned : ι → ℝ)
    (e₀ n : ℕ) {p : ℝ} (hsurplus : ∀ i ∈ raw, 0 ≤ surplus i)
    (hassigned : ∀ i ∈ raw, 0 ≤ assigned i)
    (sizes : ∑ i ∈ raw, surplus i ≤ 1/2) (costs : ∑ i ∈ raw, U i ≤ 1/2)
    (loads : ∑ i ∈ raw, assigned i = p)
    (localCost : ∀ i ∈ raw, (61/250)*assigned i ≤ U i)
    (destination : ∀ i ∈ raw, 0 < assigned i → surplus i ≤ 1/256 ∧ U i ≤ 1/1200)
    (omitted : e₀ ≤ (unqualified raw surplus U).card+n) :
    (e₀:ℝ)+1 ≤ 729-(1464/5)*p+n := by
  classical
  let big := raw.filter fun i ↦ 1/256 < surplus i
  let high := raw.filter fun i ↦ 1/1200 < U i
  have hbig : (big.card:ℝ)*(1/256) ≤ ∑ i ∈ raw, surplus i := by
    calc _ = ∑ i ∈ raw, (if 1/256 < surplus i then (1/256:ℝ) else 0) := by
           simp [big, Finset.sum_ite]
         _ ≤ _ := by
           apply Finset.sum_le_sum
           intro i hi
           split_ifs with h
           · exact h.le
           · exact hsurplus i hi
  have hhigh : (high.card:ℝ)*(1/1200)+(61/250)*p ≤ ∑ i ∈ raw, U i := by
    calc _ = ∑ i ∈ raw, ((if 1/1200 < U i then (1/1200:ℝ) else 0)+(61/250)*assigned i) := by
           rw [Finset.sum_add_distrib, ← Finset.mul_sum, loads]
           simp [high, Finset.sum_ite]
         _ ≤ _ := by
           apply Finset.sum_le_sum
           intro i hi
           split_ifs with h
           · have hzero : assigned i = 0 := le_antisymm (le_of_not_gt (fun hpos ↦
               (not_lt.mpr (destination i hi hpos).2) h)) (hassigned i hi)
             simpa [hzero] using h.le
           · simpa using localCost i hi
  have heq : unqualified raw surplus U = big ∪ high := by
    ext i
    simp only [unqualified, big, high, Finset.mem_filter, Finset.mem_union]
    tauto
  rw [heq] at omitted
  have hnum : e₀ ≤ big.card+high.card+n :=
    omitted.trans (Nat.add_le_add_right (Finset.card_union_le ..) n)
  have hre : (e₀:ℝ) ≤ big.card+high.card+(n:ℝ) := by exact_mod_cast hnum
  linarith only [hre, hbig, hhigh, sizes, costs]

/-- Normalized breakpoint, with b = y/α and d = x/(2β). -/
noncomputable def weight (m b d : ℝ) := m * max b d

/-- Each row pays its full integrated cost, even when its weight is zero. -/
theorem row_cost {m b d : ℝ} (hm : 0 < m) (hb : 0 ≤ b) (hd : 0 ≤ d) :
    0 ≤ weight m b d ∧ m*d^2 ≤ (weight m b d)^2/m ∧
    weight m b d/m + (m*d^2)/weight m b d ≤ b+2*d := by
  let f := max b d
  have hfd : d ≤ f := le_max_right _ _
  have hf : 0 ≤ f := hd.trans hfd
  have hfb : f ≤ b+d := max_le (by linarith) (by linarith)
  change 0 ≤ m*f ∧ m*d^2 ≤ (m*f)^2/m ∧ m*f/m+(m*d^2)/(m*f) ≤ b+2*d
  have hsq : d^2 ≤ f^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hfd) (add_nonneg hf hd)]
  refine ⟨mul_nonneg hm.le hf, ?_, ?_⟩
  · calc m*d^2 ≤ m*f^2 := mul_le_mul_of_nonneg_left hsq hm.le
         _ = (m*f)^2/m := by field_simp
  · rw [mul_div_cancel_left₀ _ hm.ne', mul_div_mul_left _ _ hm.ne']
    rcases hf.eq_or_lt with h | h
    · have hd' : d = 0 := by linarith
      simp [← h, hd', hb]
    · have hdiv : d^2/f ≤ d := (div_le_iff₀ h).2 (by nlinarith [mul_le_mul_of_nonneg_left hfd hd])
      linarith

/-- The cutoff proof uses the same z, the same s and the same retained rows
in all three estimates. Omitted slots include the original e₀ omissions. -/
structure Selection (rows : Finset ι) (x y : ι → ℝ) (e₀ n : ℕ) (α β S : ℝ) where
  reserved : Finset ι
  retained : Finset ι
  z : ℝ
  s : ℕ
  w : ℝ
  reserved_sub : reserved ⊆ rows
  reserved_count : reserved.card + e₀ + 1 = 1120 + 2*n
  retained_eq : retained = (rows \ reserved).filter (fun i ↦ max (y i) (α*x i/(2*β)) ≤ z)
  level_lo : α/S ≤ z
  level_hi : z ≤ α/(1120+2*(n:ℝ))
  width_eq : w = s*z/α
  width_pos : 0 < w
  width_lt : w < 1
  omitted : e₀+(rows \ retained).card+1 = s
  scale_lo : 1120 ≤ s
  scale_hi : (s:ℝ) < S
  incidence : ∀ i ∈ retained, s*y i ≤ α*w
  deficit : ∀ i ∈ retained, s*x i ≤ 2*β*w
  squares : s*(∑ i ∈ retained, (x i)^2) ≤ 4*β^2*w*(1-w)

/-- A successful test gives the complete simultaneous conclusion in paper units. -/
theorem selection_of_level (rows R : Finset ι) (x y : ι → ℝ) (e₀ n : ℕ)
    {α β S t : ℝ} (hα : 0 < α) (hβ : 0 < β) (hS : 0 < S) (hR : R ⊆ rows)
    (hc : R.card + e₀ + 1 = 1120+2*n)
    (ht₀ : (1120+2*(n:ℝ))/S ≤ t) (ht₁ : t ≤ 1)
    (success : let m : ℝ := 1120+2*(n:ℝ)
               t + ∑ i ∈ rows \ R, load m (weight m (y i/α) (x i/(2*β)))
                 (m*(x i/(2*β))^2) t < 1) :
    Nonempty (Selection rows x y e₀ n α β S) := by
  classical
  let m : ℝ := 1120+2*(n:ℝ)
  have hm : 0 < m := by dsimp [m]; positivity
  have ht : 0 < t := (div_pos hm hS).trans_le ht₀
  let a := fun i ↦ weight m (y i/α) (x i/(2*β))
  let q := fun i ↦ m*(x i/(2*β))^2
  let pool := rows \ R
  let keep := pool.filter fun i ↦ a i ≤ t
  let heavy := pool.filter fun i ↦ t < a i
  let s := 1120+2*n+heavy.card
  let z := α*t/m
  let w := (s:ℝ)*t/m
  have hsn : 1120 ≤ s := by dsimp [s]; omega
  have hs : (0:ℝ) < s := by exact_mod_cast (show 0 < s by omega)
  have hse : (s:ℝ) = m + heavy.card := by dsimp [s,m]; push_cast; ring
  have hsplit : t + ∑ i ∈ pool, load m (a i) (q i) t = w + (∑ i ∈ keep, q i)/t := by
    simp only [load, Finset.sum_ite, not_lt, Finset.sum_const, nsmul_eq_mul, ← Finset.sum_div]
    change t + ((heavy.card:ℝ)*(t/m)+(∑ i ∈ keep, q i)/t) = w+(∑ i ∈ keep, q i)/t
    dsimp [w]
    rw [hse]
    field_simp; ring
  change t + ∑ i ∈ pool, load m (a i) (q i) t < 1 at success
  rw [hsplit] at success
  have hq : 0 ≤ ∑ i ∈ keep, q i := Finset.sum_nonneg fun i _ ↦ mul_nonneg hm.le (sq_nonneg _)
  have hw : w < 1 := by linarith [div_nonneg hq ht.le]
  have hw₀ : 0 < w := div_pos (mul_pos hs ht) hm
  have hz (i : ι) : a i ≤ t ↔ max (y i) (α*x i/(2*β)) ≤ z := by
    change m * max _ _ ≤ t ↔ max _ _ ≤ α*t/m
    rw [← le_div_iff₀' hm, max_le_iff, max_le_iff]
    constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor
    · calc y i ≤ (t/m)*α := (div_le_iff₀ hα).1 h₁
           _ = _ := by ring
    · calc α*x i/(2*β) = α*(x i/(2*β)) := by ring
           _ ≤ α*(t/m) := mul_le_mul_of_nonneg_left h₂ hα.le
           _ = _ := by ring
    · apply (div_le_iff₀ hα).2; convert! h₁ using 1; ring
    · apply (le_of_mul_le_mul_left _ hα)
      convert! h₂ using 1 <;> ring
  have hcount : heavy.card + keep.card = pool.card := by
    simpa [heavy, keep, not_lt] using pool.card_filter_add_card_filter_not (fun i ↦ t < a i)
  have hkeep : keep ⊆ rows := (Finset.filter_subset ..).trans (Finset.sdiff_subset)
  have hpool : pool.card = rows.card-R.card := Finset.card_sdiff_of_subset hR
  have hrle := Finset.card_le_card hR
  have hkraw (i : ι) (hi : i ∈ keep) := (max_le_iff.mp ((hz i).1 (Finset.mem_filter.mp hi).2))
  refine ⟨{
    reserved := R
    retained := keep
    z := z
    s := s
    w := w
    reserved_sub := hR
    reserved_count := hc
    retained_eq := ?_
    level_lo := ?_
    level_hi := ?_
    width_eq := ?_
    width_pos := hw₀
    width_lt := hw
    omitted := ?_
    scale_lo := hsn
    scale_hi := ?_
    incidence := ?_
    deficit := ?_
    squares := ?_
  }⟩
  · exact Finset.filter_congr fun i _ ↦ hz i
  · dsimp [z]; apply (le_div_iff₀ hm).2
    calc α/S*m = α*(m/S) := by ring
         _ ≤ _ := mul_le_mul_of_nonneg_left ht₀ hα.le
  · exact div_le_div_of_nonneg_right (by nlinarith [mul_le_mul_of_nonneg_left ht₁ hα.le]) hm.le
  · dsimp [w,z]; field_simp
  · rw [Finset.card_sdiff_of_subset hkeep]; dsimp [s]; omega
  · have hp := (div_lt_iff₀ hm).1 hw
    have hlo := mul_le_mul_of_nonneg_left ht₀ hs.le
    have hdiv : (s:ℝ)*m/S < m := by linarith only [hlo, hp, show (s:ℝ)*(m/S) = (s:ℝ)*m/S by ring]
    have hfin := (div_lt_iff₀ hS).1 hdiv
    exact lt_of_mul_lt_mul_right (a := m) (by linarith only [hfin]) hm.le
  · intro i hi
    have he : α*w = s*z := by dsimp [w,z]; ring
    rw [he]; exact mul_le_mul_of_nonneg_left (hkraw i hi).1 hs.le
  · intro i hi
    have he := (div_le_iff₀ (by positivity : 0 < 2*β)).1 (hkraw i hi).2
    have hin : x i ≤ (2*β)*t/m := by
      apply le_of_mul_le_mul_left _ hα
      convert! he using 1; dsimp [z]; ring
    calc (s:ℝ)*x i ≤ s*((2*β)*t/m) := mul_le_mul_of_nonneg_left hin hs.le
         _ = _ := by dsimp [w]; ring
  · have hqsum : (∑ i ∈ keep, q i) = (m/(4*β^2)) * ∑ i ∈ keep, (x i)^2 := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl
      intro i _; dsimp [q]; ring
    have h₁ : (∑ i ∈ keep, q i) < (1-w)*t := (div_lt_iff₀ ht).1 (by linarith)
    rw [hqsum] at h₁
    have h₂ : m * (∑ i ∈ keep, (x i)^2) ≤ (1-w)*t*(4*β^2) := by
      rw [div_mul_eq_mul_div] at h₁
      exact ((div_lt_iff₀ (by positivity)).1 h₁).le
    calc (s:ℝ)*(∑ i ∈ keep, (x i)^2) = (s/m)*(m*(∑ i ∈ keep, (x i)^2)) := by field_simp
         _ ≤ (s/m)*((1-w)*t*(4*β^2)) := mul_le_mul_of_nonneg_left h₂ (div_nonneg hs.le hm.le)
         _ = _ := by dsimp [w]; ring

end Erdos617.WidthIntegral
