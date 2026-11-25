import PrunedWidth

/-! Sequential construction of the two pruning stages on the original coloring. -/

namespace Erdos617.ColoredLists

open Finset PruningOverlap PackingLists
open scoped Classical
noncomputable section

variable {V : Type*} {r : ℕ}

private def survivors (A : Finset V) (time : V → ℕ) (stop : ℕ) :=
  A.filter fun x ↦ stop ≤ time x

/-- A one-stage removal rule. At each time exactly one eligible vertex is
removed. The input to its test omits that vertex, as does its later star. -/
private theorem run_stage (A : Finset V) (eligible : Finset V → V → ℕ → Prop) :
    ∃ (time label : V → ℕ) (stop : ℕ),
      (∀ x ∈ A, time x < stop → eligible (A.filter fun y ↦ time x < time y) x (label x)) ∧
      (∀ x ∈ survivors A time stop, ∀ i, ¬eligible ((survivors A time stop).erase x) x i) ∧
      (∀ n < stop, ∃! x, x ∈ A ∧ time x = n) := by
  induction A using Finset.strongInductionOn with
  | _ A ih =>
    by_cases choice : ∃ x ∈ A, ∃ i, eligible (A.erase x) x i
    · obtain ⟨x,hx,i,pick⟩ := choice
      obtain ⟨tail,labels,cut,valid,done,unique⟩ := ih (A.erase x) (erase_ssubset hx)
      let time (v : V) := if v = x then 0 else tail v + 1
      let label (v : V) := if v = x then i else labels v
      have after : survivors A time (cut+1) = survivors (A.erase x) tail cut := by
        ext v
        by_cases h : v = x <;> simp [survivors,time,h,and_comm]
      refine ⟨time,label,cut+1,?_,by simpa only [after] using done,?_⟩
      · intro v hv hcut
        by_cases h : v = x
        · subst v
          have seteq : A.filter (fun y ↦ time x < time y) = A.erase x := by
            ext y
            by_cases eq : y = x <;> simp [time,eq,and_comm]
          simpa [seteq,label] using pick
        · have vt := valid v (mem_erase.mpr ⟨h,hv⟩) (by simpa [time,h] using hcut)
          have seteq : A.filter (fun y ↦ time v < time y) = (A.erase x).filter (fun y ↦ tail v < tail y) := by
            ext y
            by_cases eq : y = x <;> simp [time,h,eq]
          simpa [seteq,label,h] using vt
      · intro n hn
        cases n with
        | zero =>
          refine ⟨x,⟨hx,by simp [time]⟩,?_⟩
          intro y hy
          by_contra ne
          simp [time,ne] at hy
        | succ n =>
          obtain ⟨v,⟨hv,hnv⟩,uniq⟩ := unique n (by omega)
          refine ⟨v,⟨(mem_erase.mp hv).2, by simp [time,(mem_erase.mp hv).1,hnv]⟩,?_⟩
          intro y hy
          have ne : y ≠ x := by rintro rfl; simp [time] at hy
          exact uniq y ⟨mem_erase.mpr ⟨ne,hy.1⟩, by simpa [time,ne] using hy.2⟩
    · refine ⟨fun _ ↦ 0,fun _ ↦ 0,0,by simp,?_,by simp⟩
      simpa [survivors] using (show ∀ x ∈ A, ∀ i, ¬eligible (A.erase x) x i from fun x hx i hi ↦ choice ⟨x,hx,i,hi⟩)

variable [Fintype V]

/-- The terminal first-stage cap is retained for later sampling into any
qualifying row, even after more vertices are removed in the second stage. -/
def FirstStageStopped (T : Trace V r) : Prop :=
  let A := univ.filter fun v ↦ T.firstEnd ≤ T.time v
  ∀ x ∈ A, ∀ i ∈ qualifying T,
    4*(A.filter fun y ↦ T.crossGraph.Adj x y ∧ T.row y = i).card ≤ r

/-- After stage two, every survivor still has at most r/4 cross-row
target neighbors in each qualifying row. -/
theorem FirstStageStopped.live_bound {T : Trace V r} (done : FirstStageStopped T)
    {x : V} (hx : x ∈ live T) {i : ℕ} (hi : i ∈ qualifying T) :
    4*((live T).filter fun y ↦ T.crossGraph.Adj x y ∧ T.row y = i).card ≤ r := by
  let A := univ.filter fun v ↦ T.firstEnd ≤ T.time v
  have sub : live T ⊆ A := fun _ h ↦ mem_filter.mpr
    ⟨mem_univ _,T.stages.trans (mem_filter.mp h).2⟩
  exact (Nat.mul_le_mul_left 4 (card_le_card (filter_subset_filter _ sub))).trans (done x (sub hx) i hi)

/-- Every deletion time records precisely one source from the original coloring. -/
def Sequential (T : Trace V r) : Prop := ∀ n < T.stop, ∃! x, T.time x = n

theorem qualifying_bounds (T : Trace V r) (hr : 0 < r) {i : ℕ} (h : i ∈ qualifying T) :
    i < r ∧ 256*T.rowSize i ≤ 257*r ∧ unused T i ≤ 1/1200 := by
  obtain ⟨hi,hn⟩ := mem_sdiff.mp h
  have both : rawSurplus T i ≤ 1/256 ∧ unused T i ≤ 1/1200 := by
    by_contra! no
    apply hn
    apply mem_filter.mpr
    exact ⟨hi,by by_cases hs : rawSurplus T i ≤ 1/256
                 · exact Or.inr (no hs)
                 · exact Or.inl (lt_of_not_ge hs)⟩
  have pos : (0:ℝ) < r := by exact_mod_cast hr
  have size : (T.rowSize i:ℝ)/r-1 ≤ 1/256 := (le_max_left ..).trans both.1
  have hc := (div_le_iff₀ pos).mp (sub_le_iff_le_add.mp size)
  exact ⟨mem_range.mp hi,by exact_mod_cast (show (256:ℝ)*T.rowSize i ≤ 257*r by linarith),both.2⟩

/-- The two stopping rules can be executed on every original coloring and
row partition. All first-stage destinations qualify, and all vertices left
after stage two satisfy the required total-degree cap. -/
theorem exists_pruning_trace (color : {e : Sym2 V // ¬e.IsDiag} → Fin r) (target : Fin r)
    (row : V → ℕ) (hr : 0 < r) :
    ∃ T : Trace V r, T.color = color ∧ T.target = target ∧ T.row = row ∧ T.Legal ∧
      (∀ x ∈ T.firstSources, T.destination x ∈ qualifying T) ∧
      (∀ x ∈ live T, (Transversal.neighbors T.crossGraph (live T) x).card ≤ degreeBound r) ∧
      FirstStageStopped T ∧ Sequential T := by
  let raw : Trace V r := ⟨color,target,row,fun _ ↦ 0,0,0,le_rfl,fun _ ↦ 0⟩
  let first (A : Finset V) (x : V) (i : ℕ) := i ∈ qualifying raw ∧
    r < 4*(A.filter fun y ↦ raw.crossGraph.Adj x y ∧ row y = i).card
  let second (A : Finset V) (x : V) (_ : ℕ) :=
    199*r < 400*(A.filter (raw.crossGraph.Adj x)).card
  obtain ⟨t₁,label,k,valid₁,done₁,seq₁⟩ := run_stage univ first
  let B := survivors univ t₁ k
  have inB (x) : x ∈ B ↔ k ≤ t₁ x := by simp [B,survivors]
  obtain ⟨t₂,_,l,valid₂,done₂,seq₂⟩ := run_stage B second
  let time (x : V) := if t₁ x < k then t₁ x else k+t₂ x
  let T : Trace V r := ⟨color,target,row,time,k,k+l,Nat.le_add_right ..,label⟩
  have early (x) : time x < k ↔ t₁ x < k := by
    by_cases h : t₁ x < k <;> simp [time,h]
  have before (x y) (hx : t₁ x < k) : time x < time y ↔ t₁ x < t₁ y := by
    by_cases hy : t₁ y < k
    · simp [time,hx,hy]
    · simp only [time,ite_eq_left hx,ite_eq_right hy]
      omega
  have later (x y) (hx : ¬t₁ x < k) : time x < time y ↔ y ∈ B ∧ t₂ x < t₂ y := by
    by_cases hy : t₁ y < k <;> simp [time,hx,hy,inB] <;> omega
  have firstOK (x) (hx : t₁ x < k) := valid₁ x (mem_univ _) hx
  have survived : live T = survivors B t₂ l := by
    ext x
    change (x ∈ univ.filter fun y ↦ k+l ≤ time y) ↔ _
    by_cases hx : t₁ x < k <;> simp [survivors,time,hx,inB] <;> omega
  have originalStar (x) (hx : t₁ x < k) :
      T.star x = (univ.filter fun y ↦ t₁ x < t₁ y).filter
        (fun y ↦ raw.crossGraph.Adj x y ∧ row y = label x) := by
    ext y
    simp only [Trace.star,mem_filter,mem_univ,true_and]
    change (raw.crossGraph.Adj x y ∧ time x < k+l ∧ time x < time y ∧
        (time x < k → row y = label x)) ↔ _
    rw [before x y hx]
    have he := (early x).2 hx
    have ht : time x < k+l := by omega
    tauto
  have laterStar (x) (hx : ¬t₁ x < k) (hstop : time x < k+l) :
      T.star x = (B.filter fun y ↦ t₂ x < t₂ y).filter (raw.crossGraph.Adj x) := by
    ext y
    simp only [Trace.star,mem_filter,mem_univ,true_and]
    change (raw.crossGraph.Adj x y ∧ time x < k+l ∧ time x < time y ∧
        (time x < k → row y = label x)) ↔ _
    rw [later x y hx]
    have he : ¬time x < k := fun h ↦ hx ((early x).1 h)
    tauto
  refine ⟨T,rfl,rfl,rfl,⟨?_,?_⟩,?_,?_,?_,?_⟩
  · intro x hstop
    change time x < k+l at hstop
    by_cases hx : t₁ x < k
    · have count := (firstOK x hx).2
      rw [← originalStar x hx] at count
      have realCount : (r:ℝ) < 4*((T.star x).card:ℝ) := by exact_mod_cast count
      change (if time x < k then (r:ℝ)/4 else _) < _
      rw [ite_eq_left ((early x).2 hx)]
      linarith
    · have ts : t₂ x < l := by simpa [time,hx] using hstop
      have count := valid₂ x ((inB x).2 (le_of_not_gt hx)) ts
      change 199*r < 400*((B.filter fun y ↦ t₂ x < t₂ y).filter (raw.crossGraph.Adj x)).card at count
      rw [← laterStar x hx hstop] at count
      have realCount : (199:ℝ)*r < 400*((T.star x).card:ℝ) := by exact_mod_cast count
      change (if time x < k then (r:ℝ)/4 else if time x < k+l then _ else 0) < _
      rw [ite_eq_right (fun h ↦ hx ((early x).1 h)),ite_eq_left hstop]
      linarith
  · intro x hx
    exact (qualifying_bounds raw hr (firstOK x ((early x).mp hx)).1).2.1
  · intro x hx
    exact (firstOK x ((early x).mp (mem_filter.mp hx).2)).1
  · intro x hx
    rw [survived] at hx ⊢
    have cap := done₂ x hx 0
    change ¬199*r < 400*(((survivors B t₂ l).erase x).filter (raw.crossGraph.Adj x)).card at cap
    have er : ((survivors B t₂ l).erase x).filter (raw.crossGraph.Adj x) =
        (survivors B t₂ l).filter (raw.crossGraph.Adj x) := by
      ext y
      by_cases h : y = x <;> simp [h]
    rw [er] at cap
    apply (Nat.le_div_iff_mul_le (by decide : 0 < 400)).2
    change ((survivors B t₂ l).filter (raw.crossGraph.Adj x)).card*400 ≤ 199*r
    rw [Nat.mul_comm]
    exact le_of_not_gt cap
  · change ∀ x ∈ univ.filter (fun y ↦ k ≤ time y), ∀ i ∈ qualifying raw,
        4*((univ.filter (fun y ↦ k ≤ time y)).filter fun y ↦ raw.crossGraph.Adj x y ∧ row y = i).card ≤ r
    have mid : univ.filter (fun y ↦ k ≤ time y) = B := by
      ext y
      have h := early y
      simp [inB]
      omega
    rw [mid]
    intro x hx i hi
    have cap := done₁ x hx i
    change ¬(i ∈ qualifying raw ∧ r < 4*((B.erase x).filter fun y ↦ raw.crossGraph.Adj x y ∧ row y = i).card) at cap
    have er : (B.erase x).filter (fun y ↦ raw.crossGraph.Adj x y ∧ row y = i) =
        B.filter (fun y ↦ raw.crossGraph.Adj x y ∧ row y = i) := by
      ext y
      by_cases h : y = x <;> simp [h]
    rw [er] at cap
    exact le_of_not_gt (fun h ↦ cap ⟨hi,h⟩)
  · intro n hn
    change n < k+l at hn
    change ∃! x, time x = n
    by_cases h : n < k
    · obtain ⟨x,⟨_,hx⟩,unique⟩ := seq₁ n h
      refine ⟨x, by simp [time,hx,h],?_⟩
      intro y hy
      have he := (early y).mp (hy ▸ h)
      exact unique y ⟨mem_univ _, by simpa [time,he] using hy⟩
    · obtain ⟨x,⟨hx,t⟩,unique⟩ := seq₂ (n-k) (by omega)
      have mem := (inB x).mp hx
      refine ⟨x,by simp [time,not_lt.mpr mem,t]; omega,?_⟩
      intro y hy
      have he : ¬t₁ y < k := fun z ↦ h (hy ▸ (early y).mpr z)
      have ht : k+t₂ y = n := by simpa [time,he] using hy
      exact unique y ⟨(inB y).mpr (le_of_not_gt he),by omega⟩

end
end Erdos617.ColoredLists
