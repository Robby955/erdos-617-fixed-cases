import ColoringSenderLaw
import SenderSampleMoments
import RepresentativeRepairs

/-! One thinning law on the original vertices gives the exterior cardinality
moments and the bound on the representative repair edges simultaneously. -/

namespace Erdos617.ColoredLists

open Finset PruningOverlap PackingLists FiniteLaw MarkedSender RepresentativeRepairs
open scoped Classical
noncomputable section
variable {V : Type*} {r : ℕ} [Fintype V] (T : Trace V r)

theorem retry_rate_of_scale {s : ℕ} (hs : 1120 ≤ s) : 100*((9/40:ℝ)/s) ≤ 1 := by
  have lo : (1120:ℝ) ≤ s := by exact_mod_cast hs
  have pos : (0:ℝ)<s := by linarith
  rw [← mul_div_assoc,div_le_iff₀ pos]
  linarith only [lo]

/-- The fixed low exterior and the random marked senders are disjoint sets of
original vertices. Thus the signed fluctuation in exterior order is exactly
the fluctuation in the mark count. -/
theorem sampled_exterior_order (E : Finset V) (parts : Finset ℕ) (s : ℕ) (w : V → State V) :
    let H := senderSet T E parts s
    let L := lowExterior T E parts s
    ((exterior H L w).card:ℝ) = L.card + markCount H w := by
  dsimp only
  let H := senderSet T E parts s
  let L := lowExterior T E parts s
  have dis : Disjoint L (H.filter fun v ↦ (w v).isSome) := by
    apply disjoint_left.mpr
    intro v hv h
    exact (mem_sdiff.mp (mem_filter.mp h).1).2 hv
  have indic (v : V) : marked (w v) = if (w v).isSome then 1 else 0 := by
    cases w v <;> rfl
  change ((L ∪ (H.filter fun v ↦ (w v).isSome)).card:ℝ) = L.card + ∑ v ∈ H, marked (w v)
  rw [card_union_of_disjoint dis,Nat.cast_add]
  simp only [indic, sum_boole]

/-- The two signed-order moments hold for every thinning probability,
including the larger probability used in the oversampling argument. -/
theorem exterior_shortage_moments (E : Finset V) (I : Finset ℕ) (s : ℕ) (p : ℝ)
    (rate : 100*((9/40:ℝ)/s) ≤ 1) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    let H := senderSet T E I s
    let L := lowExterior T E I s
    let μ := product (senderLaw T E I s p rate hp hp1)
    let Δ := ((s-1:ℕ):ℝ)*r-L.card
    let m := μ.expect (markCount H)
    let v := fun w ↦ ((s-1:ℕ):ℝ)*r-((exterior H L w).card:ℝ)
    μ.expect v = Δ-m ∧ μ.expect (fun w ↦ (v w)^2) ≤ (Δ-m)^2+m := by
  intro H L μ Δ m v
  have point (w) : v w = Δ-markCount H w := by
    unfold v Δ
    rw [sampled_exterior_order]
    ring
  have var : μ.expect (fun w ↦ (markCount H w-m)^2) ≤ m :=
    mark_count_variance_le_mean (targetGraph T.color T.target) id (senderKind T E I s)
      ((9/40:ℝ)/s) p (by positivity) rate hp hp1 H
  constructor
  · have f : v = fun w ↦ Δ+markCount H w*(-1) := by funext w; rw [point]; ring
    change μ.expect v = Δ-m
    rw [f,Law.expect_add,Law.expect_const,Law.expect_mul_const]
    change Δ + m*(-1) = Δ-m
    ring
  · have f (w) : (v w)^2 = (markCount H w-m)^2 +
        (markCount H w*(2*(m-Δ)) + (Δ^2-m^2)) := by rw [point]; ring
    change μ.expect (fun w ↦ (v w)^2) ≤ (Δ-m)^2+m
    simp_rw [f]
    rw [Law.expect_add,Law.expect_add,Law.expect_const,Law.expect_mul_const]
    change _ + (m*(2*(m-Δ)) + (Δ^2-m^2)) ≤ _
    linarith only [var]

/-- For the thinned trial on the original graph, an upper bound on the
probability of each output gives a bound on all representative repair edges. -/
theorem sampled_representative_cost {E : Finset V} {e n : ℕ} {α β M : ℝ}
    (S : WidthIntegral.Selection (ordinaryLists T E) (rowDeficit T E) (rowIncidence T E) e n α β M)
    (hr : 0 < r) (X : ℝ) (lo : 0 ≤ X) (hi : X < 1120) (width : 2*β*S.w ≤ X)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    let I := S.retained
    let C := rowList T E
    let G := targetGraph T.color T.target
    let H := senderSet T E I S.s
    let U := uniqueGroup T E I S.s
    let L := lowExterior T E I S.s
    let μ := product (senderLaw T E I S.s p (retry_rate_of_scale S.scale_lo) hp hp1)
    let j := representativeFactor X
    μ.expect (fun w ↦ ((edges G I C H U L w).card:ℝ)) ≤
      (∑ i ∈ I, (j/r)*(U i).card*μ.expect
        (fun w ↦ ∑ y ∈ exterior H L w, SameRowConflicts.degree G (C i) y)) +
      (j/r)^2 * ∑ q ∈ rowPairs I,
        ((U q.1).card:ℝ)*(U q.2).card*((RepresentativeCut.cut G (C q.1) (C q.2)).card:ℝ) := by
  apply expected_edges
  · exact fun _ _ ↦ filter_subset ..
  · exact fun _ _ _ _ h ↦ disjoint_unique_groups T _ _ _ h
  · exact disjoint_left.mpr fun v hv hh ↦ (mem_sdiff.mp hh).2 hv
  · exact_mod_cast hr
  · exact representativeFactor_one lo hi
  · exact fun _ _ _ hv z _ ↦ sender_atom_bound T S hr X lo hi width p _ hp hp1 hv z
  · exact fun _ _ _ hv ↦ (unique_destination T hv).2.le

/-- These are conclusions about the actual law, including the signed shortage
variable for its sampled vertex set. -/
structure SamplingBounds (E : Finset V) (I : Finset ℕ) (s : ℕ) (loss : ℝ) : Prop where
  trial : ∃ (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (rate : 100*((9/40:ℝ)/s) ≤ 1),
    let H := senderSet T E I s
    let L := lowExterior T E I s
    let μ := product (senderLaw T E I s p rate hp.le hp1)
    let Δ := ((s-1:ℕ):ℝ)*r-L.card
    let m := μ.expect (markCount H)
    let v := fun w ↦ ((s-1:ℕ):ℝ)*r-((exterior H L w).card:ℝ)
    m = min (∑ y ∈ H, senderEligibility T E I s y) Δ ∧
      0 ≤ Δ-m ∧ Δ-m ≤ loss ∧ (3/20:ℝ)*r-loss < m ∧ m ≤ (s:ℝ)*r ∧
      μ.expect v = Δ-m ∧ μ.expect (fun w ↦ (v w)^2) ≤ (Δ-m)^2+m

theorem sampling_bounds (prep : Prepared T) (hr : 3 ≤ r) (no : ¬Witness T.color)
    (order : Fintype.card V = r^2+1) {E : Finset V} {e n : ℕ} {α β M Y b : ℝ}
    (lists : ListBounds (targetGraph T.color T.target) T.row univ (live T)
      (range r) (qualifying T) E r)
    (S : WidthIntegral.Selection (ordinaryLists T E) (rowDeficit T E) (rowIncidence T E) e n α β M)
    (band : RetainedWidth.Band Y b α β) (slots : e+(ordinaryLists T E).card = r)
    (shortage : (3/20:ℝ)*r < ((S.s-1:ℕ):ℝ)*r-((lowExterior T E S.retained S.s).card:ℝ)) :
    SamplingBounds T E S.retained S.s ((501/1000:ℝ)*(4*β^2*S.w*(1-S.w)/S.s)*r) := by
  let I := S.retained
  let s := S.s
  let H := senderSet T E I s
  let L := lowExterior T E I s
  let Δ := ((s-1:ℕ):ℝ)*r-L.card
  let A := ∑ y ∈ H, senderEligibility T E I s y
  let p := min 1 (Δ/A)
  obtain ⟨_,hp,h1,hmin,under,lossBound,low,high⟩ := eligible_thinning T prep hr no order lists S band slots shortage
  have hp' : 0 < p := hp
  have h1' : p ≤ 1 := h1
  let rate := retry_rate_of_scale S.scale_lo
  let μ := product (senderLaw T E I s p rate hp'.le h1')
  let m := μ.expect (markCount H)
  let v := fun w ↦ ((s-1:ℕ):ℝ)*r-((exterior H L w).card:ℝ)
  have mean : m = p*A := by
    change (product _).expect (fun w ↦ ∑ y ∈ H, marked (w y)) = p*A
    rw [Law.expect_sum]
    simp_rw [expect_coord,sender_mark_mean]
    unfold A
    rw [mul_sum]
    exact sum_congr rfl fun _ hy ↦ by rw [ite_eq_left hy]
  refine ⟨p,hp',h1',rate,?_⟩
  let loss := (501/1000:ℝ)*(4*β^2*S.w*(1-S.w)/S.s)*r
  change m = min A Δ ∧ 0 ≤ Δ-m ∧ Δ-m ≤ loss ∧ (3/20:ℝ)*r-loss < m ∧
    m ≤ (s:ℝ)*r ∧ μ.expect v = Δ-m ∧ μ.expect (fun w ↦ (v w)^2) ≤ (Δ-m)^2+m
  refine ⟨mean.trans hmin,by rw [mean]; exact under,by rw [mean]; exact lossBound,by rw [mean]; exact low,by rw [mean]; exact high,exterior_shortage_moments T E I s p rate hp'.le h1'⟩

/-- The shortage, the width and the cardinality moments concern the same
selection, starting with any original coloring at the working cutoff. -/
theorem witness_or_sender_sample (color : {e : Sym2 V // ¬e.IsDiag} → Fin r)
    (hr : 15*2^140 ≤ r) (order : Fintype.card V = r^2+1) :
    Witness color ∨ ∃ T : Trace V r, T.color=color ∧ Prepared T ∧
      ∃ E : Finset V, ListBounds (targetGraph T.color T.target) T.row univ (live T)
        (range r) (qualifying T) E r ∧
      ∃ b α β, RetainedWidth.Band (2-firstRate T/2-(199/400)*secondRate T) b α β ∧
      ∃ S : WidthIntegral.Selection (ordinaryLists T E) (rowDeficit T E) (rowIncidence T E)
          (range r \ ordinaryLists T E).card (omittedCount T E) α β
          ((2:ℝ)^((144-b)/4) / ((16:ℝ)/15)^(1/4:ℝ)),
        (2:ℝ)^b*(S.s:ℝ)^4 < r ∧
        (3/20:ℝ)*r < ((S.s-1:ℕ):ℝ)*r-((lowExterior T E S.retained S.s).card:ℝ) ∧
        SamplingBounds T E S.retained S.s ((501/1000:ℝ)*(4*β^2*S.w*(1-S.w)/S.s)*r) := by
  by_cases yes : Witness color
  · exact Or.inl yes
  obtain ⟨T,eq,prep,E,lists,b,α,β,band,S,_,scale,short⟩ :=
    (witness_or_exterior_shortage color hr order).resolve_left yes
  have sub : ordinaryLists T E ⊆ range r := fun _ hi ↦
    (mem_sdiff.mp (mem_sdiff.mp (mem_inter.mp hi).1).1).1
  have slots := card_sdiff_add_card_eq_card sub
  rw [card_range] at slots
  exact Or.inr ⟨T,eq,prep,E,lists,b,α,β,band,S,scale,short,
    sampling_bounds T prep (by omega) (eq ▸ yes) order lists S band slots short⟩

end
end Erdos617.ColoredLists
