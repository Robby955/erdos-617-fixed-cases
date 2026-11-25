import TwoOversamplingPasses

/-! The one-row cut bounds the actual target edges from an individual retained
clique to the sampled exterior, with no quadratic charge for a second row. -/

namespace Erdos617.ColoredLists

open Finset PruningOverlap PackingLists FiniteLaw MarkedSender RepresentativeRepairs
open scoped Classical
noncomputable section
local instance (I : Finset ℕ) : DecidableEq I := Classical.decEq _
variable {V : Type*} {r : ℕ} [Fintype V] (T : Trace V r)

/-- The single-row cut in the manuscript's normalized units. P can be the
second-pass value of normalizedRepairBound proved on these same rows. -/
theorem normalized_one_row_cut (prep : Prepared T) (hr : 2 ≤ r) (no : ¬Witness T.color)
    {E : Finset V} {e t : ℕ} {α β M Y ex : ℝ}
    (lists : ListBounds (targetGraph T.color T.target) T.row univ (live T) (range r) (qualifying T) E r)
    (S : WidthIntegral.Selection (ordinaryLists T E) (rowDeficit T E) (rowIncidence T E) e t α β M)
    (band : RetainedWidth.Band Y ex α β) (slots : e+(ordinaryLists T E).card=r)
    (scale : (2:ℝ)^ex*(S.s:ℝ)^4 < r) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (X P : ℝ) (x0 : 0 ≤ X) (x1 : X < 1120) (defi : 2*β*S.w ≤ X) (i : ℕ) (hi : i ∈ S.retained) :
    let I := S.retained
    let s := S.s
    let C := rowList T E
    let G := targetGraph T.color T.target
    let H := senderSet T E I s
    let L := lowExterior T E I s
    let μ := senderLaw T E I s p (retry_rate_of_scale S.scale_lo) hp hp1
    let budget := sampleRepairBudget G I C H (uniqueGroup T E I s) L s r μ (representativeFactor X)
    let m := (product μ).expect (markCount H)
    let u := ((s-1:ℕ):ℝ)*r-L.card-m
    let g := X/(9/40)
    let unit := ((9/40:ℝ)/s)*r
    let l := u/unit
    let η := 1/((2:ℝ)^ex*(9/40)^2)
    0 ≤ u → budget ≤ P*unit^2 →
      (product μ).expect (fun w ↦ rowToExterior T E (exterior H L w) i) ≤
        (P+g*l+l^2/2+η*(1/2+1/(2*1120)))*unit^2 := by
  intro I s C G H L μ budget m u g unit l η u0 base
  have rn : 0 < r := by omega
  have sn : 0 < S.s := by have := S.scale_lo; omega
  let _ : NeZero (30*S.s*r) := ⟨by positivity⟩
  have rp : (0:ℝ)<r := by exact_mod_cast rn
  have sp : (0:ℝ)<s := by exact_mod_cast sn
  have slo : (1120:ℝ) ≤ s := by exact_mod_cast S.scale_lo
  have up : 0 < unit := by dsimp [unit]; positivity
  have ss : S.s-1+1=S.s := by omega
  have pairs : rowPairs {i} = ∅ := by
    ext a
    simp only [rowPairs,mem_filter,mem_product,mem_singleton,notMem_empty,iff_false]
    rintro ⟨⟨h₁,h₂⟩,lt⟩
    rw [h₁,h₂] at lt
    exact lt_irrefl _ lt
  have fixed := expected_fixed_cut T S prep hr no lists band slots {i}
    (singleton_subset_iff.mpr hi) p hp hp1
  dsimp only at fixed
  simp only [pairs,sum_empty,sum_singleton,add_zero,card_singleton,ss] at fixed
  let ν := product fun _ : I ↦ ArcRepair.starts V (30*s*r)
  let repairs := (product μ).expect (fun w ↦ ν.expect fun z ↦ ((samplePairs T E I s w z).card:ℝ))
  let cut := (product μ).expect (fun w ↦ rowToExterior T E (exterior H L w) i)
  let d := (r:ℝ)-(C i).card
  change 2*cut ≤ 2*repairs+(r*s*((s:ℝ)-1)+d^2-d^2)+2*u*d+u^2+m-u at fixed
  have paid : repairs ≤ budget := sampled_union_repair_cost T S rn X x0 x1 defi p hp hp1
  have dcap : d ≤ g*unit := by
    have δ := (le_div_iff₀ sp).mpr (show rowDeficit T E i*(s:ℝ) ≤ X by
      simpa [mul_comm] using (S.deficit i hi).trans defi)
    have raw : d = rowDeficit T E i*r := by dsimp [d,C,rowDeficit]; field_simp
    rw [raw]
    exact (mul_le_mul_of_nonneg_right δ rp.le).trans_eq (by dsimp [g,unit]; ring)
  have hlu : ((s-1:ℕ):ℝ) ≤ s := by exact_mod_cast Nat.sub_le s 1
  have mcap : m ≤ r*(s:ℝ)^2/1120 := by
    change 0 ≤ ((s-1:ℕ):ℝ)*r-L.card-m at u0
    nlinarith only [u0,Nat.cast_nonneg (α:=ℝ) L.card,mul_le_mul_of_nonneg_right hlu rp.le,
      mul_nonneg (sub_nonneg.mpr slo) (mul_nonneg sp.le rp.le)]
  have err : (r:ℝ)*(s:ℝ)^2 ≤ η*unit^2 := oversample_scale_error rp sp (by positivity) scale.le
  have lead : r*s*((s:ℝ)-1) ≤ r*(s:ℝ)^2 := by nlinarith only [mul_nonneg rp.le sp.le]
  have surplus := mul_le_mul_of_nonneg_left dcap u0
  have scale_l : l*unit = u := div_mul_cancel₀ _ up.ne'
  change cut ≤ _
  nlinarith only [fixed,paid,base,mcap,err,lead,surplus,u0,
    congrArg (fun a : ℝ ↦ a^2) scale_l,congrArg (fun a : ℝ ↦ g*unit*a) scale_l]

end
end Erdos617.ColoredLists
