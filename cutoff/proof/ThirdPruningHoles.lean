import Mathlib.Tactic

/-! Two estimates for the last pruning pass in the Erdős 617 cutoff argument. -/

namespace Erdos617.ThirdPruning

open Finset

/-- If the total number of points forbidden across two rows is small enough,
the two residual list sizes have product larger than the whole edge budget. -/
theorem two_list_product {L E u v a b : ℝ} (hL : 0 < L) (hE : 0 ≤ E)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (small : u + v < L - E / L)
    (ha : L - u ≤ a) (hb : L - v ≤ b) : E < a * b := by
  have pos : u + v < L := lt_of_lt_of_le small (sub_le_self _ (div_nonneg hE hL.le))
  have mul : E < (L - (u + v)) * L := (div_lt_iff₀ hL).mp (by linarith)
  calc E < (L-u)*(L-v) := by nlinarith only [mul,mul_nonneg hu hv]
       _ ≤ a*b := mul_le_mul ha hb (by linarith) (by linarith)

/-- Sum incidences of a finite family by their endpoint, bounding the
multiplicity of each endpoint before applying its weight. -/
private theorem endpoint_sum {I V : Type*} [DecidableEq V]
    (holes : Finset I) (vertices : Finset V) (endpoint : I → V) (weight : V → ℝ)
    (M : ℝ) (cover : ∀ h ∈ holes, endpoint h ∈ vertices)
    (pos : ∀ x ∈ vertices, 0 ≤ weight x)
    (cap : ∀ x ∈ vertices, ((holes.filter fun h ↦ endpoint h = x).card : ℝ) ≤ M) :
    (∑ h ∈ holes, weight (endpoint h)) ≤ M * ∑ x ∈ vertices, weight x := by
  classical
  rw [← sum_fiberwise_of_maps_to (s := holes) (t := vertices) (g := endpoint)
    cover, mul_sum]
  apply sum_le_sum
  intro x hx
  calc (∑ h ∈ holes.filter (fun h ↦ endpoint h = x), weight (endpoint h)) =
        ∑ _h ∈ holes.filter (fun h ↦ endpoint h = x), weight x :=
          sum_congr rfl fun h hh ↦ by rw [(mem_filter.mp hh).2]
       _ = _ := by simp
       _ ≤ M * weight x := mul_le_mul_of_nonneg_right (cap x hx) (pos x hx)

/-- A missing internal edge joins one removed vertex and one survivor.
Summing the lower charge on each such edge counts the two different endpoint
multiplicities separately. -/
theorem hole_charge {I V W : Type*} [DecidableEq V] [DecidableEq W]
    (holes : Finset I) (removed : Finset V) (live : Finset W)
    (src : I → V) (dst : I → W) (excess : V → ℝ) (degree : W → ℝ)
    (threshold M N : ℝ)
    (src_mem : ∀ h ∈ holes, src h ∈ removed) (dst_mem : ∀ h ∈ holes, dst h ∈ live)
    (ex_nonneg : ∀ x ∈ removed, 0 ≤ excess x) (deg_nonneg : ∀ w ∈ live, 0 ≤ degree w)
    (src_cap : ∀ x ∈ removed, ((holes.filter fun h ↦ src h = x).card : ℝ) ≤ M)
    (dst_cap : ∀ w ∈ live, ((holes.filter fun h ↦ dst h = w).card : ℝ) ≤ N)
    (per_edge : ∀ h ∈ holes, threshold ≤ excess (src h) + degree (dst h)) :
    holes.card * threshold ≤ M * ∑ x ∈ removed, excess x + N * ∑ w ∈ live, degree w := by
  classical
  have total := sum_le_sum per_edge
  rw [sum_add_distrib] at total
  simpa using total.trans (add_le_add
    (endpoint_sum holes removed src excess M src_mem ex_nonneg src_cap)
    (endpoint_sum holes live dst degree N dst_mem deg_nonneg dst_cap))

end Erdos617.ThirdPruning

#print axioms Erdos617.ThirdPruning.two_list_product
#print axioms Erdos617.ThirdPruning.hole_charge
