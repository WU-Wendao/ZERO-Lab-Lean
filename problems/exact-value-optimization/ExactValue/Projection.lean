import ExactValue.Smoothness
import Mathlib.Analysis.InnerProductSpace.Projection
import Mathlib.Topology.MetricSpace.HausdorffDistance

open Filter Asymptotics
open scoped Topology InnerProductSpace

set_option autoImplicit false

namespace ExactValue

noncomputable section

structure ClosedConvexDomain (d : ℕ) where
  carrier : Set (Euclid d)
  nonempty : carrier.Nonempty
  closed : IsClosed carrier
  convex : Convex ℝ carrier

namespace ClosedConvexDomain

variable {d : ℕ} (K : ClosedConvexDomain d)

def project (x : Euclid d) : Euclid d :=
  Classical.choose (exists_norm_eq_iInf_of_complete_convex K.nonempty K.closed.isComplete K.convex x)

theorem project_mem (x : Euclid d) : K.project x ∈ K.carrier :=
  (Classical.choose_spec
    (exists_norm_eq_iInf_of_complete_convex K.nonempty K.closed.isComplete K.convex x)).1

theorem project_min (x y : Euclid d) (hy : y ∈ K.carrier) :
    ‖x - K.project x‖ ≤ ‖x - y‖ := by
  have hp := (Classical.choose_spec
    (exists_norm_eq_iInf_of_complete_convex K.nonempty K.closed.isComplete K.convex x)).2
  change ‖x - K.project x‖ = _ at hp
  rw [hp]
  have hb : BddBelow (Set.range (fun w : K.carrier => ‖x - (w : Euclid d)‖)) :=
    ⟨0, Set.forall_mem_range.mpr (fun w => norm_nonneg (x - (w : Euclid d)))⟩
  exact ciInf_le hb ⟨y, hy⟩

theorem project_optimality (x y : Euclid d) (hy : y ∈ K.carrier) :
    ⟪x - K.project x, y - K.project x⟫_ℝ ≤ 0 := by
  have hp := (Classical.choose_spec
    (exists_norm_eq_iInf_of_complete_convex K.nonempty K.closed.isComplete K.convex x)).2
  exact (norm_eq_iInf_iff_real_inner_le_zero K.convex (K.project_mem x)).mp hp y hy

def residual (x : Euclid d) : Euclid d := x - K.project x

def halfSquaredDistance (x : Euclid d) : ℝ := ‖K.residual x‖ ^ 2 / 2

theorem residual_norm_eq_infDist (x : Euclid d) :
    ‖K.residual x‖ = Metric.infDist x K.carrier := by
  apply le_antisymm
  · apply (Metric.le_infDist K.nonempty).2
    intro y hy
    simpa [dist_eq_norm, residual] using K.project_min x y hy
  · simpa [dist_eq_norm, residual] using Metric.infDist_le_dist_of_mem (K.project_mem x)

theorem halfSquaredDistance_eq (x : Euclid d) :
    K.halfSquaredDistance x = (Metric.infDist x K.carrier) ^ 2 / 2 := by
  rw [halfSquaredDistance, K.residual_norm_eq_infDist]

theorem lower_model (x y : Euclid d) :
    K.halfSquaredDistance x + ⟪K.residual x, y - x⟫_ℝ ≤ K.halfSquaredDistance y := by
  have hi := K.project_optimality x (K.project y) (K.project_mem y)
  have hsq := sq_nonneg ‖K.residual y - K.residual x‖
  rw [norm_sub_sq_real] at hsq
  have heq : ⟪K.residual x, y - x⟫_ℝ =
      ⟪K.residual y, K.residual x⟫_ℝ - ‖K.residual x‖ ^ 2 +
        ⟪K.residual x, K.project y - K.project x⟫_ℝ := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [residual, inner_sub_left, inner_sub_right]
    simp only [real_inner_comm]
    ring
  change ⟪K.residual x, K.project y - K.project x⟫_ℝ ≤ 0 at hi
  rw [heq]
  unfold halfSquaredDistance
  nlinarith

theorem upper_model (x y : Euclid d) :
    K.halfSquaredDistance y ≤ K.halfSquaredDistance x +
      ⟪K.residual x, y - x⟫_ℝ + ‖y - x‖ ^ 2 / 2 := by
  have hp := pow_le_pow_left₀ (norm_nonneg (y - K.project y))
    (K.project_min y (K.project x) (K.project_mem x)) 2
  have heq : y - K.project x = K.residual x + (y - x) := by unfold residual; abel
  rw [heq, norm_add_sq_real] at hp
  change ‖K.residual y‖ ^ 2 ≤ _ at hp
  unfold halfSquaredDistance
  nlinarith

theorem residual_lipschitz : LipschitzWith 1 K.residual := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hx := K.project_optimality x (K.project y) (K.project_mem y)
  have hy := K.project_optimality y (K.project x) (K.project_mem x)
  have hprod : ⟪K.residual x - K.residual y, K.project x - K.project y⟫_ℝ ≥ 0 := by
    simp only [residual, inner_sub_left, inner_sub_right] at hx hy ⊢
    linarith
  have hsum : x - y = (K.residual x - K.residual y) + (K.project x - K.project y) := by
    unfold residual
    abel
  have heq := norm_add_sq_real (K.residual x - K.residual y) (K.project x - K.project y)
  rw [← hsum] at heq
  simp only [dist_eq_norm, NNReal.coe_one, one_mul]
  nlinarith [sq_nonneg ‖K.project x - K.project y‖,
    norm_nonneg (K.residual x - K.residual y), norm_nonneg (x - y)]

theorem halfSquaredDistance_hasFDerivAt (x : Euclid d) :
    HasFDerivAt K.halfSquaredDistance (innerSL ℝ (K.residual x)) x := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  refine (Asymptotics.IsBigO.of_bound (1 / 2) ?_).trans_isLittleO
    (Asymptotics.isLittleO_norm_pow_id (n := 2) (by norm_num))
  apply Filter.Eventually.of_forall
  intro h
  have hl := K.lower_model x (x + h)
  have hu := K.upper_model x (x + h)
  simp only [add_sub_cancel_left] at hl hu
  simp only [innerSL_apply, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖h‖)]
  rw [abs_of_nonneg (by linarith : 0 ≤ K.halfSquaredDistance (x + h) -
    K.halfSquaredDistance x - ⟪K.residual x, h⟫_ℝ)]
  linarith

theorem halfSquaredDistance_contDiff : ContDiff ℝ 1 K.halfSquaredDistance := by
  apply contDiff_one_iff_hasFDerivAt.mpr
  exact ⟨fun x => innerSL ℝ (K.residual x),
    (innerSL ℝ).continuous.comp K.residual_lipschitz.continuous,
    K.halfSquaredDistance_hasFDerivAt⟩

theorem halfSquaredDistance_convex : ConvexOn ℝ Set.univ K.halfSquaredDistance := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  let z := a • x + b • y
  have hx := mul_le_mul_of_nonneg_left (K.lower_model z x) ha
  have hy := mul_le_mul_of_nonneg_left (K.lower_model z y) hb
  have heq : a * ⟪K.residual z, x - z⟫_ℝ + b * ⟪K.residual z, y - z⟫_ℝ = 0 := by
    rw [← inner_smul_right, ← inner_smul_right, ← inner_add_right]
    have hid : a • (x - z) + b • (y - z) = 0 := by
      rw [smul_sub, smul_sub, sub_add_sub_comm, ← add_smul, hab, one_smul]
      exact sub_self _
    rw [hid, inner_zero_right]
  change K.halfSquaredDistance z ≤ a * K.halfSquaredDistance x + b * K.halfSquaredDistance y
  have hw : a * K.halfSquaredDistance z + b * K.halfSquaredDistance z =
      K.halfSquaredDistance z := by rw [← add_mul, hab, one_mul]
  nlinarith

end ClosedConvexDomain

end

end ExactValue
