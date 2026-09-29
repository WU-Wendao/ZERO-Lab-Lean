import ExactValue.Smoothness
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.Calculus.ContDiff.Operations

open Finset
open scoped InnerProductSpace

set_option autoImplicit false

namespace ExactValue

noncomputable section

def frameRead {m d : ℕ} (U : Fin m → Euclid d) : Euclid d →L[ℝ] Euclid m :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => innerSL ℝ (U i)))

theorem frameRead_apply {m d : ℕ} (U : Fin m → Euclid d) (x : Euclid d) (i : Fin m) :
    frameRead U x i = ⟪U i, x⟫_ℝ := rfl

def frameWrite {m d : ℕ} (U : Fin m → Euclid d) : Euclid m →L[ℝ] Euclid d :=
  ∑ i, (EuclideanSpace.proj i).smulRight (U i)

theorem frameWrite_apply {m d : ℕ} (U : Fin m → Euclid d) (y : Euclid m) :
    frameWrite U y = ∑ i, y i • U i := by simp [frameWrite]

theorem frameWrite_norm {m d : ℕ} {U : Fin m → Euclid d}
    (hU : Orthonormal ℝ U) (y : Euclid m) : ‖frameWrite U y‖ = ‖y‖ := by
  have hi := hU.inner_sum (fun i => y i) (fun i => y i) Finset.univ
  simp only [RCLike.conj_to_real, ← sq] at hi
  rw [← frameWrite_apply, real_inner_self_eq_norm_sq, ← euclidean_norm_sq] at hi
  nlinarith [norm_nonneg (frameWrite U y), norm_nonneg y]

theorem frameRead_norm {m d : ℕ} {U : Fin m → Euclid d}
    (hU : Orthonormal ℝ U) (x : Euclid d) : ‖frameRead U x‖ ≤ ‖x‖ := by
  have hi := hU.sum_inner_products_le (s := Finset.univ) x
  simp only [Real.norm_eq_abs, sq_abs] at hi
  have hn := euclidean_norm_sq (frameRead U x)
  simp only [frameRead_apply] at hn
  nlinarith [norm_nonneg (frameRead U x), norm_nonneg x]

theorem frameRead_write {m d : ℕ} {U : Fin m → Euclid d}
    (hU : Orthonormal ℝ U) (y : Euclid m) : frameRead U (frameWrite U y) = y := by
  ext i
  rw [frameRead_apply, frameWrite_apply]
  exact hU.inner_right_fintype (fun j => y j) i

theorem frame_inner {m d : ℕ} (U : Fin m → Euclid d) (y : Euclid m) (x : Euclid d) :
    ⟪frameWrite U y, x⟫_ℝ = ⟪y, frameRead U x⟫_ℝ := by
  rw [frameWrite_apply, sum_inner, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp only [real_inner_smul_left, frameRead_apply]
  exact mul_comm _ _

theorem moreau_value_bound {m : ℕ} (hm : 0 < m) {ρ : ℝ} (hρ : 0 < ρ)
    (x y : Euclid m) : euclideanMoreau ρ x - euclideanMoreau ρ y ≤ ‖x - y‖ := by
  obtain ⟨p, hp⟩ := exists_dualMax hm ρ (fun i => x i)
  obtain ⟨q, hq⟩ := exists_dualMax hm ρ (fun i => y i)
  have hmax := hq.2 p hp.1
  have hchange := dualObjective_change_input ρ (fun i => y i) (fun i => x i) p
  have hsum : (∑ i, p i * (x i - y i)) ≤ ‖x - y‖ := by
    calc
      _ ≤ ∑ i, p i * ‖x - y‖ := by
        apply Finset.sum_le_sum
        intro i _
        apply mul_le_mul_of_nonneg_left _ (simplex_coord_nonneg hp.1 i)
        exact (le_abs_self _).trans (PiLp.norm_apply_le (x - y) i)
      _ = ‖x - y‖ := by rw [← Finset.sum_mul, hp.1.2, one_mul]
  dsimp [euclideanMoreau]
  rw [moreau_eq_dual hm hρ, moreau_eq_dual hm hρ,
    dualValue_eq_of_max hp, dualValue_eq_of_max hq]
  linarith

def embeddedCore {m d : ℕ} (A ρ : ℝ) (U : Fin m → Euclid d) (x : Euclid d) : ℝ :=
  A * euclideanMoreau ρ (frameRead U x)

def embeddedCoreGradient {m d : ℕ} (hm : 0 < m) (A ρ : ℝ)
    (U : Fin m → Euclid d) (x : Euclid d) : Euclid d :=
  A • frameWrite U (chainGradient hm ρ (frameRead U x))

theorem embeddedCore_contDiff {m d : ℕ} (hm : 0 < m) {ρ : ℝ} (hρ : 0 < ρ)
    (A : ℝ) (U : Fin m → Euclid d) : ContDiff ℝ 1 (embeddedCore A ρ U) := by
  exact contDiff_const.mul ((moreau_contDiff_one hm hρ).comp (frameRead U).contDiff)

theorem embeddedCore_convex {m d : ℕ} (hm : 0 < m) {A ρ : ℝ}
    (hA : 0 ≤ A) (hρ : 0 < ρ) (U : Fin m → Euclid d) :
    ConvexOn ℝ Set.univ (embeddedCore A ρ U) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have hc := (moreau_convex hm hρ).2 (Set.mem_univ (frameRead U x))
    (Set.mem_univ (frameRead U y)) ha hb hab
  dsimp [embeddedCore]
  simp only [map_add, map_smul, smul_eq_mul]
  simpa only [smul_eq_mul, mul_add, mul_left_comm] using mul_le_mul_of_nonneg_left hc hA

theorem embeddedCore_hasFDerivAt {m d : ℕ} (hm : 0 < m) {ρ : ℝ} (hρ : 0 < ρ)
    (A : ℝ) (U : Fin m → Euclid d) (x : Euclid d) :
    HasFDerivAt (embeddedCore A ρ U) (innerSL ℝ (embeddedCoreGradient hm A ρ U x)) x := by
  have hc := (moreau_hasFDerivAt hm hρ (frameRead U x)
    (chainGradient_spec hm ρ (frameRead U x))).comp x (frameRead U).hasFDerivAt
  have hh := hc.const_mul A
  convert hh using 1
  ext z
  change ⟪A • frameWrite U (chainGradient hm ρ (frameRead U x)), z⟫_ℝ =
    A * gradientLinear (fun i => chainGradient hm ρ (frameRead U x) i) (frameRead U z)
  rw [real_inner_smul_left, frame_inner, gradientLinear_eq_innerSL]
  rfl

theorem embeddedCore_gradient_bound {m d : ℕ} (hm : 0 < m) {A : ℝ} (hA : 0 ≤ A)
    (ρ : ℝ) {U : Fin m → Euclid d} (hU : Orthonormal ℝ U) (x : Euclid d) :
    ‖embeddedCoreGradient hm A ρ U x‖ ≤ A := by
  have hg := gradient_norm_le_one (chainGradient_spec hm ρ (frameRead U x)).1
  change ‖chainGradient hm ρ (frameRead U x)‖ ≤ 1 at hg
  rw [embeddedCoreGradient, norm_smul, Real.norm_eq_abs, abs_of_nonneg hA, frameWrite_norm hU]
  nlinarith

theorem embeddedCore_gradient_lipschitz {m d : ℕ} (hm : 0 < m) {A ρ : ℝ}
    (hA : 0 ≤ A) (hρ : 0 < ρ) {U : Fin m → Euclid d} (hU : Orthonormal ℝ U)
    (x y : Euclid d) :
    ‖embeddedCoreGradient hm A ρ U x - embeddedCoreGradient hm A ρ U y‖ ≤
      (A * (2 / ρ)) * ‖x - y‖ := by
  have hg := (chainGradient_lipschitz hm hρ).norm_sub_le (frameRead U x) (frameRead U y)
  have hr := frameRead_norm hU (x - y)
  rw [map_sub] at hr
  simp only [NNReal.coe_mk] at hg
  simp only [embeddedCoreGradient, ← smul_sub, ← map_sub, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg hA, frameWrite_norm hU]
  have hc : 0 ≤ 2 / ρ := by positivity
  nlinarith [mul_le_mul_of_nonneg_left (hg.trans (mul_le_mul_of_nonneg_left hr hc)) hA]

theorem embeddedCore_value_bound {m d : ℕ} (hm : 0 < m) {A ρ : ℝ}
    (hA : 0 ≤ A) (hρ : 0 < ρ) {U : Fin m → Euclid d} (hU : Orthonormal ℝ U)
    (x y : Euclid d) : embeddedCore A ρ U x - embeddedCore A ρ U y ≤ A * ‖x - y‖ := by
  have hc := moreau_value_bound hm hρ (frameRead U x) (frameRead U y)
  have hr := frameRead_norm hU (x - y)
  rw [map_sub] at hr
  simpa [embeddedCore, mul_sub] using mul_le_mul_of_nonneg_left (hc.trans hr) hA

end

end ExactValue
