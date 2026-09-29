import ExactValue.Regularization
import ExactValue.Frames
import ExactValue.HardObjective
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

open scoped InnerProductSpace

set_option autoImplicit false

namespace ExactValue

noncomputable section

theorem embeddedObjective_eq_regularized {m d : ℕ} (β ρ η r : ℝ)
    (U : Fin m → Euclid d) :
    embeddedObjective β ρ η r U = regularized (embeddedCore (β * ρ / 8) ρ U) β η r := rfl

theorem embeddedObjective_strongConvex {m d : ℕ} (hm : 0 < m) {β ρ η r : ℝ}
    (hβ : 0 ≤ β) (hρ : 0 < ρ) (hr : 0 ≤ r) (U : Fin m → Euclid d) :
    StrongConvexOn Set.univ η (embeddedObjective β ρ η r U) := by
  rw [embeddedObjective_eq_regularized]
  exact regularized_strongConvex (embeddedCore_convex hm (by positivity) hρ U) hβ hr

theorem embeddedObjective_contDiff {m d : ℕ} (hm : 0 < m) {β ρ η r : ℝ}
    (hρ : 0 < ρ) (hr : 0 ≤ r) (U : Fin m → Euclid d) :
    ContDiff ℝ 1 (embeddedObjective β ρ η r U) := by
  rw [embeddedObjective_eq_regularized]
  exact regularized_contDiff (embeddedCore_contDiff hm hρ _ U) hr

def embeddedGradient {m d : ℕ} (hm : 0 < m) (β ρ η r : ℝ)
    (hr : 0 ≤ r) (U : Fin m → Euclid d) : Euclid d → Euclid d :=
  regularizedGradient (embeddedCoreGradient hm (β * ρ / 8) ρ U) β η r hr

theorem embeddedObjective_hasFDerivAt {m d : ℕ} (hm : 0 < m) {β ρ η r : ℝ}
    (hρ : 0 < ρ) (hr : 0 ≤ r) (U : Fin m → Euclid d) (x : Euclid d) :
    HasFDerivAt (embeddedObjective β ρ η r U) (innerSL ℝ (embeddedGradient hm β ρ η r hr U x)) x := by
  rw [embeddedObjective_eq_regularized]
  exact regularized_hasFDerivAt hr x (embeddedCore_hasFDerivAt hm hρ _ U x)

theorem embeddedGradient_lipschitz_bound {m d : ℕ} (hm : 0 < m) {β ρ η r : ℝ}
    (hβ : 0 ≤ β) (hρ : 0 < ρ) (hη : 0 ≤ η) (hr : 0 ≤ r)
    {U : Fin m → Euclid d} (hU : Orthonormal ℝ U) (x y : Euclid d) :
    ‖embeddedGradient hm β ρ η r hr U x - embeddedGradient hm β ρ η r hr U y‖ ≤
      (β / 2 + η) * ‖x - y‖ := by
  have hg := regularizedGradient_bound hr hβ hη
    (embeddedCore_gradient_lipschitz hm (show 0 ≤ β * ρ / 8 by positivity) hρ hU) x y
  have heq : β * ρ / 8 * (2 / ρ) + β / 4 + η = β / 2 + η := by
    field_simp
    ring
  simpa only [embeddedGradient, heq] using hg

theorem embeddedObjective_exists_unique_min {m d : ℕ} (hm : 0 < m) {β ρ η r : ℝ}
    (hβ : 0 < β) (hρ : 0 < ρ) (hη : 0 < η) (hr : 0 ≤ r)
    {U : Fin m → Euclid d} (hU : Orthonormal ℝ U) :
    ∃ x : Euclid d, (∀ y, embeddedObjective β ρ η r U x ≤ embeddedObjective β ρ η r U y) ∧
      ‖x‖ ≤ r + ρ ∧
      ∀ z, (∀ y, embeddedObjective β ρ η r U z ≤ embeddedObjective β ρ η r U y) → z = x := by
  rw [embeddedObjective_eq_regularized]
  have hA : 0 ≤ β * ρ / 8 := by positivity
  have heq : 8 * (β * ρ / 8) / β = ρ := by field_simp
  simpa only [heq] using regularized_exists_unique_min
    (embeddedCore_contDiff hm hρ (β * ρ / 8) U).continuous
    (embeddedCore_convex hm hA hρ U) hβ hη hr hA
    (embeddedCore_value_bound hm hA hρ hU)

theorem exists_unit_frame_kernel {m d : ℕ} (hmd : m < d) (U : Fin m → Euclid d) :
    ∃ v : Euclid d, ‖v‖ = 1 ∧ frameRead U v = 0 := by
  have hk : LinearMap.ker (frameRead U).toLinearMap ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt
    (by simpa only [Euclid, finrank_euclideanSpace_fin] using hmd)
  obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff _).mp hk
  have hwk : frameRead U w = 0 := hw
  have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  refine ⟨(1 / ‖w‖) • w, ?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), div_mul_cancel₀ _ hn.ne']
  · rw [map_smul, hwk, smul_zero]

theorem embeddedObjective_kernel_line {m d : ℕ} {β ρ η r : ℝ}
    (U : Fin m → Euclid d) {v : Euclid d} (hv : ‖v‖ = 1) (hk : frameRead U v = 0)
    {t : ℝ} (ht : |t| ≤ r) :
    embeddedObjective β ρ η r U (t • v) =
      (β * ρ / 8) * euclideanMoreau ρ (0 : Euclid m) + η / 2 * t ^ 2 := by
  rw [embeddedObjective_eq_regularized]
  simp only [regularized, embeddedCore, map_smul, hk, smul_zero, norm_smul,
    Real.norm_eq_abs, hv, mul_one, max_eq_right (sub_nonpos.mpr ht), zero_pow (by decide : 2 ≠ 0),
    mul_zero, add_zero, sq_abs]

theorem embeddedObjective_modulus_le {m d : ℕ} (hmd : m < d) {β ρ η r μ : ℝ}
    (hr : 0 < r) (U : Fin m → Euclid d)
    (hμ : StrongConvexOn Set.univ μ (embeddedObjective β ρ η r U)) : μ ≤ η := by
  obtain ⟨v, hv, hk⟩ := exists_unit_frame_kernel hmd U
  have hc := (strongConvexOn_iff_convex.mp hμ).2
    (Set.mem_univ (r • v)) (Set.mem_univ ((-r) • v))
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (1 : ℝ) / 2 + 1 / 2 = 1 by norm_num)
  have hmid : (1 / 2 : ℝ) • (r • v) + (1 / 2 : ℝ) • ((-r) • v) = 0 := by
    rw [← smul_add, ← add_smul]
    simp
  have hp := embeddedObjective_kernel_line (β := β) (ρ := ρ) (η := η)
    U hv hk (t := r) (le_of_eq (abs_of_pos hr))
  have hn := embeddedObjective_kernel_line (β := β) (ρ := ρ) (η := η) U hv hk (t := -r)
    (by rw [abs_neg, abs_of_pos hr])
  have hz := embeddedObjective_kernel_line (β := β) (ρ := ρ) (η := η)
    U hv hk (t := 0) (by simpa using hr.le)
  simp only [zero_smul, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero] at hz
  rw [hmid] at hc
  dsimp only at hc
  rw [hp, hn, hz] at hc
  simp only [norm_smul, Real.norm_eq_abs, hv, mul_one, norm_zero,
    zero_pow (by decide : 2 ≠ 0), mul_zero, sub_zero, smul_eq_mul, sq_abs, neg_sq] at hc
  nlinarith [sq_pos_of_pos hr]

end

end ExactValue
