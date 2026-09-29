import ExactValue.Moreau
import ExactValue.Bounds
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-! The Moreau envelope is differentiable on Euclidean space. -/

open Finset Filter Asymptotics
open scoped Topology InnerProductSpace

set_option autoImplicit false

namespace ExactValue

noncomputable section

abbrev Euclid (m : ℕ) := EuclideanSpace ℝ (Fin m)

def euclideanMoreau {m : ℕ} (ρ : ℝ) (y : Euclid m) : ℝ :=
  moreauValue ρ (fun i => y i)

def gradientLinear {m : ℕ} (p : Vec m) : Euclid m →L[ℝ] ℝ :=
  ∑ i, p i • EuclideanSpace.proj i

theorem gradientLinear_apply {m : ℕ} (p : Vec m) (h : Euclid m) :
    gradientLinear p h = ∑ i, p i * h i := by
  simp [gradientLinear]

theorem euclidean_norm_sq {m : ℕ} (h : Euclid m) : ‖h‖ ^ 2 = ∑ i, (h i) ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  simp [Real.norm_eq_abs, sq_abs]

theorem moreau_remainder_norm {m : ℕ} (hm : 0 < m) {ρ : ℝ} (hρ : 0 < ρ)
    (y : Euclid m) {p : Vec m} (hp : IsDualMax ρ (fun i => y i) p) (h : Euclid m) :
    ‖euclideanMoreau ρ (y + h) - euclideanMoreau ρ y - gradientLinear p h‖ ≤
      ‖h‖ ^ 2 / ρ := by
  have hmodel := moreau_quadratic_model hm hρ hp (fun i => (y + h) i)
  simp only [PiLp.add_apply, add_sub_cancel_left] at hmodel
  rw [euclideanMoreau, euclideanMoreau, gradientLinear_apply, Real.norm_eq_abs]
  simp only [PiLp.add_apply]
  rw [abs_of_nonneg hmodel.1, euclidean_norm_sq]
  exact hmodel.2

theorem moreau_hasFDerivAt {m : ℕ} (hm : 0 < m) {ρ : ℝ} (hρ : 0 < ρ)
    (y : Euclid m) {p : Vec m} (hp : IsDualMax ρ (fun i => y i) p) :
    HasFDerivAt (euclideanMoreau ρ) (gradientLinear p) y := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  refine (Asymptotics.IsBigO.of_bound (1 / ρ) ?_).trans_isLittleO
    (Asymptotics.isLittleO_norm_pow_id (n := 2) (by norm_num))
  apply Filter.Eventually.of_forall
  intro h
  have hb := moreau_remainder_norm hm hρ y hp h
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖h‖), one_div,
    div_eq_mul_inv, mul_comm, mul_one, one_mul] using hb

theorem moreau_differentiable {m : ℕ} (hm : 0 < m) {ρ : ℝ} (hρ : 0 < ρ) :
    Differentiable ℝ (euclideanMoreau (m := m) ρ) := by
  intro y
  obtain ⟨p, hp⟩ := exists_dualMax hm ρ (fun i => y i)
  exact (moreau_hasFDerivAt hm hρ y hp).differentiableAt

/-- The simplex constraint bounds the Euclidean norm of the gradient candidate. -/
theorem gradient_norm_le_one {m : ℕ} {p : Vec m} (hp : p ∈ simplex m) :
    ‖((WithLp.equiv 2 (Fin m → ℝ)).symm p : Euclid m)‖ ≤ 1 := by
  have hs := simplex_sq_sum_le_one hp
  have hn := euclidean_norm_sq ((WithLp.equiv 2 (Fin m → ℝ)).symm p)
  simp only [WithLp.equiv_symm_pi_apply] at hn
  nlinarith [norm_nonneg ((WithLp.equiv 2 (Fin m → ℝ)).symm p : Euclid m)]

theorem dualMax_lipschitz {m : ℕ} {ρ : ℝ} (hρ : 0 < ρ)
    (y z : Euclid m) {p q : Vec m}
    (hp : IsDualMax ρ (fun i => y i) p) (hq : IsDualMax ρ (fun i => z i) q) :
    ‖((WithLp.equiv 2 (Fin m → ℝ)).symm q : Euclid m) -
        (WithLp.equiv 2 (Fin m → ℝ)).symm p‖ ≤ (2 / ρ) * ‖z - y‖ := by
  let P : Euclid m := (WithLp.equiv 2 (Fin m → ℝ)).symm p
  let Q : Euclid m := (WithLp.equiv 2 (Fin m → ℝ)).symm q
  have h1 := dualMax_strong hρ hp hq.1
  have h2 := dualMax_strong hρ hq hp.1
  rw [dualObjective_change_input ρ (fun i => y i) (fun i => z i) p,
    dualObjective_change_input ρ (fun i => y i) (fun i => z i) q] at h2
  have hrev : (∑ i, (p i - q i) ^ 2) = ∑ i, (q i - p i) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hrev] at h2
  have hlin : (∑ i, q i * (z i - y i)) - (∑ i, p i * (z i - y i)) =
      ∑ i, (q i - p i) * (z i - y i) := by
    simp only [sub_mul, Finset.sum_sub_distrib]
  have hstrong : ρ / 2 * (∑ i, (q i - p i) ^ 2) ≤
      ∑ i, (q i - p i) * (z i - y i) := by rw [← hlin]; linarith
  have hnorm : ‖Q - P‖ ^ 2 = ∑ i, (q i - p i) ^ 2 := by
    simpa [P, Q] using euclidean_norm_sq (Q - P)
  have hinner : ⟪Q - P, z - y⟫_ℝ =
      ∑ i, (q i - p i) * (z i - y i) := by
    simp [PiLp.inner_apply, P, Q, mul_comm]
  rw [← hnorm, ← hinner] at hstrong
  have hcs := real_inner_le_norm (Q - P) (z - y)
  change ‖Q - P‖ ≤ 2 / ρ * ‖z - y‖
  have heq : (2 / ρ * ‖z - y‖) * ρ = 2 * ‖z - y‖ := by field_simp
  by_cases hz : ‖Q - P‖ = 0
  · rw [hz]
    positivity
  · have hn : 0 < ‖Q - P‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    have hc : ρ / 2 * ‖Q - P‖ ≤ ‖z - y‖ := by
      apply (mul_le_mul_right hn).mp
      nlinarith [hstrong, hcs]
    nlinarith

def chainGradient {m : ℕ} (hm : 0 < m) (ρ : ℝ) (y : Euclid m) : Euclid m :=
  (WithLp.equiv 2 (Fin m → ℝ)).symm (Classical.choose (exists_dualMax hm ρ (fun i => y i)))

theorem chainGradient_spec {m : ℕ} (hm : 0 < m) (ρ : ℝ) (y : Euclid m) :
    IsDualMax ρ (fun i => y i) (fun i => chainGradient hm ρ y i) := by
  exact Classical.choose_spec (exists_dualMax hm ρ (fun i => y i))

theorem chainGradient_lipschitz {m : ℕ} (hm : 0 < m) {ρ : ℝ} (hρ : 0 < ρ) :
    LipschitzWith ⟨2 / ρ, by positivity⟩ (chainGradient hm ρ) := by
  apply LipschitzWith.of_dist_le_mul
  intro y z
  simpa [dist_eq_norm] using dualMax_lipschitz hρ z y
    (chainGradient_spec hm ρ z) (chainGradient_spec hm ρ y)

theorem gradientLinear_eq_innerSL {m : ℕ} (g : Euclid m) :
    gradientLinear (fun i => g i) = innerSL ℝ g := by
  ext h
  simp [gradientLinear_apply, PiLp.inner_apply, mul_comm]

theorem moreau_contDiff_one {m : ℕ} (hm : 0 < m) {ρ : ℝ} (hρ : 0 < ρ) :
    ContDiff ℝ 1 (euclideanMoreau (m := m) ρ) := by
  apply contDiff_one_iff_hasFDerivAt.mpr
  refine ⟨fun y => innerSL ℝ (chainGradient hm ρ y), ?_, ?_⟩
  · exact (innerSL ℝ).continuous.comp (chainGradient_lipschitz hm hρ).continuous
  · intro y
    dsimp only
    rw [← gradientLinear_eq_innerSL]
    exact moreau_hasFDerivAt hm hρ y (chainGradient_spec hm ρ y)

theorem dualObjective_affine_input {m : ℕ} (ρ a b : ℝ) (hab : a + b = 1)
    (y z p : Vec m) :
    dualObjective ρ (fun i => a * y i + b * z i) p =
      a * dualObjective ρ y p + b * dualObjective ρ z p := by
  have hb : b = 1 - a := by linarith
  subst b
  unfold dualObjective
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem moreau_convex {m : ℕ} (hm : 0 < m) {ρ : ℝ} (hρ : 0 < ρ) :
    ConvexOn ℝ Set.univ (euclideanMoreau (m := m) ρ) := by
  refine ⟨convex_univ, ?_⟩
  intro y _ z _ a b ha hb hab
  change moreauValue ρ (fun i => a * y i + b * z i) ≤
    a * moreauValue ρ (fun i => y i) + b * moreauValue ρ (fun i => z i)
  rw [moreau_eq_dual hm hρ, moreau_eq_dual hm hρ, moreau_eq_dual hm hρ]
  obtain ⟨p, hp⟩ := exists_dualMax hm ρ (fun i => a * y i + b * z i)
  obtain ⟨q, hq⟩ := exists_dualMax hm ρ (fun i => y i)
  obtain ⟨r, hr⟩ := exists_dualMax hm ρ (fun i => z i)
  rw [dualValue_eq_of_max hp, dualValue_eq_of_max hq, dualValue_eq_of_max hr,
    dualObjective_affine_input ρ a b hab]
  exact add_le_add (mul_le_mul_of_nonneg_left (hq.2 p hp.1) ha)
    (mul_le_mul_of_nonneg_left (hr.2 p hp.1) hb)

end

end ExactValue
