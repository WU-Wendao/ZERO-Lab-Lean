import ExactValue.Smoothness

open Finset
open scoped InnerProductSpace

set_option autoImplicit false

namespace ExactValue

noncomputable section

theorem maxAffine_convex {m : ℕ} (hm : 0 < m) (ρ : ℝ) :
    ConvexOn ℝ Set.univ (fun y : Euclid m => maxAffine ρ (fun i => y i)) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  apply maxAffine_le hm
  intro i
  have hx := mul_le_mul_of_nonneg_left (coord_le_maxAffine ρ (fun i => x i) i) ha
  have hy := mul_le_mul_of_nonneg_left (coord_le_maxAffine ρ (fun i => y i) i) hb
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  calc
    _ = a * x i + b * y i - (a + b) * (8 * ρ * (i.val + 1)) := by rw [hab, one_mul]
    _ = a * (x i - 8 * ρ * (i.val + 1)) + b * (y i - 8 * ρ * (i.val + 1)) := by ring
    _ ≤ _ := add_le_add hx hy

theorem maxAffine_difference_le {m : ℕ} (hm : 0 < m) (ρ : ℝ) (x y : Euclid m) :
    maxAffine ρ (fun i => x i) - maxAffine ρ (fun i => y i) ≤ ‖x - y‖ := by
  suffices maxAffine ρ (fun i => x i) ≤ maxAffine ρ (fun i => y i) + ‖x - y‖ by linarith
  apply maxAffine_le hm
  intro i
  have hc := coord_le_maxAffine ρ (fun i => y i) i
  have hn := PiLp.norm_apply_le (x - y) i
  simp only [PiLp.sub_apply, Real.norm_eq_abs] at hn
  have hv := le_abs_self (x i - y i)
  linarith

theorem maxAffine_lipschitz {m : ℕ} (hm : 0 < m) (ρ : ℝ) :
    LipschitzWith 1 (fun y : Euclid m => maxAffine ρ (fun i => y i)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul, Real.dist_eq, dist_eq_norm]
  apply abs_le.mpr
  constructor
  · have h := maxAffine_difference_le hm ρ y x
    rw [norm_sub_rev] at h
    linarith
  · exact maxAffine_difference_le hm ρ x y

theorem strengthened_weak_duality {m : ℕ} {ρ : ℝ} (hρ : 0 < ρ)
    (y z : Vec m) {p : Vec m} (hp : p ∈ simplex m) :
    dualObjective ρ y p + (∑ i, (z i - primalCandidate ρ y p i) ^ 2) / ρ ≤
      primalObjective ρ y z := by
  have heq : dualObjective ρ y p + (∑ i, (z i - primalCandidate ρ y p i) ^ 2) / ρ =
      (∑ i, p i * (z i - 8 * ρ * (i.val + 1))) + (∑ i, (z i - y i) ^ 2) / ρ := by
    unfold dualObjective
    rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [primalCandidate]
    field_simp
    ring
  rw [heq]
  exact add_le_add_right (weighted_le_maxAffine ρ z hp) _

theorem primalCandidate_unique {m : ℕ} (hm : 0 < m) {ρ : ℝ} (hρ : 0 < ρ)
    {y p : Vec m} (hp : IsDualMax ρ y p) {z : Vec m}
    (hz : ∀ w, primalObjective ρ y z ≤ primalObjective ρ y w) :
    z = primalCandidate ρ y p := by
  have hz' := hz (primalCandidate ρ y p)
  rw [primalCandidate_attains hm hρ hp] at hz'
  have hs := strengthened_weak_duality hρ y z hp.1
  have hdiv : (∑ i, (z i - primalCandidate ρ y p i) ^ 2) / ρ ≤ 0 := by linarith
  have hsum : (∑ i, (z i - primalCandidate ρ y p i) ^ 2) ≤ 0 := by
    simpa only [zero_mul] using (div_le_iff₀ hρ).mp hdiv
  funext i
  have hi := Finset.single_le_sum (fun j _ => sq_nonneg (z j - primalCandidate ρ y p j))
    (Finset.mem_univ i)
  nlinarith [sq_nonneg (z i - primalCandidate ρ y p i)]

theorem moreau_unique_proximal_point {m : ℕ} (hm : 0 < m) {ρ : ℝ} (hρ : 0 < ρ)
    (y : Euclid m) :
    ∃! z : Euclid m, ∀ w : Euclid m,
      primalObjective ρ (fun i => y i) (fun i => z i) ≤
        primalObjective ρ (fun i => y i) (fun i => w i) := by
  obtain ⟨p, hp⟩ := exists_dualMax hm ρ (fun i => y i)
  let z : Euclid m := (WithLp.equiv 2 (Fin m → ℝ)).symm (primalCandidate ρ (fun i => y i) p)
  refine ⟨z, ?_, ?_⟩
  · intro w
    change primalObjective ρ (fun i => y i) (primalCandidate ρ (fun i => y i) p) ≤ _
    rw [primalCandidate_attains hm hρ hp]
    exact weak_duality hρ _ _ hp.1
  · intro w hw
    have heq := primalCandidate_unique hm hρ hp
      (fun v => hw ((WithLp.equiv 2 (Fin m → ℝ)).symm v))
    ext i
    exact congrFun heq i

theorem proximal_radius_and_gradient {m : ℕ} (hm : 0 < m) {ρ : ℝ} (hρ : 0 < ρ)
    (y : Euclid m) {z : Euclid m}
    (hz : ∀ w : Euclid m, primalObjective ρ (fun i => y i) (fun i => z i) ≤
      primalObjective ρ (fun i => y i) (fun i => w i)) :
    ‖z - y‖ ≤ ρ / 2 ∧ chainGradient hm ρ y = (2 / ρ) • (y - z) := by
  have hp := chainGradient_spec hm ρ y
  have heq := primalCandidate_unique hm hρ hp
    (fun v => hz ((WithLp.equiv 2 (Fin m → ℝ)).symm v))
  constructor
  · have hsq := primalCandidate_radius_sq (ρ := ρ) (fun i => y i) hp.1
    rw [← heq] at hsq
    have hn := euclidean_norm_sq (z - y)
    simp only [PiLp.sub_apply] at hn
    nlinarith [norm_nonneg (z - y)]
  · ext i
    have hi := congrFun heq i
    simp only [primalCandidate] at hi
    simp only [PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    rw [hi]
    field_simp
    ring

end

end ExactValue
