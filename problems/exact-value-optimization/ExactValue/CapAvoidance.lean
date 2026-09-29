import ExactValue.FiniteSigns

open Finset
open scoped InnerProductSpace

set_option autoImplicit false

namespace ExactValue

noncomputable section

theorem cap_exponential_threshold {p M : ℕ} {R ρ s : ℝ} (hR : 0 < R)
    (hsq : s ^ 2 = (p : ℝ))
    (hcap : 64 * R ^ 2 * Real.log (4 * ((M : ℝ) + 1)) ≤ (p : ℝ) * ρ ^ 2) :
    2 * (M : ℝ) * Real.exp (((ρ * s) / R ^ 2) ^ 2 / 2 * R ^ 2) <
      Real.exp (((ρ * s) / R ^ 2) * (ρ * s)) := by
  let q := (ρ * s) ^ 2 / (2 * R ^ 2)
  have harg : 1 < 4 * ((M : ℝ) + 1) := by have := Nat.cast_nonneg (α := ℝ) M; linarith
  have hlog : 0 < Real.log (4 * ((M : ℝ) + 1)) := Real.log_pos harg
  have hsq' : (ρ * s) ^ 2 = (p : ℝ) * ρ ^ 2 := by rw [mul_pow, hsq]; ring
  have hlogq : Real.log (4 * ((M : ℝ) + 1)) < q := by
    dsimp [q]
    apply (lt_div_iff₀ (by positivity)).mpr
    rw [hsq']
    nlinarith [mul_pos (sq_pos_of_pos hR) hlog]
  have hcount : 2 * (M : ℝ) < Real.exp q := by
    have he := Real.exp_lt_exp.mpr hlogq
    rw [Real.exp_log (by linarith)] at he
    linarith
  have heq1 : ((ρ * s) / R ^ 2) ^ 2 / 2 * R ^ 2 = q := by
    dsimp [q]
    field_simp
    ring
  have heq2 : ((ρ * s) / R ^ 2) * (ρ * s) = q + q := by
    dsimp [q]
    field_simp
    ring
  rw [heq1, heq2, Real.exp_add]
  exact mul_lt_mul_of_pos_right hcount (Real.exp_pos _)

/-- Simultaneous cap avoidance in the span of any orthonormal family.
The proof averages over finitely many normalized sign vectors. -/
theorem orthonormal_cap_avoidance {p d M : ℕ} (hp : 0 < p) {R ρ : ℝ}
    (hR : 0 < R) (hρ : 0 < ρ) {U : Fin p → Euclid d} (hU : Orthonormal ℝ U)
    (a : Fin M → Euclid d) (ha : ∀ i, ‖a i‖ ≤ R)
    (hcap : 64 * R ^ 2 * Real.log (4 * ((M : ℝ) + 1)) ≤ (p : ℝ) * ρ ^ 2) :
    ∃ y : Euclid p, ‖frameWrite U y‖ = 1 ∧ ∀ i, |⟪frameWrite U y, a i⟫_ℝ| ≤ ρ := by
  let s := Real.sqrt (p : ℝ)
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hs : 0 < s := Real.sqrt_pos.mpr hp'
  have hsq : s ^ 2 = (p : ℝ) := Real.sq_sqrt hp'.le
  let b := fun (i : Fin M) (j : Fin p) => ⟪U j, a i⟫_ℝ
  have hb : ∀ i, ∑ j, (b i j) ^ 2 ≤ R ^ 2 := by
    intro i
    have hbessel := hU.sum_inner_products_le (s := Finset.univ) (a i)
    simp only [Real.norm_eq_abs, sq_abs] at hbessel
    exact hbessel.trans (pow_le_pow_left₀ (norm_nonneg _) (ha i) 2)
  obtain ⟨σ, hσ⟩ := exists_signed_sums_lt b (show 0 < (ρ * s) / R ^ 2 by positivity) hb
    (cap_exponential_threshold hR hsq hcap)
  let z : Euclid p := (WithLp.equiv 2 (Fin p → ℝ)).symm (fun j => sign (σ j))
  have hzsq : ‖z‖ ^ 2 = (p : ℝ) := by
    rw [euclidean_norm_sq]
    simp [z, sign_sq]
  have hz : ‖z‖ = s := by nlinarith [norm_nonneg z]
  refine ⟨(1 / s) • z, ?_, ?_⟩
  · rw [frameWrite_norm hU, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity), hz, div_mul_cancel₀ _ hs.ne']
  · intro i
    have hi : ⟪frameWrite U ((1 / s) • z), a i⟫_ℝ = signedSum σ (b i) / s := by
      rw [map_smul, real_inner_smul_left, frameWrite_apply, sum_inner]
      simp only [real_inner_smul_left]
      change (1 / s) * (∑ j, sign (σ j) * b i j) = signedSum σ (b i) / s
      rw [signedSum]
      ring
    rw [hi, abs_div, abs_of_pos hs]
    exact (div_le_iff₀ hs).mpr (hσ i).le

/-- The subspace cap-avoidance lemma stated in the paper. -/
theorem subspace_cap_avoidance {d M : ℕ} (S : Submodule ℝ (Euclid d)) {R ρ : ℝ}
    (hR : 0 < R) (hρ : 0 < ρ) (a : Fin M → Euclid d) (ha : ∀ i, ‖a i‖ ≤ R)
    (hcap : 64 * R ^ 2 * Real.log (4 * ((M : ℝ) + 1)) ≤
      (Module.finrank ℝ S : ℝ) * ρ ^ 2) :
    ∃ u : Euclid d, u ∈ S ∧ ‖u‖ = 1 ∧ ∀ i, |⟪u, a i⟫_ℝ| ≤ ρ := by
  let U : Fin (Module.finrank ℝ S) → Euclid d := fun j => (stdOrthonormalBasis ℝ S j : Euclid d)
  have hU : Orthonormal ℝ U :=
    (stdOrthonormalBasis ℝ S).orthonormal.comp_linearIsometry S.subtypeₗᵢ
  have hp : 0 < Module.finrank ℝ S := by
    by_contra hp0
    have hp0' : Module.finrank ℝ S = 0 := by omega
    rw [hp0', Nat.cast_zero, zero_mul] at hcap
    have hlog : 0 < Real.log (4 * ((M : ℝ) + 1)) := Real.log_pos (by
      have := Nat.cast_nonneg (α := ℝ) M
      linarith)
    have : 0 < 64 * R ^ 2 * Real.log (4 * ((M : ℝ) + 1)) := by positivity
    linarith
  obtain ⟨y, hyn, hy⟩ := orthonormal_cap_avoidance hp hR hρ hU a ha hcap
  refine ⟨frameWrite U y, ?_, hyn, hy⟩
  rw [frameWrite_apply]
  exact Submodule.sum_mem S (fun j _ => S.smul_mem (y j) (stdOrthonormalBasis ℝ S j).property)

end

end ExactValue
