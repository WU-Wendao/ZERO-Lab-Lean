import ExactValue.CapParameters
import ExactValue.Projection

open scoped InnerProductSpace

set_option autoImplicit false

namespace ExactValue

noncomputable section

/-- A direction can obey exact orthogonality constraints and simultaneous small-projection constraints. -/
theorem exists_unit_orthogonal_small {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (forbidden : ι → Euclid d) (a : κ → Euclid d) {R ρ : ℝ}
    (hR : 0 < R) (hρ : 0 < ρ) (ha : ∀ i, ‖a i‖ ≤ R)
    (hcap : 64 * R ^ 2 * Real.log (4 * ((Fintype.card κ : ℝ) + 1)) ≤
      ((d : ℝ) - Fintype.card ι) * ρ ^ 2) :
    ∃ v : Euclid d, ‖v‖ = 1 ∧ (∀ j, ⟪v, forbidden j⟫_ℝ = 0) ∧
      ∀ i, |⟪v, a i⟫_ℝ| ≤ ρ := by
  classical
  let K := Submodule.span ℝ (Set.range forbidden)
  have hspan : Module.finrank ℝ K ≤ Fintype.card ι := finrank_range_le_card forbidden
  have htotal : Module.finrank ℝ K + Module.finrank ℝ Kᗮ = d := by
    simpa only [Euclid, finrank_euclideanSpace_fin] using K.finrank_add_finrank_orthogonal
  have hdim : (d : ℝ) - Fintype.card ι ≤ Module.finrank ℝ Kᗮ := by
    have hspan' : (Module.finrank ℝ K : ℝ) ≤ Fintype.card ι := by exact_mod_cast hspan
    have htotal' : (Module.finrank ℝ K : ℝ) + Module.finrank ℝ Kᗮ = d := by exact_mod_cast htotal
    linarith
  have hcap' := hcap.trans (mul_le_mul_of_nonneg_right hdim (sq_nonneg ρ))
  obtain ⟨v, hv, hvnorm, hsmall⟩ := subspace_cap_avoidance Kᗮ hR hρ
    (fun i => a ((Fintype.equivFin κ).symm i)) (fun i => ha _) hcap'
  refine ⟨v, hvnorm, ?_, ?_⟩
  · intro j
    exact K.inner_left_of_mem_orthogonal (Submodule.subset_span ⟨j, rfl⟩) hv
  · intro i
    simpa using hsmall ((Fintype.equivFin κ) i)

end

end ExactValue
