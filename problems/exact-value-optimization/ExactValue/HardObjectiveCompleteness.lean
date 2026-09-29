import ExactValue.HardParameters

set_option autoImplicit false

namespace ExactValue

noncomputable section

theorem hard_objective_strict_minimizer {m d : ℕ} (hm : 0 < m) {β R ρ η s : ℝ}
    (hβ : 0 < β) (hR : 0 < R) (hs : 0 < s) (hsq : s ^ 2 = (m : ℝ))
    (hρ : ρ = R / (256 * (m : ℝ) * s)) (hη : η = β / (4096 * (m : ℝ) ^ 2))
    {U : Fin m → Euclid d} (hU : Orthonormal ℝ U) :
    ∃ x : Euclid d, ‖x‖ < R / 2 ∧
      (∀ y, embeddedObjective β ρ η (R / 4) U x ≤ embeddedObjective β ρ η (R / 4) U y) ∧
      ∀ z, (∀ y, embeddedObjective β ρ η (R / 4) U z ≤
        embeddedObjective β ρ η (R / 4) U y) → z = x := by
  obtain ⟨hρpos, _, hηpos, _, hrad⟩ := hard_parameter_bounds hm hβ hR hs hsq hρ hη
  obtain ⟨x, hmin, hn, hu⟩ := embeddedObjective_exists_unique_min hm hβ hρpos hηpos
    (show 0 ≤ R / 4 by positivity) hU
  exact ⟨x, hn.trans_lt hrad, hmin, hu⟩

theorem hard_objective_strict_smoothness {m d : ℕ} (hm : 0 < m) {β R ρ η s : ℝ}
    (hβ : 0 < β) (hR : 0 < R) (hs : 0 < s) (hsq : s ^ 2 = (m : ℝ))
    (hρ : ρ = R / (256 * (m : ℝ) * s)) (hη : η = β / (4096 * (m : ℝ) ^ 2))
    {U : Fin m → Euclid d} (hU : Orthonormal ℝ U) :
    ∃ L : ℝ, L < β ∧ ∃ G : Euclid d → Euclid d,
      (∀ x, HasFDerivAt (embeddedObjective β ρ η (R / 4) U) (innerSL ℝ (G x)) x) ∧
      ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖ := by
  obtain ⟨hρpos, _, hηpos, hLip, _⟩ := hard_parameter_bounds hm hβ hR hs hsq hρ hη
  have hr : 0 ≤ R / 4 := by positivity
  exact ⟨β / 2 + η, hLip, embeddedGradient hm β ρ η (R / 4) hr U,
    embeddedObjective_hasFDerivAt hm hρpos hr U,
    embeddedGradient_lipschitz_bound hm hβ.le hρpos hηpos.le hr hU⟩

end

end ExactValue
