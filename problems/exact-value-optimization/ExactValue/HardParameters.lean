import ExactValue.Admissibility

set_option autoImplicit false

namespace ExactValue

noncomputable section

/-- The analytic function class in the paper, with a genuine derivative and a unique global minimum. -/
structure AdmissibleObjective (d : ℕ) (β R : ℝ) (F : Euclid d → ℝ) : Prop where
  convex : ConvexOn ℝ Set.univ F
  contDiff : ContDiff ℝ 1 F
  gradient_lipschitz : ∃ G : Euclid d → Euclid d,
    (∀ x, HasFDerivAt F (innerSL ℝ (G x)) x) ∧
    ∀ x y, ‖G x - G y‖ ≤ β * ‖x - y‖
  minimizer : ∃ x : Euclid d, ‖x‖ ≤ R / 2 ∧ (∀ y, F x ≤ F y) ∧
    ∀ z, (∀ y, F z ≤ F y) → z = x

theorem hard_parameter_bounds {m : ℕ} (hm : 0 < m) {β R ρ η s : ℝ}
    (hβ : 0 < β) (hR : 0 < R) (hs : 0 < s) (hsq : s ^ 2 = (m : ℝ))
    (hρ : ρ = R / (256 * (m : ℝ) * s)) (hη : η = β / (4096 * (m : ℝ) ^ 2)) :
    0 < ρ ∧ ρ ≤ R / 256 ∧ 0 < η ∧ β / 2 + η < β ∧ R / 4 + ρ < R / 2 := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have hmpos : (0 : ℝ) < m := by linarith
  have hs1 : 1 ≤ s := by nlinarith
  have hden : 256 ≤ 256 * (m : ℝ) * s := by nlinarith
  have hρpos : 0 < ρ := by rw [hρ]; positivity
  have hρle : ρ ≤ R / 256 := by
    rw [hρ]
    exact div_le_div_of_nonneg_left hR.le (by norm_num) hden
  have hηpos : 0 < η := by rw [hη]; positivity
  have hdenη : 4096 ≤ 4096 * (m : ℝ) ^ 2 := by nlinarith
  have hηle : η ≤ β / 4096 := by
    rw [hη]
    exact div_le_div_of_nonneg_left hβ.le (by norm_num) hdenη
  exact ⟨hρpos, hρle, hηpos, by linarith, by linarith⟩

theorem hard_objective_admissible {m d : ℕ} (hm : 0 < m) {β R ρ η s : ℝ}
    (hβ : 0 < β) (hR : 0 < R) (hs : 0 < s) (hsq : s ^ 2 = (m : ℝ))
    (hρ : ρ = R / (256 * (m : ℝ) * s)) (hη : η = β / (4096 * (m : ℝ) ^ 2))
    {U : Fin m → Euclid d} (hU : Orthonormal ℝ U) :
    AdmissibleObjective d β R (embeddedObjective β ρ η (R / 4) U) := by
  obtain ⟨hρpos, _, hηpos, hLip, hrad⟩ := hard_parameter_bounds hm hβ hR hs hsq hρ hη
  have hr : 0 ≤ R / 4 := by positivity
  refine ⟨?_, embeddedObjective_contDiff hm hρpos hr U, ?_, ?_⟩
  · exact ((embeddedObjective_strongConvex hm hβ.le hρpos hr U).strictConvexOn hηpos).convexOn
  · refine ⟨embeddedGradient hm β ρ η (R / 4) hr U,
      embeddedObjective_hasFDerivAt hm hρpos hr U, ?_⟩
    intro x y
    exact (embeddedGradient_lipschitz_bound hm hβ.le hρpos hηpos.le hr hU x y).trans
      (mul_le_mul_of_nonneg_right hLip.le (norm_nonneg _))
  · obtain ⟨x, hmin, hnorm, huniq⟩ := embeddedObjective_exists_unique_min hm hβ hρpos hηpos hr hU
    exact ⟨x, (hnorm.trans_lt hrad).le, hmin, huniq⟩

/-- The exact modulus is expressed as an attained greatest possible strong-convexity parameter. -/
theorem hard_objective_exact_modulus {m d : ℕ} (hm : 0 < m) (hmd : m < d)
    {β R ρ η s : ℝ} (hβ : 0 < β) (hR : 0 < R) (hs : 0 < s)
    (hsq : s ^ 2 = (m : ℝ)) (hρ : ρ = R / (256 * (m : ℝ) * s))
    (hη : η = β / (4096 * (m : ℝ) ^ 2)) (U : Fin m → Euclid d) :
    StrongConvexOn Set.univ η (embeddedObjective β ρ η (R / 4) U) ∧
    ∀ μ, StrongConvexOn Set.univ μ (embeddedObjective β ρ η (R / 4) U) → μ ≤ η := by
  have hρpos := (hard_parameter_bounds hm hβ hR hs hsq hρ hη).1
  exact ⟨embeddedObjective_strongConvex hm hβ.le hρpos (by positivity) U,
    fun _ hμ => embeddedObjective_modulus_le hmd (by positivity) U hμ⟩

def comparisonPoint {m d : ℕ} (R s : ℝ) (U : Fin m → Euclid d) : Euclid d :=
  frameWrite U ((WithLp.equiv 2 (Fin m → ℝ)).symm (fun _ => -((R / 4) / s)))

theorem comparisonPoint_coordinates {m d : ℕ} (R s : ℝ)
    {U : Fin m → Euclid d} (hU : Orthonormal ℝ U) :
    frameCoordinates U (comparisonPoint R s U) = fun _ => -((R / 4) / s) := by
  have h := frameRead_write hU ((WithLp.equiv 2 (Fin m → ℝ)).symm (fun _ => -((R / 4) / s)))
  ext i
  exact congrArg (fun y : Euclid m => y i) h

theorem comparisonPoint_norm {m d : ℕ} {R s : ℝ} (hR : 0 ≤ R) (hs : 0 < s)
    (hsq : s ^ 2 = (m : ℝ)) {U : Fin m → Euclid d} (hU : Orthonormal ℝ U) :
    ‖comparisonPoint R s U‖ = R / 4 := by
  rw [comparisonPoint, frameWrite_norm hU]
  have hn := euclidean_norm_sq
    ((WithLp.equiv 2 (Fin m → ℝ)).symm (fun _ => -((R / 4) / s)))
  simp only [WithLp.equiv_symm_pi_apply, neg_sq, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hn
  have heq : (m : ℝ) * (R / 4 / s) ^ 2 = (R / 4) ^ 2 := by
    rw [← hsq]
    field_simp
    ring
  rw [heq] at hn
  nlinarith [norm_nonneg ((WithLp.equiv 2 (Fin m → ℝ)).symm
    (fun _ => -((R / 4) / s)) : Euclid m)]

theorem hard_objective_output_gap {m d : ℕ} (hm : 0 < m) {β R ρ η s : ℝ}
    (hβ : 0 < β) (hR : 0 < R) (hs : 0 < s) (hsq : s ^ 2 = (m : ℝ))
    (hρ : ρ = R / (256 * (m : ℝ) * s)) (hη : η = β / (4096 * (m : ℝ) ^ 2))
    {U : Fin m → Euclid d} (hU : Orthonormal ℝ U) (xout : Euclid d)
    (hlast : |frameCoordinates U xout ⟨m - 1, by omega⟩| ≤ ρ) :
    ∃ xstar : Euclid d, (∀ y, embeddedObjective β ρ η (R / 4) U xstar ≤
      embeddedObjective β ρ η (R / 4) U y) ∧
      11 / 131072 * (β * R ^ 2 / (m : ℝ) ^ 2) ≤
        embeddedObjective β ρ η (R / 4) U xout - embeddedObjective β ρ η (R / 4) U xstar := by
  obtain ⟨xstar, _, hmin, _⟩ := (hard_objective_admissible hm hβ hR hs hsq hρ hη hU).minimizer
  exact ⟨xstar, hmin, embedded_output_gap hm hβ hR hs hsq hρ hη U xout
    (comparisonPoint R s U) hlast (comparisonPoint_coordinates R s hU)
    (comparisonPoint_norm hR.le hs hsq hU) (hmin _)⟩

end

end ExactValue
