import Mathlib.Probability.Distributions.Gaussian
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Data.Complex.ExponentialBounds

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real

set_option autoImplicit false

namespace ExactValue

noncomputable section

def standardGaussianVector (p : ℕ) : Measure (Fin p → ℝ) :=
  Measure.pi (fun _ => gaussianReal 0 1)

instance standardGaussianVector_probability (p : ℕ) :
    IsProbabilityMeasure (standardGaussianVector p) := by
  unfold standardGaussianVector
  infer_instance

def squaredCoordinates {p : ℕ} (x : Fin p → ℝ) : ℝ := ∑ i, (x i) ^ 2

theorem gaussian_half_laplace :
    (∫ x : ℝ, Real.exp (-x ^ 2 / 2) ∂gaussianReal 0 1) = (Real.sqrt 2)⁻¹ := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
  have heq : (fun x : ℝ => gaussianPDFReal 0 1 x • Real.exp (-x ^ 2 / 2)) =
      fun x => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1 : ℝ) * x ^ 2) := by
    funext x
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, smul_eq_mul,
      mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [heq, integral_const_mul, integral_gaussian, div_one, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hp : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  rw [mul_inv_rev]
  field_simp

theorem gaussian_exp_integrable :
    Integrable (fun x : ℝ => Real.exp (-x ^ 2 / 2)) (gaussianReal 0 1) := by
  apply Integrable.mono' (integrable_const (1 : ℝ))
  · exact (by fun_prop : Measurable (fun x : ℝ => Real.exp (-x ^ 2 / 2))).aestronglyMeasurable
  · filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_one_iff.mpr
    nlinarith [sq_nonneg x]

theorem gaussian_energy_exp_product {p : ℕ} (x : Fin p → ℝ) :
    Real.exp (-squaredCoordinates x / 2) = ∏ i, Real.exp (-(x i) ^ 2 / 2) := by
  rw [← Real.exp_sum]
  congr 1
  simp only [squaredCoordinates, neg_div, Finset.sum_div, Finset.sum_neg_distrib]

theorem gaussian_vector_half_laplace (p : ℕ) :
    (∫ x, Real.exp (-squaredCoordinates x / 2) ∂standardGaussianVector p) =
      (Real.sqrt 2)⁻¹ ^ p := by
  simp_rw [gaussian_energy_exp_product]
  letI : MeasureSpace ℝ := ⟨gaussianReal 0 1⟩
  letI : SigmaFinite (volume : Measure ℝ) :=
    show SigmaFinite (gaussianReal 0 1) from inferInstance
  have hi := integral_fintype_prod_eq_pow (Fin p) (fun x : ℝ => Real.exp (-x ^ 2 / 2))
  change (∫ x, ∏ i, Real.exp (-(x i) ^ 2 / 2) ∂standardGaussianVector p) =
    (∫ x : ℝ, Real.exp (-x ^ 2 / 2) ∂gaussianReal 0 1) ^ Fintype.card (Fin p) at hi
  simpa only [gaussian_half_laplace, Fintype.card_fin] using hi

theorem gaussian_vector_exp_integrable (p : ℕ) :
    Integrable (fun x => Real.exp (-squaredCoordinates x / 2)) (standardGaussianVector p) := by
  simp_rw [gaussian_energy_exp_product]
  letI : MeasureSpace ℝ := ⟨gaussianReal 0 1⟩
  letI : SigmaFinite (volume : Measure ℝ) :=
    show SigmaFinite (gaussianReal 0 1) from inferInstance
  exact Integrable.fintype_prod (fun _ => gaussian_exp_integrable)

theorem gaussian_chi_square_lower_tail_real (p : ℕ) :
    (standardGaussianVector p).real {x | squaredCoordinates x ≤ (p : ℝ) / 2} ≤
      Real.exp (-(p : ℝ) / 16) := by
  have hset : {x : Fin p → ℝ | Real.exp (-(p : ℝ) / 4) ≤ Real.exp (-squaredCoordinates x / 2)} =
      {x | squaredCoordinates x ≤ (p : ℝ) / 2} := by
    ext x
    simp only [Set.mem_setOf_eq, Real.exp_le_exp]
    constructor <;> intro h <;> linarith
  have hb := mul_meas_ge_le_integral_of_nonneg
    (μ := standardGaussianVector p) (ae_of_all _ (fun x => (Real.exp_pos (-squaredCoordinates x / 2)).le))
    (gaussian_vector_exp_integrable p) (Real.exp (-(p : ℝ) / 4))
  rw [hset, gaussian_vector_half_laplace] at hb
  have hbase : (Real.sqrt 2)⁻¹ = Real.exp (-Real.log 2 / 2) := by
    rw [neg_div, Real.exp_neg, ← Real.log_sqrt (by norm_num : (0 : ℝ) ≤ 2),
      Real.exp_log (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))]
  rw [hbase, ← Real.exp_nat_mul] at hb
  have hlog : (5 / 8 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hnum : Real.exp ((p : ℝ) * (-Real.log 2 / 2)) ≤
      Real.exp (-(p : ℝ) / 4) * Real.exp (-(p : ℝ) / 16) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (Nat.cast_nonneg p : (0 : ℝ) ≤ p) (sub_nonneg.mpr hlog)]
  exact (mul_le_mul_left (Real.exp_pos _)).mp (hb.trans hnum)

/-- The law is the product of p independent standard normal coordinates. -/
theorem gaussian_chi_square_lower_tail (p : ℕ) :
    standardGaussianVector p {x | squaredCoordinates x ≤ (p : ℝ) / 2} ≤
      ENNReal.ofReal (Real.exp (-(p : ℝ) / 16)) := by
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal (Real.exp_pos _).le]
  exact gaussian_chi_square_lower_tail_real p

theorem gaussian_chi_square_lower_tail_of_law {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {p : ℕ} (g : Ω → Fin p → ℝ) (hg : Measurable g)
    (hlaw : μ.map g = standardGaussianVector p) :
    μ {ω | squaredCoordinates (g ω) ≤ (p : ℝ) / 2} ≤
      ENNReal.ofReal (Real.exp (-(p : ℝ) / 16)) := by
  have hs : MeasurableSet {x : Fin p → ℝ | squaredCoordinates x ≤ (p : ℝ) / 2} := by
    apply measurableSet_le _ measurable_const
    unfold squaredCoordinates
    fun_prop
  have h := gaussian_chi_square_lower_tail p
  rw [← hlaw, Measure.map_apply hg hs] at h
  exact h

end

end ExactValue
