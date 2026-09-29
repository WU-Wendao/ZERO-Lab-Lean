import ExactValue.Frames
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

open Finset

set_option autoImplicit false

namespace ExactValue

noncomputable section

def sign (b : Bool) : ℝ := if b then 1 else -1

theorem sign_sq (b : Bool) : sign b ^ 2 = 1 := by cases b <;> norm_num [sign]

def signedSum {p : ℕ} (σ : Fin p → Bool) (a : Fin p → ℝ) : ℝ :=
  ∑ j, sign (σ j) * a j

theorem signed_exp_sum {p : ℕ} (a : Fin p → ℝ) (t : ℝ) :
    (∑ σ : Fin p → Bool, Real.exp (t * signedSum σ a)) =
      ∏ j, (Real.exp (t * a j) + Real.exp (-(t * a j))) := by
  simp only [signedSum, Finset.mul_sum, Real.exp_sum]
  rw [← Fintype.prod_sum (fun (j : Fin p) (b : Bool) => Real.exp (t * (sign b * a j)))]
  apply Finset.prod_congr rfl
  intro j _
  simp [sign, mul_comm, mul_left_comm, mul_assoc, add_comm]

theorem signed_exp_sum_le {p : ℕ} (a : Fin p → ℝ) (t : ℝ) :
    (∑ σ : Fin p → Bool, Real.exp (t * signedSum σ a)) ≤
      2 ^ p * Real.exp (t ^ 2 / 2 * ∑ j, (a j) ^ 2) := by
  rw [signed_exp_sum]
  calc
    _ ≤ ∏ j, (2 * Real.exp ((t * a j) ^ 2 / 2)) := by
      apply Finset.prod_le_prod
      · intro j _; positivity
      · intro j _
        have hc := Real.cosh_le_exp_half_sq (t * a j)
        rw [Real.cosh_eq] at hc
        linarith
    _ = _ := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin, ← Real.exp_sum, Finset.mul_sum]
      congr 2
      apply Finset.sum_congr rfl
      intro j _
      ring

/-- A finite exponential-potential proof of simultaneous small signed sums. -/
theorem exists_signed_sums_lt {p M : ℕ} (a : Fin M → Fin p → ℝ) {R t τ : ℝ}
    (ht : 0 < t) (ha : ∀ i, ∑ j, (a i j) ^ 2 ≤ R ^ 2)
    (hthreshold : 2 * (M : ℝ) * Real.exp (t ^ 2 / 2 * R ^ 2) < Real.exp (t * τ)) :
    ∃ σ : Fin p → Bool, ∀ i, |signedSum σ (a i)| < τ := by
  classical
  let Φ := fun σ : Fin p → Bool =>
    ∑ i, (Real.exp (t * signedSum σ (a i)) + Real.exp ((-t) * signedSum σ (a i)))
  have hsum : (∑ σ, Φ σ) ≤ 2 ^ p * (2 * (M : ℝ) * Real.exp (t ^ 2 / 2 * R ^ 2)) := by
    calc
      _ = ∑ i, ((∑ σ : Fin p → Bool, Real.exp (t * signedSum σ (a i))) +
        ∑ σ : Fin p → Bool, Real.exp ((-t) * signedSum σ (a i))) := by
          dsimp [Φ]
          rw [Finset.sum_comm]
          simp only [Finset.sum_add_distrib]
      _ ≤ ∑ _i : Fin M, (2 * (2 ^ p * Real.exp (t ^ 2 / 2 * R ^ 2))) := by
        apply Finset.sum_le_sum
        intro i _
        have hp := signed_exp_sum_le (a i) t
        have hn := signed_exp_sum_le (a i) (-t)
        simp only [neg_sq] at hn
        have he : Real.exp (t ^ 2 / 2 * ∑ j, (a i j) ^ 2) ≤
            Real.exp (t ^ 2 / 2 * R ^ 2) :=
          Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (ha i) (by positivity))
        have hm := mul_le_mul_of_nonneg_left he (show (0 : ℝ) ≤ 2 ^ p by positivity)
        linarith
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have htotal : (∑ σ, Φ σ) < ∑ _σ : Fin p → Bool, Real.exp (t * τ) := by
    have hlt := hsum.trans_lt (mul_lt_mul_of_pos_left hthreshold (show (0 : ℝ) < 2 ^ p by positivity))
    simpa [Fintype.card_fun] using hlt
  obtain ⟨σ, _, hσ⟩ := Finset.exists_lt_of_sum_lt htotal
  refine ⟨σ, ?_⟩
  intro i
  have hterm : Real.exp (t * signedSum σ (a i)) +
      Real.exp ((-t) * signedSum σ (a i)) ≤ Φ σ := by
    dsimp only [Φ]
    apply Finset.single_le_sum (f := fun j : Fin M => Real.exp (t * signedSum σ (a j)) +
      Real.exp ((-t) * signedSum σ (a j)))
    · intro j _; positivity
    · exact Finset.mem_univ i
  have hp : Real.exp (t * signedSum σ (a i)) < Real.exp (t * τ) := by
    have := Real.exp_pos ((-t) * signedSum σ (a i))
    linarith
  have hn : Real.exp ((-t) * signedSum σ (a i)) < Real.exp (t * τ) := by
    have := Real.exp_pos (t * signedSum σ (a i))
    linarith
  have hp' := Real.exp_lt_exp.mp hp
  have hn' := Real.exp_lt_exp.mp hn
  rw [abs_lt]
  constructor <;> nlinarith

end

end ExactValue
