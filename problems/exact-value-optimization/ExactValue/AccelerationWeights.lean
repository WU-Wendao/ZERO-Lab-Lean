import ExactValue.Bounds

set_option autoImplicit false

namespace ExactValue

noncomputable section

def accelerationScale : ℕ → ℝ
  | 0 => 0
  | n + 1 => (1 + Real.sqrt (1 + 4 * accelerationScale n ^ 2)) / 2

theorem accelerationScale_pos (n : ℕ) : 0 < accelerationScale (n + 1) := by
  rw [accelerationScale]
  positivity

theorem accelerationScale_rec (n : ℕ) :
    accelerationScale (n + 1) ^ 2 - accelerationScale n ^ 2 = accelerationScale (n + 1) := by
  have hs := Real.sq_sqrt (show 0 ≤ 1 + 4 * accelerationScale n ^ 2 by positivity)
  rw [accelerationScale]
  nlinarith

theorem accelerationScale_lower (n : ℕ) : (n : ℝ) / 2 ≤ accelerationScale n :=
  accelerated_weight_growth accelerationScale rfl accelerationScale_pos accelerationScale_rec n

def accelerationWeight (L : ℝ) (n : ℕ) : ℝ := accelerationScale n ^ 2 / L

def accelerationStep (L : ℝ) (n : ℕ) : ℝ := accelerationScale (n + 1) / L

theorem accelerationWeight_zero (L : ℝ) : accelerationWeight L 0 = 0 := by
  simp [accelerationWeight, accelerationScale]

theorem accelerationStep_pos {L : ℝ} (hL : 0 < L) (n : ℕ) : 0 < accelerationStep L n :=
  div_pos (accelerationScale_pos n) hL

theorem accelerationWeight_nonneg {L : ℝ} (hL : 0 < L) (n : ℕ) : 0 ≤ accelerationWeight L n := by
  unfold accelerationWeight
  positivity

theorem accelerationWeight_add_step {L : ℝ} (_hL : 0 < L) (n : ℕ) :
    accelerationWeight L n + accelerationStep L n = accelerationWeight L (n + 1) := by
  unfold accelerationWeight accelerationStep
  rw [← add_div]
  congr 1
  linarith [accelerationScale_rec n]

theorem accelerationWeight_step_sq {L : ℝ} (hL : 0 < L) (n : ℕ) :
    accelerationWeight L (n + 1) = L * accelerationStep L n ^ 2 := by
  unfold accelerationWeight accelerationStep
  field_simp
  ring

theorem accelerationWeight_mono {L : ℝ} (hL : 0 < L) : Monotone (accelerationWeight L) := by
  apply monotone_nat_of_le_succ
  intro n
  have ha := accelerationStep_pos hL n
  have he := accelerationWeight_add_step hL n
  linarith

theorem accelerationWeight_pos {L : ℝ} (hL : 0 < L) {n : ℕ} (hn : 0 < n) :
    0 < accelerationWeight L n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hn)
  rw [← accelerationWeight_add_step hL]
  exact add_pos_of_nonneg_of_pos (accelerationWeight_nonneg hL k) (accelerationStep_pos hL k)

theorem accelerationWeight_lower {L : ℝ} (hL : 0 < L) (n : ℕ) :
    (n : ℝ) ^ 2 / (4 * L) ≤ accelerationWeight L n := by
  have hs := accelerationScale_lower n
  unfold accelerationWeight
  apply (div_le_div_iff₀ (by positivity) hL).mpr
  have hs2 := pow_le_pow_left₀ (show (0 : ℝ) ≤ (n : ℝ) / 2 by positivity) hs 2
  nlinarith [mul_le_mul_of_nonneg_right hs2 hL.le]

end

end ExactValue
