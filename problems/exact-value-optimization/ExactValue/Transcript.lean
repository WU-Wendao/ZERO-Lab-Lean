import ExactValue.Moreau

/-! Exact replay of an adaptive deterministic transcript. No measurability
assumption is needed for this pathwise identity. -/

set_option autoImplicit false

namespace ExactValue

def onlineState {S : Type*} (initial : S) (advance : S → ℝ → S)
    (replies : ℕ → ℝ) : ℕ → S
  | 0 => initial
  | n + 1 => advance (onlineState initial advance replies n) (replies n)

def oracleState {S X : Type*} (initial : S) (advance : S → ℝ → S)
    (query : S → X) (f : X → ℝ) : ℕ → S
  | 0 => initial
  | n + 1 =>
    let s := oracleState initial advance query f n
    advance s (f (query s))

theorem exact_transcript_replay {S X : Type*} (initial : S) (advance : S → ℝ → S)
    (query : S → X) (f : X → ℝ) (replies : ℕ → ℝ) (T : ℕ)
    (hconsistent : ∀ n < T,
      replies n = f (query (onlineState initial advance replies n))) :
    ∀ n ≤ T, onlineState initial advance replies n = oracleState initial advance query f n := by
  intro n hn
  induction n with
  | zero => rfl
  | succ n ih =>
    have hnT : n < T := by omega
    have heq := ih (by omega)
    simp only [onlineState, oracleState]
    rw [hconsistent n hnT, heq]

theorem exact_output_replay {S X Y : Type*} (initial : S) (advance : S → ℝ → S)
    (query : S → X) (output : S → Y) (f : X → ℝ) (replies : ℕ → ℝ) (T : ℕ)
    (hconsistent : ∀ n < T,
      replies n = f (query (onlineState initial advance replies n))) :
    output (onlineState initial advance replies T) =
      output (oracleState initial advance query f T) := by
  rw [exact_transcript_replay initial advance query f replies T hconsistent T le_rfl]

/-- A zero current coordinate and small future coordinates reproduce the reply
made before those directions were selected. The frame's construction is separate. -/
theorem fixed_objective_reply {m : ℕ} {ρ A radial reply : ℝ} (hρ : 0 < ρ)
    (coordinates : Vec m) (j : Fin m) (hzero : coordinates j = 0)
    (hfuture : ∀ k, j < k → |coordinates k| ≤ ρ)
    (hreply : reply = A * dualValue ρ (truncateBefore coordinates j) + radial) :
    reply = A * dualValue ρ coordinates + radial := by
  rw [hreply, exact_zero_shielding hρ coordinates j hzero hfuture]

theorem fixed_moreau_objective_reply {m : ℕ} {ρ A radial reply : ℝ} (hρ : 0 < ρ)
    (coordinates : Vec m) (j : Fin m) (hzero : coordinates j = 0)
    (hfuture : ∀ k, j < k → |coordinates k| ≤ ρ)
    (hreply : reply = A * moreauValue ρ (truncateBefore coordinates j) + radial) :
    reply = A * moreauValue ρ coordinates + radial := by
  rw [hreply, moreau_exact_zero_shielding hρ coordinates j hzero hfuture]

end ExactValue
