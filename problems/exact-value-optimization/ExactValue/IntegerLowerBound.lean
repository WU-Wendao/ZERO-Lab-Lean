import ExactValue.OracleCompiler

set_option autoImplicit false

namespace ExactValue

noncomputable section

def paddedQuery {S : Type*} {d : ℕ} (T : ℕ) (query output : S → Euclid d)
    (s : ℕ × S) : Euclid d := if s.1 < T then query s.2 else output s.2

def paddedAdvance {S : Type*} (T : ℕ) (advance : S → ℝ → S)
    (s : ℕ × S) (y : ℝ) : ℕ × S :=
  (s.1 + 1, if s.1 < T then advance s.2 y else s.2)

theorem padded_state {S : Type*} {d : ℕ} (T : ℕ) (initial : S)
    (advance : S → ℝ → S) (query output : S → Euclid d) (F : Euclid d → ℝ)
    (n : ℕ) (hn : n ≤ T) :
    oracleState (0, initial) (paddedAdvance T advance) (paddedQuery T query output) F n =
      (n, oracleState initial advance query F n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hnT : n < T := by omega
    simp only [oracleState, ih (by omega), paddedAdvance, paddedQuery, if_pos hnT]

theorem padded_output {S : Type*} {d : ℕ} (T : ℕ) (initial : S)
    (advance : S → ℝ → S) (query output : S → Euclid d) (F : Euclid d → ℝ) :
    paddedQuery T query output (oracleState (0, initial) (paddedAdvance T advance)
      (paddedQuery T query output) F T) = output (oracleState initial advance query F T) := by
  rw [padded_state T initial advance query output F T le_rfl]
  simp [paddedQuery]

/-- Lower bound with explicit block size and geometric condition, for arbitrary deterministic state machines. -/
theorem block_lower_bound {S : Type*} {m d b T : ℕ} (hm : 0 < m) (hmd : m < d)
    (hb : 0 < b) (hT : T < m * b) (initial : S) (advance : S → ℝ → S)
    (query output : S → Euclid d) {β R ρ η s : ℝ}
    (hβ : 0 < β) (hR : 0 < R) (hs : 0 < s) (hsq : s ^ 2 = (m : ℝ))
    (hρ : ρ = R / (256 * (m : ℝ) * s)) (hη : η = β / (4096 * (m : ℝ) ^ 2))
    (hquery : ∀ z, ‖query z‖ ≤ R) (houtput : ∀ z, ‖output z‖ ≤ R)
    (hcap : 64 * R ^ 2 * Real.log (4 * ((m : ℝ) * b + 1)) ≤
      ((d : ℝ) - m - b) * ρ ^ 2) :
    ∃ F : Euclid d → ℝ, AdmissibleObjective d β R F ∧
      StrongConvexOn Set.univ η F ∧ (∀ μ, StrongConvexOn Set.univ μ F → μ ≤ η) ∧
      ∃ xstar : Euclid d, (∀ y, F xstar ≤ F y) ∧
        11 / 131072 * (β * R ^ 2 / (m : ℝ) ^ 2) ≤
          F (output (oracleState initial advance query F T)) - F xstar := by
  have hρpos := (hard_parameter_bounds hm hβ hR hs hsq hρ hη).1
  have hpadded : ∀ z, ‖paddedQuery T query output z‖ ≤ R := by
    intro z
    unfold paddedQuery
    split_ifs <;> [exact hquery _; exact houtput _]
  obtain ⟨U, hU, hsmall⟩ := exists_hard_frame_for_queries (β := β) (η := η) (r := R / 4)
    hm hb (0, initial) (paddedAdvance T advance) (paddedQuery T query output) hR hρpos hpadded hcap
  let F := embeddedObjective β ρ η (R / 4) U
  have hlast := hsmall T hT
  rw [padded_output T initial advance query output] at hlast
  have hmod := hard_objective_exact_modulus hm hmd hβ hR hs hsq hρ hη U
  exact ⟨F, hard_objective_admissible hm hβ hR hs hsq hρ hη hU, hmod.1, hmod.2,
    hard_objective_output_gap hm hβ hR hs hsq hρ hη hU
      (output (oracleState initial advance query F T)) hlast⟩

/-- Integer-parameter lower bound (thm:integer), with c₀ = 2⁻²⁴ and d₀ = 8.
The statement covers all bounded deterministic state machines, without any measurability restriction. -/
theorem integer_parameter_lower_bound {S : Type*} {d m T : ℕ}
    (hd : 8 ≤ d) (hm : 0 < m) (hmd : 4 * m ≤ d) (hT : 8 * T < d * m)
    (initial : S) (advance : S → ℝ → S) (query output : S → Euclid d)
    {β R : ℝ} (hβ : 0 < β) (hR : 0 < R)
    (hquery : ∀ z, ‖query z‖ ≤ R) (houtput : ∀ z, ‖output z‖ ≤ R)
    (hscale : (m : ℝ) ^ 3 * (1 + Real.log (d : ℝ)) ≤ (1 / 16777216 : ℝ) * d) :
    ∃ F : Euclid d → ℝ, AdmissibleObjective d β R F ∧
      StrongConvexOn Set.univ (β / (4096 * (m : ℝ) ^ 2)) F ∧
      (∀ μ, StrongConvexOn Set.univ μ F → μ ≤ β / (4096 * (m : ℝ) ^ 2)) ∧
      ∃ xstar : Euclid d, (∀ y, F xstar ≤ F y) ∧
        11 / 131072 * (β * R ^ 2 / (m : ℝ) ^ 2) ≤
          F (output (oracleState initial advance query F T)) - F xstar := by
  let b := d / 4
  let s := Real.sqrt (m : ℝ)
  let ρ := R / (256 * (m : ℝ) * s)
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hs : 0 < s := Real.sqrt_pos.mpr hmpos
  have hsq : s ^ 2 = (m : ℝ) := Real.sq_sqrt hmpos.le
  have hd' : (8 : ℝ) ≤ d := by exact_mod_cast hd
  have hm' : (m : ℝ) ≤ (d : ℝ) / 4 := by
    have : (4 : ℝ) * m ≤ d := by exact_mod_cast hmd
    linarith
  have hb' : (b : ℝ) ≤ (d : ℝ) / 4 := by
    have : 4 * b ≤ d := by dsimp [b]; omega
    have hreal : (4 : ℝ) * b ≤ d := by exact_mod_cast this
    linarith
  have hcount : (m : ℝ) * b ≤ (d : ℝ) ^ 2 / 16 + 1 := by
    have := mul_le_mul hm' hb' (by positivity : (0 : ℝ) ≤ b) (by positivity : (0 : ℝ) ≤ (d : ℝ) / 4)
    nlinarith
  have hdim : (d : ℝ) / 2 ≤ (d : ℝ) - m - b := by linarith
  have hcap := cap_parameter_condition hd' hmpos (show (0 : ℝ) ≤ (m : ℝ) * b by positivity)
    hR hs hsq hcount hdim (show ρ = R / (256 * (m : ℝ) * s) by rfl) hscale
  have hTb : T < m * b := by
    simpa only [Nat.mul_comm] using budget_implies_incomplete_chain d m T hd hT
  exact block_lower_bound hm (by omega) (show 0 < b by dsimp [b]; omega) hTb
    initial advance query output hβ hR hs hsq rfl rfl hquery houtput hcap

end

end ExactValue
