import ExactValue.DelayedFrame
import ExactValue.HardParameters
import ExactValue.Transcript

open scoped InnerProductSpace

set_option autoImplicit false

namespace ExactValue

noncomputable section

def prefixObjective {m d : ℕ} (β ρ η r : ℝ) (U : Fin m → Euclid d)
    (k : ℕ) (x : Euclid d) : ℝ :=
  (β * ρ / 8) * moreauValue ρ (fun i => if i.val < k then ⟪U i, x⟫_ℝ else 0) +
    β / 8 * (max (‖x‖ - r) 0) ^ 2 + η / 2 * ‖x‖ ^ 2

theorem prefixObjective_congr {m d : ℕ} (β ρ η r : ℝ) (U V : Fin m → Euclid d)
    (k : ℕ) (j : Fin m) (hkj : k ≤ j.val) (hUV : ∀ i, i < j → U i = V i) :
    prefixObjective β ρ η r U k = prefixObjective β ρ η r V k := by
  funext x
  unfold prefixObjective
  congr 4
  funext i
  split_ifs with hi
  · rw [hUV i (show i.val < j.val from hi.trans_le hkj)]
  · rfl

def prefixState {S : Type*} {m d : ℕ} (initial : S) (advance : S → ℝ → S)
    (query : S → Euclid d) (b : ℕ) (β ρ η r : ℝ) (U : Fin m → Euclid d) : ℕ → S
  | 0 => initial
  | n + 1 =>
    let s := prefixState initial advance query b β ρ η r U n
    advance s (prefixObjective β ρ η r U (n / b) (query s))

theorem prefixState_congr {S : Type*} {m d b : ℕ} (initial : S) (advance : S → ℝ → S)
    (query : S → Euclid d) (hb : 0 < b) (β ρ η r : ℝ)
    (U V : Fin m → Euclid d) (j : Fin m) (hUV : ∀ i, i < j → U i = V i)
    (n : ℕ) (hn : n ≤ (j.val + 1) * b) :
    prefixState initial advance query b β ρ η r U n =
      prefixState initial advance query b β ρ η r V n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have heq := ih (by omega)
    have hfloor : n / b ≤ j.val := Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hb).mpr
      (show n < (j.val + 1) * b by omega))
    simp only [prefixState]
    rw [heq, prefixObjective_congr β ρ η r U V (n / b) j hfloor hUV]

def prefixBlocks {S : Type*} {m d : ℕ} (initial : S) (advance : S → ℝ → S)
    (query : S → Euclid d) (b : ℕ) (β ρ η r : ℝ) (U : Fin m → Euclid d)
    (j : Fin m) (l : Fin b) : Euclid d :=
  query (prefixState initial advance query b β ρ η r U (j.val * b + l.val))

theorem prefixBlocks_local {S : Type*} {m d b : ℕ} (initial : S) (advance : S → ℝ → S)
    (query : S → Euclid d) (hb : 0 < b) (β ρ η r : ℝ) :
    PrefixLocal (prefixBlocks (m := m) initial advance query b β ρ η r) := by
  intro U V j hUV
  funext l
  apply congrArg query
  apply prefixState_congr initial advance query hb β ρ η r U V j hUV
  simp only [Nat.add_mul, one_mul]
  have := l.isLt
  omega

theorem exists_compiled_frame {S : Type*} {m d b : ℕ} (hm : 0 < m) (hb : 0 < b)
    (initial : S) (advance : S → ℝ → S) (query : S → Euclid d)
    {β ρ η r R : ℝ} (hR : 0 < R) (hρ : 0 < ρ) (hquery : ∀ s, ‖query s‖ ≤ R)
    (hcap : 64 * R ^ 2 * Real.log (4 * ((m : ℝ) * b + 1)) ≤
      ((d : ℝ) - m - b) * ρ ^ 2) :
    ∃ U : Fin m → Euclid d, Orthonormal ℝ U ∧
      (∀ n, n < m * b →
        prefixObjective β ρ η r U (n / b) (query (prefixState initial advance query b β ρ η r U n)) =
        embeddedObjective β ρ η r U (query (prefixState initial advance query b β ρ η r U n))) ∧
      ∀ n, n < m * b →
        |frameCoordinates U (query (prefixState initial advance query b β ρ η r U n))
          ⟨m - 1, by omega⟩| ≤ ρ := by
  let B := prefixBlocks (m := m) initial advance query b β ρ η r
  obtain ⟨U, hU, hzero, hsmall⟩ := exists_delayed_frame hR hρ B
    (prefixBlocks_local initial advance query hb β ρ η r) (fun U j l => hquery _) hcap
  have hcoords (n : ℕ) (hn : n < m * b) :
      ∃ j : Fin m, j.val = n / b ∧
        ⟪U j, query (prefixState initial advance query b β ρ η r U n)⟫_ℝ = 0 ∧
        ∀ i, j < i → |⟪U i, query (prefixState initial advance query b β ρ η r U n)⟫_ℝ| ≤ ρ := by
    let j : Fin m := ⟨n / b, (Nat.div_lt_iff_lt_mul hb).mpr hn⟩
    let l : Fin b := ⟨n % b, Nat.mod_lt n hb⟩
    have heq : B U j l = query (prefixState initial advance query b β ρ η r U n) := by
      dsimp [B, prefixBlocks, j, l]
      rw [Nat.mul_comm (n / b) b, Nat.div_add_mod]
    exact ⟨j, rfl, heq ▸ hzero j l, fun i hi => heq ▸ hsmall i j hi l⟩
  refine ⟨U, hU, ?_, ?_⟩
  · intro n hn
    obtain ⟨j, hj, hz, hs⟩ := hcoords n hn
    have hshield := moreau_exact_zero_shielding hρ
      (frameCoordinates U (query (prefixState initial advance query b β ρ η r U n))) j hz hs
    unfold prefixObjective embeddedObjective
    rw [← hj]
    change (β * ρ / 8) * moreauValue ρ (truncateBefore _ j) + _ + _ = _
    rw [hshield]
    rfl
  · intro n hn
    obtain ⟨j, _, hz, hs⟩ := hcoords n hn
    let last : Fin m := ⟨m - 1, by omega⟩
    change |⟪U last, query (prefixState initial advance query b β ρ η r U n)⟫_ℝ| ≤ ρ
    by_cases hj : j = last
    · have hz' : ⟪U last, query (prefixState initial advance query b β ρ η r U n)⟫_ℝ = 0 := by
        simpa only [hj] using hz
      rw [hz', abs_zero]
      exact hρ.le
    · apply hs last
      change j.val < m - 1
      have hne : j.val ≠ m - 1 := by
        intro heq
        exact hj (Fin.ext heq)
      have := j.isLt
      omega

theorem prefixState_eq_oracle {S : Type*} {m d b : ℕ}
    (initial : S) (advance : S → ℝ → S) (query : S → Euclid d)
    (β ρ η r : ℝ) (U : Fin m → Euclid d)
    (hconsistent : ∀ n, n < m * b →
      prefixObjective β ρ η r U (n / b) (query (prefixState initial advance query b β ρ η r U n)) =
      embeddedObjective β ρ η r U (query (prefixState initial advance query b β ρ η r U n)))
    (n : ℕ) (hn : n ≤ m * b) :
    prefixState initial advance query b β ρ η r U n =
      oracleState initial advance query (embeddedObjective β ρ η r U) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [prefixState, oracleState]
    rw [hconsistent n (by omega), ih (by omega)]

theorem exists_hard_frame_for_queries {S : Type*} {m d b : ℕ} (hm : 0 < m) (hb : 0 < b)
    (initial : S) (advance : S → ℝ → S) (query : S → Euclid d)
    {β ρ η r R : ℝ} (hR : 0 < R) (hρ : 0 < ρ) (hquery : ∀ s, ‖query s‖ ≤ R)
    (hcap : 64 * R ^ 2 * Real.log (4 * ((m : ℝ) * b + 1)) ≤
      ((d : ℝ) - m - b) * ρ ^ 2) :
    ∃ U : Fin m → Euclid d, Orthonormal ℝ U ∧ ∀ n, n < m * b →
      |frameCoordinates U (query (oracleState initial advance query
        (embeddedObjective β ρ η r U) n)) ⟨m - 1, by omega⟩| ≤ ρ := by
  obtain ⟨U, hU, hc, hs⟩ := exists_compiled_frame (β := β) (η := η) (r := r)
    hm hb initial advance query hR hρ hquery hcap
  refine ⟨U, hU, ?_⟩
  intro n hn
  have heq := prefixState_eq_oracle initial advance query β ρ η r U hc n hn.le
  rw [← heq]
  exact hs n hn

end

end ExactValue
