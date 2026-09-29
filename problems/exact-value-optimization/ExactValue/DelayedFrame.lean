import ExactValue.DirectionSelection

open scoped InnerProductSpace

set_option autoImplicit false

namespace ExactValue

noncomputable section

def PrefixLocal {m b d : ℕ}
    (B : (Fin m → Euclid d) → Fin m → Fin b → Euclid d) : Prop :=
  ∀ U V j, (∀ i, i < j → U i = V i) → B U j = B V j

structure PartialDelayedFrame {m b d : ℕ}
    (B : (Fin m → Euclid d) → Fin m → Fin b → Euclid d)
    (ρ : ℝ) (k : ℕ) (U : Fin m → Euclid d) : Prop where
  unit : ∀ i, i.val < k → ‖U i‖ = 1
  orthogonal : ∀ i j, i.val < k → j.val < k → i ≠ j → ⟪U i, U j⟫_ℝ = 0
  current : ∀ i, i.val < k → ∀ l, ⟪U i, B U i l⟫_ℝ = 0
  previous : ∀ i, i.val < k → ∀ j, j < i → ∀ l, |⟪U i, B U j l⟫_ℝ| ≤ ρ

theorem prefixLocal_update {m b d : ℕ}
    {B : (Fin m → Euclid d) → Fin m → Fin b → Euclid d} (hB : PrefixLocal B)
    (U : Fin m → Euclid d) (i j : Fin m) (hji : j ≤ i) (v : Euclid d) :
    B (Function.update U i v) j = B U j := by
  apply hB
  intro t ht
  exact Function.update_of_ne (ne_of_lt (ht.trans_le hji)) _ _

theorem delayed_frame_step {m b d k : ℕ} {R ρ : ℝ}
    (hk : k < m) (hR : 0 < R) (hρ : 0 < ρ)
    {B : (Fin m → Euclid d) → Fin m → Fin b → Euclid d}
    (hB : PrefixLocal B) (hbounded : ∀ U j l, ‖B U j l‖ ≤ R)
    (hcap : 64 * R ^ 2 * Real.log (4 * ((m : ℝ) * b + 1)) ≤
      ((d : ℝ) - m - b) * ρ ^ 2)
    {U : Fin m → Euclid d} (hU : PartialDelayedFrame B ρ k U) :
    ∃ V : Fin m → Euclid d, PartialDelayedFrame B ρ (k + 1) V := by
  let i : Fin m := ⟨k, hk⟩
  let f : Fin k ⊕ Fin b → Euclid d := Sum.elim
    (fun j => U ⟨j.val, j.isLt.trans hk⟩) (B U i)
  let a : Fin m × Fin b → Euclid d := fun q => B U q.1 q.2
  have hdim : (d : ℝ) - m - b ≤ (d : ℝ) - Fintype.card (Fin k ⊕ Fin b) := by
    simp only [Fintype.card_sum, Fintype.card_fin, Nat.cast_add]
    have : (k : ℝ) ≤ m := by exact_mod_cast hk.le
    linarith
  have hcap' : 64 * R ^ 2 * Real.log (4 * ((Fintype.card (Fin m × Fin b) : ℝ) + 1)) ≤
      ((d : ℝ) - Fintype.card (Fin k ⊕ Fin b)) * ρ ^ 2 := by
    simpa only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul] using
      hcap.trans (mul_le_mul_of_nonneg_right hdim (sq_nonneg ρ))
  obtain ⟨v, hv, horth, hsmall⟩ := exists_unit_orthogonal_small f a hR hρ
    (fun q => hbounded U q.1 q.2) hcap'
  let V := Function.update U i v
  have hnew : V i = v := Function.update_self _ _ _
  have hold : ∀ j : Fin m, j ≠ i → V j = U j := fun j hj => Function.update_of_ne hj _ _
  have hblocks : ∀ j : Fin m, j ≤ i → B V j = B U j :=
    fun j hj => prefixLocal_update hB U i j hj v
  have horthold : ∀ j : Fin m, j < i → ⟪v, U j⟫_ℝ = 0 := by
    intro j hj
    exact horth (Sum.inl ⟨j.val, hj⟩)
  refine ⟨V, ?_, ?_, ?_, ?_⟩
  · intro j hj
    by_cases hji : j = i
    · simpa [hji, hnew] using hv
    · rw [hold j hji]
      exact hU.unit j (by have := (Fin.ne_iff_vne _ _).mp hji; dsimp [i] at this; omega)
  · intro j t hj ht hjt
    by_cases hji : j = i
    · subst j
      rw [hnew, hold t (Ne.symm hjt)]
      exact horthold t (by
        change t.val < k
        have := (Fin.ne_iff_vne _ _).mp (Ne.symm hjt)
        dsimp [i] at this
        omega)
    · by_cases hti : t = i
      · subst t
        rw [hold j hji, hnew, real_inner_comm]
        exact horthold j (by
          change j.val < k
          have := (Fin.ne_iff_vne _ _).mp hji
          dsimp [i] at this
          omega)
      · rw [hold j hji, hold t hti]
        exact hU.orthogonal j t
          (by have := (Fin.ne_iff_vne _ _).mp hji; dsimp [i] at *; omega)
          (by have := (Fin.ne_iff_vne _ _).mp hti; dsimp [i] at *; omega) hjt
  · intro j hj l
    rw [hblocks j (by change j.val ≤ k; omega)]
    by_cases hji : j = i
    · subst j
      rw [hnew]
      exact horth (Sum.inr l)
    · rw [hold j hji]
      exact hU.current j (by have := (Fin.ne_iff_vne _ _).mp hji; dsimp [i] at *; omega) l
  · intro j hj t ht l
    rw [hblocks t (by change t.val ≤ k; have := ht; change t.val < j.val at this; omega)]
    by_cases hji : j = i
    · subst j
      rw [hnew]
      exact hsmall (t, l)
    · rw [hold j hji]
      exact hU.previous j (by have := (Fin.ne_iff_vne _ _).mp hji; dsimp [i] at *; omega) t ht l

/-- Every prefix-dependent sequence of query blocks admits a completed orthonormal frame
that is exactly orthogonal on its current block and small on all earlier blocks. -/
theorem exists_delayed_frame {m b d : ℕ} {R ρ : ℝ} (hR : 0 < R) (hρ : 0 < ρ)
    (B : (Fin m → Euclid d) → Fin m → Fin b → Euclid d)
    (hB : PrefixLocal B) (hbounded : ∀ U j l, ‖B U j l‖ ≤ R)
    (hcap : 64 * R ^ 2 * Real.log (4 * ((m : ℝ) * b + 1)) ≤
      ((d : ℝ) - m - b) * ρ ^ 2) :
    ∃ U : Fin m → Euclid d, Orthonormal ℝ U ∧
      (∀ j l, ⟪U j, B U j l⟫_ℝ = 0) ∧
      ∀ i j, j < i → ∀ l, |⟪U i, B U j l⟫_ℝ| ≤ ρ := by
  have hstage : ∀ k, k ≤ m → ∃ U : Fin m → Euclid d, PartialDelayedFrame B ρ k U := by
    intro k hk
    induction k with
    | zero =>
      refine ⟨fun _ => 0, ?_, ?_, ?_, ?_⟩ <;> intros <;> omega
    | succ k ih =>
      obtain ⟨U, hU⟩ := ih (by omega)
      exact delayed_frame_step (by omega) hR hρ hB hbounded hcap hU
  obtain ⟨U, hU⟩ := hstage m le_rfl
  refine ⟨U, ?_, fun j l => hU.current j j.isLt l,
    fun i j hji l => hU.previous i i.isLt j hji l⟩
  exact ⟨fun i => hU.unit i i.isLt, fun i j hij => hU.orthogonal i j i.isLt j.isLt hij⟩

end

end ExactValue
