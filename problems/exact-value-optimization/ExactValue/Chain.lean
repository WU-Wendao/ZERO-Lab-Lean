import Mathlib.Analysis.Convex.Topology
import Mathlib.Tactic

/-!
The simplex dual and exact prefix shielding from source/main.tex.
Indices are zero based internally; the affine bias uses i.val + 1.
This module defines the dual value directly. Its identification with the
primal Moreau infimum is proved in ExactValue/Moreau.lean.
-/

open Finset

set_option autoImplicit false

namespace ExactValue

noncomputable section

abbrev Vec (m : ℕ) := Fin m → ℝ

def simplex (m : ℕ) : Set (Vec m) := stdSimplex ℝ (Fin m)

def dualObjective {m : ℕ} (ρ : ℝ) (y p : Vec m) : ℝ :=
  ∑ i, (p i * (y i - 8 * ρ * (i.val + 1)) - ρ / 4 * (p i) ^ 2)

def IsDualMax {m : ℕ} (ρ : ℝ) (y p : Vec m) : Prop :=
  p ∈ simplex m ∧ ∀ q ∈ simplex m, dualObjective ρ y q ≤ dualObjective ρ y p

theorem simplex_coord_nonneg {m : ℕ} {p : Vec m} (hp : p ∈ simplex m) (i) :
    0 ≤ p i := hp.1 i

theorem simplex_coord_le_one {m : ℕ} {p : Vec m} (hp : p ∈ simplex m) (i) :
    p i ≤ 1 := by
  exact (mem_Icc_of_mem_stdSimplex hp i).2

theorem dualObjective_continuous {m : ℕ} (ρ : ℝ) (y : Vec m) :
    Continuous (dualObjective ρ y) := by
  unfold dualObjective
  fun_prop

theorem exists_dualMax {m : ℕ} (hm : 0 < m) (ρ : ℝ) (y : Vec m) :
    ∃ p, IsDualMax ρ y p := by
  obtain ⟨p, hp, hmax⟩ := (isCompact_stdSimplex (Fin m)).exists_isMaxOn
    ⟨Pi.single ⟨0, hm⟩ 1, single_mem_stdSimplex ℝ _⟩
    (dualObjective_continuous ρ y).continuousOn
  exact ⟨p, hp, hmax⟩

noncomputable def dualValue {m : ℕ} (ρ : ℝ) (y : Vec m) : ℝ :=
  sSup (dualObjective ρ y '' simplex m)

theorem dualValue_eq_of_max {m : ℕ} {ρ : ℝ} {y p : Vec m}
    (hp : IsDualMax ρ y p) : dualValue ρ y = dualObjective ρ y p := by
  apply IsGreatest.csSup_eq
  exact ⟨⟨p, hp.1, rfl⟩, by rintro _ ⟨q, hq, rfl⟩; exact hp.2 q hq⟩

def moveMass {m : ℕ} (p : Vec m) (j k : Fin m) : Vec m :=
  Function.update (Function.update p j (p j + p k)) k 0

theorem sum_moveMass {m : ℕ} (p : Vec m) (j k : Fin m) (hjk : j ≠ k)
    (f : Fin m → ℝ → ℝ) :
    (∑ i, f i (moveMass p j k i)) =
      (∑ i, f i (p i)) + (f j (p j + p k) - f j (p j)) + (f k 0 - f k (p k)) := by
  classical
  have h : (fun i => f i (moveMass p j k i)) =
      Function.update (Function.update (fun i => f i (p i)) j (f j (p j + p k))) k (f k 0) := by
    funext i
    by_cases hi : i = k
    · subst i
      simp [moveMass]
    · by_cases hi' : i = j
      · subst i
        simp [moveMass, hjk]
      · simp [moveMass, hi, hi']
  have hu (g : Fin m → ℝ) (i : Fin m) (v : ℝ) :
      (∑ l, Function.update g i v l) = (∑ l, g l) + v - g i := by
    have hd : (∑ l, (Function.update g i v l - g l)) = v - g i := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro l _ hli
        simp [hli]
      · simp
    rw [Finset.sum_sub_distrib] at hd
    linarith
  rw [h, hu, hu]
  simp [hjk.symm]
  ring

theorem moveMass_mem {m : ℕ} {p : Vec m} (hp : p ∈ simplex m)
    (j k : Fin m) (hjk : j ≠ k) : moveMass p j k ∈ simplex m := by
  constructor
  · intro i
    by_cases hi : i = k
    · subst i
      simp [moveMass]
    · by_cases hi' : i = j
      · subst i
        simpa [moveMass, hjk] using add_nonneg (hp.1 j) (hp.1 k)
      · simpa [moveMass, hi, hi'] using hp.1 i
  · rw [sum_moveMass p j k hjk (fun _ x => x), hp.2]
    ring

theorem dualObjective_moveMass {m : ℕ} (ρ : ℝ) (y p : Vec m)
    (j k : Fin m) (hjk : j ≠ k) :
    dualObjective ρ y (moveMass p j k) - dualObjective ρ y p =
      p k * ((y j - 8 * ρ * (j.val + 1)) - (y k - 8 * ρ * (k.val + 1))) -
        ρ / 2 * p j * p k := by
  unfold dualObjective
  rw [sum_moveMass p j k hjk (fun i x =>
    x * (y i - 8 * ρ * (i.val + 1)) - ρ / 4 * x ^ 2)]
  ring

theorem biased_gap {m : ℕ} {ρ : ℝ} (hρ : 0 < ρ) (y : Vec m)
    (j k : Fin m) (hjk : j < k) (hj : |y j| ≤ ρ) (hk : |y k| ≤ ρ) :
    6 * ρ ≤ (y j - 8 * ρ * (j.val + 1)) - (y k - 8 * ρ * (k.val + 1)) := by
  have hnat : j.val + 1 ≤ k.val := hjk
  have hreal : (j.val : ℝ) + 1 ≤ k.val := by exact_mod_cast hnat
  obtain ⟨hjlow, _⟩ := abs_le.mp hj
  obtain ⟨_, hkup⟩ := abs_le.mp hk
  nlinarith

/-- Every dual maximizer is supported on the prefix ending at j. -/
theorem dualMax_tail_zero {m : ℕ} {ρ : ℝ} (hρ : 0 < ρ) {y p : Vec m}
    (hp : IsDualMax ρ y p) (j : Fin m)
    (hwindow : ∀ k, j ≤ k → |y k| ≤ ρ) :
    ∀ k, j < k → p k = 0 := by
  intro k hjk
  by_contra hne
  have hpk : 0 < p k := lt_of_le_of_ne (hp.1.1 k) (Ne.symm hne)
  have hpj := simplex_coord_le_one hp.1 j
  have hgap := biased_gap hρ y j k hjk (hwindow j le_rfl) (hwindow k hjk.le)
  have hopt := hp.2 (moveMass p j k) (moveMass_mem hp.1 j k (ne_of_lt hjk))
  have hdiff := dualObjective_moveMass ρ y p j k (ne_of_lt hjk)
  have hstrict : 0 <
      (y j - 8 * ρ * (j.val + 1)) - (y k - 8 * ρ * (k.val + 1)) - ρ / 2 * p j := by
    nlinarith
  have := mul_pos hpk hstrict
  nlinarith

def truncateAfter {m : ℕ} (y : Vec m) (j : Fin m) : Vec m :=
  fun k => if k ≤ j then y k else 0

theorem dualObjective_prefix {m : ℕ} (ρ : ℝ) (y p : Vec m) (j : Fin m)
    (hsupp : ∀ k, j < k → p k = 0) :
    dualObjective ρ (truncateAfter y j) p = dualObjective ρ y p := by
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : k ≤ j
  · simp [truncateAfter, hk]
  · simp [truncateAfter, hk, hsupp k (lt_of_not_ge hk)]

/-- The paper's exact shielding identity, for the simplex dual value. -/
theorem exact_prefix_shielding {m : ℕ} {ρ : ℝ} (hρ : 0 < ρ)
    (y : Vec m) (j : Fin m) (hwindow : ∀ k, j ≤ k → |y k| ≤ ρ) :
    dualValue ρ y = dualValue ρ (truncateAfter y j) := by
  have hm : 0 < m := Nat.zero_lt_of_lt j.isLt
  obtain ⟨p, hp⟩ := exists_dualMax hm ρ y
  obtain ⟨q, hq⟩ := exists_dualMax hm ρ (truncateAfter y j)
  have hwindow' : ∀ k, j ≤ k → |truncateAfter y j k| ≤ ρ := by
    intro k hk
    by_cases hkj : k ≤ j
    · simp only [truncateAfter, if_pos hkj]
      exact hwindow k hk
    · simp [truncateAfter, hkj, hρ.le]
  have hpp := dualObjective_prefix ρ y p j (dualMax_tail_zero hρ hp j hwindow)
  have hqp := dualObjective_prefix ρ y q j (dualMax_tail_zero hρ hq j hwindow')
  rw [dualValue_eq_of_max hp, dualValue_eq_of_max hq]
  apply le_antisymm
  · rw [← hpp]
    exact hq.2 p hp.1
  · rw [hqp]
    exact hp.2 q hq.1

def truncateBefore {m : ℕ} (y : Vec m) (j : Fin m) : Vec m :=
  fun k => if k < j then y k else 0

theorem exact_zero_shielding {m : ℕ} {ρ : ℝ} (hρ : 0 < ρ)
    (y : Vec m) (j : Fin m) (hj : y j = 0)
    (hwindow : ∀ k, j < k → |y k| ≤ ρ) :
    dualValue ρ y = dualValue ρ (truncateBefore y j) := by
  have hw : ∀ k, j ≤ k → |y k| ≤ ρ := by
    intro k hk
    rcases eq_or_lt_of_le hk with rfl | hlt
    · simpa [hj] using hρ.le
    · exact hwindow k hlt
  rw [exact_prefix_shielding hρ y j hw]
  congr 1
  funext k
  rcases lt_trichotomy k j with hk | rfl | hk
  · simp [truncateAfter, truncateBefore, hk, hk.le]
  · simp [truncateAfter, truncateBefore, hj]
  · simp [truncateAfter, truncateBefore, not_le.mpr hk, not_lt.mpr hk.le]

theorem dualObjective_vertex {m : ℕ} (ρ : ℝ) (y : Vec m) (j : Fin m) :
    dualObjective ρ y (Pi.single j 1) = y j - 8 * ρ * (j.val + 1) - ρ / 4 := by
  classical
  unfold dualObjective
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hkj
    simp [Pi.single_apply, hkj]
  · simp

theorem coordinate_lower_bound {m : ℕ} (ρ : ℝ) (y : Vec m) (j : Fin m) :
    y j - 8 * ρ * (j.val + 1) - ρ / 4 ≤ dualValue ρ y := by
  obtain ⟨p, hp⟩ := exists_dualMax (Nat.zero_lt_of_lt j.isLt) ρ y
  rw [dualValue_eq_of_max hp, ← dualObjective_vertex ρ y j]
  exact hp.2 _ (single_mem_stdSimplex ℝ j)

theorem dualValue_le_of_coordinates {m : ℕ} (hm : 0 < m) {ρ b : ℝ}
    (hρ : 0 ≤ ρ) (y : Vec m)
    (hcoord : ∀ j, y j - 8 * ρ * (j.val + 1) ≤ b) : dualValue ρ y ≤ b := by
  obtain ⟨p, hp⟩ := exists_dualMax hm ρ y
  rw [dualValue_eq_of_max hp]
  calc
    dualObjective ρ y p ≤ ∑ j, p j * b := by
      apply Finset.sum_le_sum
      intro j _
      have h1 := mul_le_mul_of_nonneg_left (hcoord j) (hp.1.1 j)
      have h2 : 0 ≤ ρ / 4 * (p j) ^ 2 := by positivity
      linarith
    _ = b := by rw [← Finset.sum_mul, hp.1.2, one_mul]

theorem constant_vector_upper {m : ℕ} (hm : 0 < m) {ρ v : ℝ} (hρ : 0 ≤ ρ) :
    dualValue ρ (fun _ : Fin m => v) ≤ v - 8 * ρ := by
  apply dualValue_le_of_coordinates hm hρ
  intro j
  have : (0 : ℝ) ≤ j.val := by positivity
  nlinarith

/-- The progress gap before the last coordinate, with sqrt(m) supplied as s.
The chosen rho is the manuscript's R0 / (64 m^(3/2)). -/
theorem progress_gap {m : ℕ} (hm : 0 < m) {ρ R0 s : ℝ}
    (hR0 : 0 < R0) (hs : 0 < s)
    (hρ : ρ = R0 / (64 * (m : ℝ) * s)) (y : Vec m)
    (hfinal : |y ⟨m - 1, by omega⟩| ≤ ρ) :
    3 * R0 / (4 * s) ≤ dualValue ρ y - dualValue ρ (fun _ : Fin m => -(R0 / s)) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hρpos : 0 < ρ := by rw [hρ]; positivity
  have hlow := coordinate_lower_bound ρ y ⟨m - 1, by omega⟩
  have hupp := constant_vector_upper (v := -(R0 / s)) hm hρpos.le
  simp only [neg_div] at hupp
  have hidx : ((m - 1 : ℕ) : ℝ) + 1 = m := by
    exact_mod_cast (show m - 1 + 1 = m by omega)
  simp only at hlow
  rw [hidx] at hlow
  have hlast := (abs_le.mp hfinal).1
  have hid : 8 * (m : ℝ) * ρ = R0 / (8 * s) := by
    rw [hρ]
    field_simp
    ring
  have hgap : R0 / s - 8 * (m : ℝ) * ρ ≤
      dualValue ρ y - dualValue ρ (fun _ : Fin m => -(R0 / s)) := by nlinarith
  rw [hid] at hgap
  have hdiv : R0 / s - R0 / (8 * s) = 7 * R0 / (8 * s) := by ring
  rw [hdiv] at hgap
  have hpos : 0 ≤ R0 / s := by positivity
  have heq : 7 * R0 / (8 * s) = 7 / 8 * (R0 / s) := by ring
  have heq' : 3 * R0 / (4 * s) = 3 / 4 * (R0 / s) := by ring
  rw [heq] at hgap
  rw [heq']
  linarith

end

end ExactValue
