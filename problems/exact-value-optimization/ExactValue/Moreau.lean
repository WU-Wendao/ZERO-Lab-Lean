import ExactValue.Chain

/-! Identification of the simplex dual with the primal Moreau infimum.
The quadratic norm is written as the finite sum of squared coordinates. -/

open Finset

set_option autoImplicit false

namespace ExactValue

noncomputable section

def maxAffine {m : ℕ} (ρ : ℝ) (y : Vec m) : ℝ :=
  sSup (Set.range (fun i => y i - 8 * ρ * (i.val + 1)))

def primalObjective {m : ℕ} (ρ : ℝ) (y z : Vec m) : ℝ :=
  maxAffine ρ z + (∑ i, (z i - y i) ^ 2) / ρ

def moreauValue {m : ℕ} (ρ : ℝ) (y : Vec m) : ℝ :=
  sInf (Set.range (primalObjective ρ y))

theorem coord_le_maxAffine {m : ℕ} (ρ : ℝ) (y : Vec m) (i : Fin m) :
    y i - 8 * ρ * (i.val + 1) ≤ maxAffine ρ y := by
  apply le_csSup (Set.finite_range _).bddAbove
  exact ⟨i, rfl⟩

theorem maxAffine_le {m : ℕ} (hm : 0 < m) (ρ : ℝ) (y : Vec m) (b : ℝ)
    (hb : ∀ i, y i - 8 * ρ * (i.val + 1) ≤ b) : maxAffine ρ y ≤ b := by
  unfold maxAffine
  apply csSup_le
  · exact ⟨_, ⟨⟨0, hm⟩, rfl⟩⟩
  · rintro _ ⟨i, rfl⟩
    exact hb i

theorem weighted_le_maxAffine {m : ℕ} (ρ : ℝ) (y : Vec m) {p : Vec m}
    (hp : p ∈ simplex m) :
    (∑ i, p i * (y i - 8 * ρ * (i.val + 1))) ≤ maxAffine ρ y := by
  calc
    _ ≤ ∑ i, p i * maxAffine ρ y := Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (coord_le_maxAffine ρ y i) (hp.1 i)
    _ = maxAffine ρ y := by rw [← Finset.sum_mul, hp.2, one_mul]

theorem scalar_weak_duality {ρ c y z p : ℝ} (hρ : 0 < ρ) :
    p * (y - c) - ρ / 4 * p ^ 2 ≤ p * (z - c) + (z - y) ^ 2 / ρ := by
  have heq : ((z - y) ^ 2 / ρ) * ρ = (z - y) ^ 2 := div_mul_cancel₀ _ hρ.ne'
  have hsq := sq_nonneg (z - y + ρ / 2 * p)
  nlinarith

theorem weak_duality {m : ℕ} {ρ : ℝ} (hρ : 0 < ρ) (y z : Vec m) {p : Vec m}
    (hp : p ∈ simplex m) : dualObjective ρ y p ≤ primalObjective ρ y z := by
  calc
    dualObjective ρ y p ≤
        ∑ i, (p i * (z i - 8 * ρ * (i.val + 1)) + (z i - y i) ^ 2 / ρ) := by
      exact Finset.sum_le_sum fun i _ => scalar_weak_duality hρ
    _ = (∑ i, p i * (z i - 8 * ρ * (i.val + 1))) + (∑ i, (z i - y i) ^ 2) / ρ := by
      rw [Finset.sum_add_distrib, Finset.sum_div]
    _ ≤ primalObjective ρ y z := by
      exact add_le_add_right (weighted_le_maxAffine ρ z hp) _

/-- An elementary one-sided first-order test for a quadratic on [0,1]. -/
theorem quadratic_first_order {a b : ℝ} (hb : 0 ≤ b)
    (h : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t * a - b * t ^ 2 ≤ 0) : a ≤ 0 := by
  by_contra ha
  have ha : 0 < a := lt_of_not_ge ha
  let t := min 1 (a / (2 * (b + 1)))
  have ht : 0 < t := lt_min (by norm_num) (by positivity)
  have ht1 : t ≤ 1 := min_le_left _ _
  have ht2 : t * (2 * (b + 1)) ≤ a :=
    (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  have hq := h t ht.le ht1
  have hpos : 0 < a - b * t := by nlinarith
  have := mul_pos ht hpos
  nlinarith

theorem dualObjective_segment {m : ℕ} (ρ t : ℝ) (y p q : Vec m) :
    dualObjective ρ y (fun i => p i + t * (q i - p i)) - dualObjective ρ y p =
      t * (∑ i, (q i - p i) * (y i - 8 * ρ * (i.val + 1) - ρ / 2 * p i)) -
        (ρ / 4 * t ^ 2) * (∑ i, (q i - p i) ^ 2) := by
  unfold dualObjective
  rw [← Finset.sum_sub_distrib]
  calc
    _ = ∑ i, (t * ((q i - p i) * (y i - 8 * ρ * (i.val + 1) - ρ / 2 * p i)) -
        (ρ / 4 * t ^ 2) * (q i - p i) ^ 2) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by rw [Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]

theorem dualMax_variational {m : ℕ} {ρ : ℝ} (hρ : 0 < ρ) {y p : Vec m}
    (hp : IsDualMax ρ y p) {q : Vec m} (hq : q ∈ simplex m) :
    (∑ i, (q i - p i) * (y i - 8 * ρ * (i.val + 1) - ρ / 2 * p i)) ≤ 0 := by
  apply quadratic_first_order (b := ρ / 4 * ∑ i, (q i - p i) ^ 2) (by positivity)
  intro t ht ht1
  have hmix : (fun i => p i + t * (q i - p i)) ∈ simplex m := by
    have hc := (convex_stdSimplex ℝ (Fin m)) hp.1 hq
      (show 0 ≤ 1 - t by linarith) ht (show (1 - t) + t = 1 by ring)
    convert hc using 1
    ext i
    simp
    ring
  have ho := hp.2 _ hmix
  have heq := dualObjective_segment ρ t y p q
  nlinarith

theorem dualMax_coordinate_condition {m : ℕ} {ρ : ℝ} (hρ : 0 < ρ) {y p : Vec m}
    (hp : IsDualMax ρ y p) (j : Fin m) :
    y j - 8 * ρ * (j.val + 1) - ρ / 2 * p j ≤
      ∑ i, p i * (y i - 8 * ρ * (i.val + 1) - ρ / 2 * p i) := by
  classical
  have hv := dualMax_variational hρ hp (single_mem_stdSimplex ℝ j)
  simp_rw [sub_mul] at hv
  rw [Finset.sum_sub_distrib] at hv
  simp at hv
  simpa [Pi.single_apply, ite_mul] using hv

def primalCandidate {m : ℕ} (ρ : ℝ) (y p : Vec m) : Vec m :=
  fun i => y i - ρ / 2 * p i

theorem primalCandidate_attains {m : ℕ} (hm : 0 < m) {ρ : ℝ} (hρ : 0 < ρ)
    {y p : Vec m} (hp : IsDualMax ρ y p) :
    primalObjective ρ y (primalCandidate ρ y p) = dualObjective ρ y p := by
  have hg : maxAffine ρ (primalCandidate ρ y p) =
      ∑ i, p i * (y i - 8 * ρ * (i.val + 1) - ρ / 2 * p i) := by
    apply le_antisymm
    · apply maxAffine_le hm
      intro i
      convert dualMax_coordinate_condition hρ hp i using 1
      simp only [primalCandidate]
      ring
    · convert weighted_le_maxAffine ρ (primalCandidate ρ y p) hp.1 using 1
      apply Finset.sum_congr rfl
      intro i _
      simp only [primalCandidate]
      ring
  unfold primalObjective
  rw [hg, Finset.sum_div, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [primalCandidate]
  field_simp
  ring

/-- The paper's simplex dual representation, with the Moreau parameter rho/2. -/
theorem moreau_eq_dual {m : ℕ} (hm : 0 < m) {ρ : ℝ} (hρ : 0 < ρ) (y : Vec m) :
    moreauValue ρ y = dualValue ρ y := by
  obtain ⟨p, hp⟩ := exists_dualMax hm ρ y
  rw [dualValue_eq_of_max hp]
  apply IsLeast.csInf_eq
  constructor
  · exact ⟨primalCandidate ρ y p, primalCandidate_attains hm hρ hp⟩
  · rintro _ ⟨z, rfl⟩
    exact weak_duality hρ y z hp.1

theorem moreau_exact_prefix_shielding {m : ℕ} {ρ : ℝ} (hρ : 0 < ρ)
    (y : Vec m) (j : Fin m) (hwindow : ∀ k, j ≤ k → |y k| ≤ ρ) :
    moreauValue ρ y = moreauValue ρ (truncateAfter y j) := by
  have hm := Nat.zero_lt_of_lt j.isLt
  rw [moreau_eq_dual hm hρ, moreau_eq_dual hm hρ]
  exact exact_prefix_shielding hρ y j hwindow

theorem moreau_exact_zero_shielding {m : ℕ} {ρ : ℝ} (hρ : 0 < ρ)
    (y : Vec m) (j : Fin m) (hj : y j = 0)
    (hwindow : ∀ k, j < k → |y k| ≤ ρ) :
    moreauValue ρ y = moreauValue ρ (truncateBefore y j) := by
  have hm := Nat.zero_lt_of_lt j.isLt
  rw [moreau_eq_dual hm hρ, moreau_eq_dual hm hρ]
  exact exact_zero_shielding hρ y j hj hwindow

theorem simplex_sq_sum_le_one {m : ℕ} {p : Vec m} (hp : p ∈ simplex m) :
    (∑ i, (p i) ^ 2) ≤ 1 := by
  calc
    _ ≤ ∑ i, p i := by
      apply Finset.sum_le_sum
      intro i _
      have h0 := hp.1 i
      have h1 := simplex_coord_le_one hp i
      nlinarith
    _ = 1 := hp.2

theorem moreau_approximation {m : ℕ} (hm : 0 < m) {ρ : ℝ} (hρ : 0 < ρ)
    (y : Vec m) : 0 ≤ maxAffine ρ y - moreauValue ρ y ∧
      maxAffine ρ y - moreauValue ρ y ≤ ρ / 4 := by
  rw [moreau_eq_dual hm hρ]
  constructor
  · apply sub_nonneg.mpr
    exact dualValue_le_of_coordinates hm hρ.le y (coord_le_maxAffine ρ y)
  · have hg : maxAffine ρ y ≤ dualValue ρ y + ρ / 4 := by
      apply maxAffine_le hm
      intro i
      have := coordinate_lower_bound ρ y i
      linarith
    linarith

theorem primalCandidate_radius_sq {m : ℕ} {ρ : ℝ} (y : Vec m) {p : Vec m}
    (hp : p ∈ simplex m) :
    (∑ i, (primalCandidate ρ y p i - y i) ^ 2) ≤ ρ ^ 2 / 4 := by
  calc
    _ = ρ ^ 2 / 4 * ∑ i, (p i) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp only [primalCandidate]
      ring
    _ ≤ ρ ^ 2 / 4 * 1 := mul_le_mul_of_nonneg_left (simplex_sq_sum_le_one hp) (by positivity)
    _ = ρ ^ 2 / 4 := mul_one _

theorem dualMax_strong {m : ℕ} {ρ : ℝ} (hρ : 0 < ρ) {y p : Vec m}
    (hp : IsDualMax ρ y p) {q : Vec m} (hq : q ∈ simplex m) :
    dualObjective ρ y q + ρ / 4 * (∑ i, (q i - p i) ^ 2) ≤ dualObjective ρ y p := by
  have hv := dualMax_variational hρ hp hq
  have he := dualObjective_segment ρ 1 y p q
  simp only [one_mul, one_pow, mul_one, add_sub_cancel] at he
  linarith

theorem dualMax_unique {m : ℕ} {ρ : ℝ} (hρ : 0 < ρ) {y p q : Vec m}
    (hp : IsDualMax ρ y p) (hq : IsDualMax ρ y q) : p = q := by
  have hs := dualMax_strong hρ hp hq.1
  have hv := hq.2 p hp.1
  have hnonneg : 0 ≤ ∑ i, (q i - p i) ^ 2 := by positivity
  have hsum : (∑ i, (q i - p i) ^ 2) = 0 := by nlinarith
  funext i
  have hi : (q i - p i) ^ 2 ≤ ∑ j, (q j - p j) ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg (q j - p j)) (Finset.mem_univ i)
  rw [hsum] at hi
  nlinarith [sq_nonneg (q i - p i)]

theorem dualObjective_change_input {m : ℕ} (ρ : ℝ) (y z p : Vec m) :
    dualObjective ρ z p = dualObjective ρ y p + ∑ i, p i * (z i - y i) := by
  rw [dualObjective, dualObjective, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- A two-sided quadratic first-order model, with the dual optimizer as gradient candidate. -/
theorem moreau_quadratic_model {m : ℕ} (hm : 0 < m) {ρ : ℝ} (hρ : 0 < ρ)
    {y p : Vec m} (hp : IsDualMax ρ y p) (z : Vec m) :
    0 ≤ moreauValue ρ z - moreauValue ρ y - (∑ i, p i * (z i - y i)) ∧
    moreauValue ρ z - moreauValue ρ y - (∑ i, p i * (z i - y i)) ≤
      (∑ i, (z i - y i) ^ 2) / ρ := by
  obtain ⟨q, hq⟩ := exists_dualMax hm ρ z
  rw [moreau_eq_dual hm hρ, moreau_eq_dual hm hρ,
    dualValue_eq_of_max hp, dualValue_eq_of_max hq]
  constructor
  · have hl := hq.2 p hp.1
    rw [dualObjective_change_input ρ y z p] at hl
    linarith
  · have hs := dualMax_strong hρ hp hq.1
    have he := dualObjective_change_input ρ y z q
    have hscalar :
        (∑ i, (q i - p i) * (z i - y i)) - ρ / 4 * (∑ i, (q i - p i) ^ 2) ≤
          (∑ i, (z i - y i) ^ 2) / ρ := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
      apply Finset.sum_le_sum
      intro i _
      simpa only [sub_zero, mul_zero, zero_sub, neg_sq, zero_add] using
        (scalar_weak_duality (c := 0) (y := z i - y i) (z := 0)
        (p := q i - p i) hρ)
    have hlin : (∑ i, (q i - p i) * (z i - y i)) =
        (∑ i, q i * (z i - y i)) - (∑ i, p i * (z i - y i)) := by
      simp only [sub_mul, Finset.sum_sub_distrib]
    rw [hlin] at hscalar
    linarith

theorem moreau_progress_gap {m : ℕ} (hm : 0 < m) {ρ R0 s : ℝ}
    (hR0 : 0 < R0) (hs : 0 < s)
    (hρ : ρ = R0 / (64 * (m : ℝ) * s)) (y : Vec m)
    (hfinal : |y ⟨m - 1, by omega⟩| ≤ ρ) :
    3 * R0 / (4 * s) ≤ moreauValue ρ y - moreauValue ρ (fun _ : Fin m => -(R0 / s)) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hρpos : 0 < ρ := by rw [hρ]; positivity
  rw [moreau_eq_dual hm hρpos, moreau_eq_dual hm hρpos]
  exact progress_gap hm hR0 hs hρ y hfinal

end

end ExactValue
