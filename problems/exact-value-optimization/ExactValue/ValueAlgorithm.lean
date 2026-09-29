import ExactValue.IntegerLowerBound
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

open scoped ENNReal

set_option autoImplicit false

namespace ExactValue

noncomputable section

abbrev QueryBall (d : ℕ) (R : ℝ) := {x : Euclid d // ‖x‖ ≤ R}

abbrev QueryHistory (d : ℕ) (R : ℝ) (n : ℕ) := Fin n → QueryBall d R × ℝ

/-- Borel means measurability for the Borel sigma-algebras on both spaces. -/
def BorelMap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) : Prop :=
  @Measurable X Y (borel X) (borel Y) f

/-- Queries beyond T are ignored; this permits a simple total recursion for histories. -/
structure ValueAlgorithm (d : ℕ) (R : ℝ) (T : ℕ) where
  query : (n : ℕ) → QueryHistory d R n → QueryBall d R
  output : QueryHistory d R T → QueryBall d R
  query_borel : ∀ n, BorelMap (query n)
  output_borel : BorelMap output

def policyHistory {d : ℕ} {R : ℝ}
    (Q : (n : ℕ) → QueryHistory d R n → QueryBall d R) (f : Euclid d → ℝ) :
    (n : ℕ) → QueryHistory d R n
  | 0 => Fin.elim0
  | n + 1 =>
    let h := policyHistory Q f n
    let x := Q n h
    Fin.snoc h (x, f x)

def ValueAlgorithm.result {d T : ℕ} {R : ℝ} (A : ValueAlgorithm d R T) (f : Euclid d → ℝ) : Euclid d :=
  A.output (policyHistory A.query f T)

def ValueAlgorithm.Guarantees {d T : ℕ} {β R ε : ℝ} (A : ValueAlgorithm d R T) : Prop :=
  ∀ f, AdmissibleObjective d β R f → ∃ xstar : Euclid d,
    (∀ y, f xstar ≤ f y) ∧ f (A.result f) - f xstar ≤ ε

def valueComplexity (d : ℕ) (R β ε : ℝ) : ℝ≥0∞ :=
  ⨅ T : ℕ, ⨅ A : ValueAlgorithm d R T, ⨅ (_ : A.Guarantees (β := β) (ε := ε)), (T : ℝ≥0∞)

theorem valueComplexity_le {d T : ℕ} {β R ε : ℝ} (A : ValueAlgorithm d R T)
    (hA : A.Guarantees (β := β) (ε := ε)) : valueComplexity d R β ε ≤ T := by
  exact iInf_le_of_le T (iInf_le_of_le A (iInf_le_of_le hA le_rfl))

/-- Every finite list of policies in the manuscript extends to this total policy representation. -/
def ValueAlgorithm.ofFinite {d T : ℕ} {R : ℝ} (hR : 0 ≤ R)
    (Q : (n : Fin T) → QueryHistory d R n.val → QueryBall d R)
    (out : QueryHistory d R T → QueryBall d R)
    (hQ : ∀ n, BorelMap (Q n)) (hout : BorelMap out) : ValueAlgorithm d R T where
  query n h := if hn : n < T then Q ⟨n, hn⟩ h else ⟨0, by simpa using hR⟩
  output := out
  query_borel := by
    intro n
    split_ifs with hn
    · exact hQ ⟨n, hn⟩
    · exact continuous_const.borel_measurable
  output_borel := hout

abbrev HistoryState (d : ℕ) (R : ℝ) := (n : ℕ) × QueryHistory d R n

def historyQuery {d T : ℕ} {R : ℝ} (A : ValueAlgorithm d R T) (s : HistoryState d R) : Euclid d :=
  A.query s.1 s.2

def historyAdvance {d T : ℕ} {R : ℝ} (A : ValueAlgorithm d R T) (s : HistoryState d R)
    (y : ℝ) : HistoryState d R :=
  ⟨s.1 + 1, Fin.snoc s.2 (A.query s.1 s.2, y)⟩

def historyOutput {d T : ℕ} {R : ℝ} (_hR : 0 ≤ R) (A : ValueAlgorithm d R T)
    (s : HistoryState d R) : Euclid d :=
  if h : s.1 = T then A.output (h ▸ s.2) else 0

theorem historyState_eq {d T : ℕ} {R : ℝ} (A : ValueAlgorithm d R T) (f : Euclid d → ℝ) (n : ℕ) :
    oracleState (⟨0, Fin.elim0⟩ : HistoryState d R) (historyAdvance A) (historyQuery A) f n =
      ⟨n, policyHistory A.query f n⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change historyAdvance A (oracleState (⟨0, Fin.elim0⟩ : HistoryState d R)
      (historyAdvance A) (historyQuery A) f n)
      (f (historyQuery A (oracleState (⟨0, Fin.elim0⟩ : HistoryState d R)
        (historyAdvance A) (historyQuery A) f n))) = _
    rw [ih]
    rfl

theorem historyOutput_eq {d T : ℕ} {R : ℝ} (hR : 0 ≤ R) (A : ValueAlgorithm d R T)
    (f : Euclid d → ℝ) :
    historyOutput hR A (oracleState (⟨0, Fin.elim0⟩ : HistoryState d R)
      (historyAdvance A) (historyQuery A) f T) = A.result f := by
  rw [historyState_eq]
  simp [historyOutput, ValueAlgorithm.result]

theorem algorithm_integer_lower_bound {d m T : ℕ} (hd : 8 ≤ d) (hm : 0 < m)
    (hmd : 4 * m ≤ d) (hT : 8 * T < d * m) {β R : ℝ} (hβ : 0 < β) (hR : 0 < R)
    (hscale : (m : ℝ) ^ 3 * (1 + Real.log (d : ℝ)) ≤ (1 / 16777216 : ℝ) * d)
    (A : ValueAlgorithm d R T) :
    ∃ f : Euclid d → ℝ, AdmissibleObjective d β R f ∧
      ∃ xstar : Euclid d, (∀ y, f xstar ≤ f y) ∧
        11 / 131072 * (β * R ^ 2 / (m : ℝ) ^ 2) ≤ f (A.result f) - f xstar := by
  have hquery : ∀ s, ‖historyQuery A s‖ ≤ R := fun s => (A.query s.1 s.2).property
  have houtput : ∀ s, ‖historyOutput hR.le A s‖ ≤ R := by
    intro s
    unfold historyOutput
    split_ifs with h
    · exact (A.output _).property
    · simpa using hR.le
  obtain ⟨f, hf, _, _, xstar, hmin, hgap⟩ := integer_parameter_lower_bound hd hm hmd hT
    (⟨0, Fin.elim0⟩ : HistoryState d R) (historyAdvance A) (historyQuery A) (historyOutput hR.le A)
    hβ hR hquery houtput hscale
  rw [historyOutput_eq] at hgap
  exact ⟨f, hf, xstar, hmin, hgap⟩

theorem algorithm_integer_lower_bound_with_modulus {d m T : ℕ} (hd : 8 ≤ d) (hm : 0 < m)
    (hmd : 4 * m ≤ d) (hT : 8 * T < d * m) {β R : ℝ} (hβ : 0 < β) (hR : 0 < R)
    (hscale : (m : ℝ) ^ 3 * (1 + Real.log (d : ℝ)) ≤ (1 / 16777216 : ℝ) * d)
    (A : ValueAlgorithm d R T) :
    ∃ f : Euclid d → ℝ, AdmissibleObjective d β R f ∧
      StrongConvexOn Set.univ (β / (4096 * (m : ℝ) ^ 2)) f ∧
      (∀ μ, StrongConvexOn Set.univ μ f → μ ≤ β / (4096 * (m : ℝ) ^ 2)) ∧
      ∃ xstar : Euclid d, (∀ y, f xstar ≤ f y) ∧
        11 / 131072 * (β * R ^ 2 / (m : ℝ) ^ 2) ≤ f (A.result f) - f xstar := by
  have hquery : ∀ s, ‖historyQuery A s‖ ≤ R := fun s => (A.query s.1 s.2).property
  have houtput : ∀ s, ‖historyOutput hR.le A s‖ ≤ R := by
    intro s
    unfold historyOutput
    split_ifs with h
    · exact (A.output _).property
    · simpa using hR.le
  obtain ⟨f, hf, hstrong, hmax, xstar, hmin, hgap⟩ := integer_parameter_lower_bound hd hm hmd hT
    (⟨0, Fin.elim0⟩ : HistoryState d R) (historyAdvance A) (historyQuery A) (historyOutput hR.le A)
    hβ hR hquery houtput hscale
  rw [historyOutput_eq] at hgap
  exact ⟨f, hf, hstrong, hmax, xstar, hmin, hgap⟩

end

end ExactValue
