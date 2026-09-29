# Smooth convex optimization with exact function values

**English** | [简体中文](README.zh-CN.md)

This project formalizes the main upper bound, the integer-parameter and dimension–accuracy lower bounds, the matching corollary, the two accuracy regimes, and the supporting lemmas in *Near-Optimal Deterministic Exact-Value Complexity for Smooth Convex Optimization*. All 20 named mathematical results in the manuscript have corresponding proofs, including both appendix lemmas. See the [coverage map](proof/COVERAGE.md) for individual entry points.

The model is deterministic, adaptive zeroth-order optimization with an exact function-value oracle. At each iteration, the upper-bound algorithm takes finite differences along all coordinate directions and then performs an accelerated projected update. The lower bound covers the full deterministic algorithm class, excluding randomized algorithms. See the [provenance record](PROVENANCE.md) for the manuscript version and fingerprint.

## Main results

Write `Q = βR²/ε` and `log(ed) = 1 + log d`. The definition `valueComplexity` gives the minimax query complexity over actual Borel adaptive exact-value algorithms. It takes values in `ℝ≥0∞`, with the infimum of the empty set equal to infinity.

| Result | Proved bound | Lean entry point |
|---|---|---|
| Complete upper bound | `N ≤ (d+1)⌈2√Q⌉ ≤ 6d√Q`, for `d ≥ 1` and `0 < ε ≤ βR²` | [UpperBound.lean](ExactValue/UpperBound.lean): `valueComplexity_upper_calls`, `valueComplexity_upper` |
| Integer-parameter lower bound | If `8T < dm`, an admissible hard objective yields output error at least `11/131072 · βR²/m²` | [IntegerLowerBound.lean](ExactValue/IntegerLowerBound.lean): `integer_parameter_lower_bound` |
| Integer lower bound and exact modulus for Borel algorithms | The same error bound; the greatest strong-convexity modulus of the hard objective is exactly `β/(4096m²)` | [ValueAlgorithm.lean](ExactValue/ValueAlgorithm.lean): `algorithm_integer_lower_bound_with_modulus` |
| Main lower bound | `N ≥ c d min{√Q, (d/log(ed))^(1/3)}` | [ComplexityLower.lean](ExactValue/ComplexityLower.lean): `main_lower_rate` |
| Matching bounds at moderate accuracy | In the manuscript's stated regime, `c d√Q ≤ N ≤ C d√Q` | [MainTheorems.lean](ExactValue/MainTheorems.lean): `matching_rate` |
| Two accuracy regimes | The square-root accuracy term and the term `d^(4/3)/log(ed)^(1/3)` | [MainTheorems.lean](ExactValue/MainTheorems.lean): `low_accuracy_regime`, `high_accuracy_regime` |

The integer-parameter theorem also requires `d ≥ 8`, `1 ≤ m`, `4m ≤ d`, and `m³(1+log d) ≤ 2⁻²⁴d`, with `β,R > 0`. The dimension–accuracy theorem applies when `d ≥ d₀` and `0 < ε ≤ cεβR²`. The matching interval is `βR²(log(ed)/d)^(2/3) ≤ ε ≤ cεβR²`. The explicit universal constants are:

```
c = 2⁻¹³,   C = 6,   cε = 2⁻²⁰,   d₀ = 2⁶⁴.
```

The dimension threshold is conservative to simplify logarithmic estimates and integer rounding; the manuscript only requires the existence of such universal constants. At higher accuracy, the formalization establishes the manuscript's lower bound and makes no additional claim of matching upper and lower bounds.

## Reproduction and verification

Install [elan](https://github.com/leanprover/elan#installation) and ensure `lake` is on PATH. The verification script requires Python 3.10 or later. Run the following commands from this directory on Windows, macOS, or Linux:

```sh
lake exe cache get
python scripts/verify.py
```

The first command downloads compiled Mathlib artifacts for the pinned version. The verification script checks that all 37 modules are imported by the entry point, scans for proof placeholders and trust escapes, builds the project, and audits every project theorem's transitive axiom dependencies. It generates `proof/build.log`, `proof/audit.log`, and a summary in `proof/verification.json` locally. CI also preserves these files as [Actions artifacts](https://github.com/WU-Wendao/ZERO-Lab-Lean/actions/workflows/lean.yml). Generated logs are not committed.

**The first complete verification passed on 2026-09-09. After migration to this repository on 2026-09-29, local verification and [GitHub CI](https://github.com/WU-Wendao/ZERO-Lab-Lean/actions/runs/36542248703) passed again: 37 modules, 255 handwritten theorems, and 449 audited theorem constants, including generated auxiliary declarations. All depend only on standard foundational axioms.**

- Lean: 4.19.0.
- Mathlib: v4.19.0, commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`.
- Dependency versions are pinned in [lake-manifest.json](lake-manifest.json).
- elan selects the version from this directory's `lean-toolchain`; no machine-specific toolchain directory or PowerShell wrapper is required.
- Build separately with `lake build`; audit separately with `lake env lean proof/Audit.lean`.
- Top-level source entry point: [ExactValue.lean](ExactValue.lean).

## Formalization conventions

`AdmissibleObjective` uses Euclidean space, genuine Fréchet derivatives, and `ContDiff ℝ 1`. The objective class promises a unique global minimizer in the **closed** ball of radius `R/2`, as in the manuscript. A separate theorem establishes the strict interior guarantee for the constructed hard objectives.

The upper-bound algorithm forms finite differences from historical exact function values, charging `d+1` queries per iteration. The proofs establish Borel measurability of its query and output maps, query feasibility for all histories, output in the inner ball, and agreement between the actual oracle execution and the accelerated iteration. The error analysis includes the complete inductive invariant; Taylor remainder estimates and the final estimate-sequence inequalities are derived rather than assumed.

The lower bound is first proved for all bounded deterministic state machines and then connected to the manuscript's Borel history-based algorithms. The delayed-frame construction defines one fixed objective and proves that it reproduces every exact reply. The output is treated as a virtual query during the construction of the hard objective, without increasing the algorithm's actual query budget.

Subspace cap avoidance is proved using finite sign vectors and an exponential potential, obtaining the conclusion and parameter conditions needed by the manuscript. The appendix's Gaussian chi-square lower-tail bound is also proved independently using a Gaussian product measure. Moreau-envelope properties follow from an explicit simplex dual. Existence and localization of the hard objective's minimizer follow from radial comparison and compactness, using the sufficient bound `R/4 + ρ < R/2`. The coverage map records these choices of proof approach.

`Fin m` uses zero-based indices, so the bias is written with `i.val + 1`. The modifier `noncomputable` is used for real numbers, extrema, and classical choice. Lean checks every proof; the audit allows only the standard foundational axioms `propext`, `Classical.choice`, and `Quot.sound`.

Lean's natural numbers include zero. [ZeroDimension.lean](ExactValue/ZeroDimension.lean) additionally proves `N = 0` in dimension zero and establishes `N ≤ 6d√Q` for all natural-number dimensions. The manuscript's call-count comparison `(d+1)⌈2√Q⌉ ≤ 6d√Q` is interpreted for positive dimensions.

Return to the [repository README](../../README.md). See the [contribution guide](../../CONTRIBUTING.md) to add another research problem.
