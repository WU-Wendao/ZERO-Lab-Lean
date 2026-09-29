# Correspondence between the manuscript and Lean proofs

**English** | [简体中文](COVERAGE.zh-CN.md)

Source: *Near-Optimal Deterministic Exact-Value Complexity for Smooth Convex Optimization*, September 2026 working draft; see the [provenance record](../PROVENANCE.md) for the version fingerprint. The table covers all 20 named theorems, propositions, corollaries, and lemmas in the manuscript. Line numbers refer to that version. The root module `ExactValue.lean` imports all 37 modules, including them in the build and transitive axiom audit.

The notation `file: theorem` identifies source locations. Project theorems are in the `ExactValue` namespace; projection theorems are in `ExactValue.ClosedConvexDomain`.

| Manuscript line and label | Lean entry points and coverage |
|---|---|
| 251, `thm:upper` | `UpperBound`: `valueComplexity_upper_calls`, `valueComplexity_upper`, `acceleratedValueAlgorithm_guarantees`, `acceleratedValueAlgorithm_output_inner`. The actual Borel algorithm, exact query count, error guarantee, feasible queries, and output in the inner ball. |
| 267, `thm:integer` | `IntegerLowerBound`: `integer_parameter_lower_bound`; `ValueAlgorithm`: `algorithm_integer_lower_bound_with_modulus`. An admissible hard objective, error for the actual execution, and the exact strong convexity modulus. The error constant `11/131072` improves on the manuscript's `1/131072`. |
| 286, `thm:main` | `ComplexityLower`: `dimension_accuracy_lower`, `main_lower_rate`. `DimensionScale.lowerScale_floor` establishes the integer choice, dimension and scale constraints, and strict error comparison. |
| 307, `cor:matching` | `MainTheorems`: `matching_complexity`, `matching_rate`. Includes the accuracy range and existential quantifiers for universal constants. |
| 329, `cor:regimes` | `MainTheorems`: `low_accuracy_regime`, `high_accuracy_regime`. The identities involving real fractional powers and logarithms are also proved. |
| 357, `lem:fd` | `SmoothModel`: `smooth_remainder`, `finiteGradient_error`. Derives the remainder and error `βh√d/2` from the actual derivative and Lipschitz gradient assumption; `Bounds.displaced_query_in_ball` proves query feasibility. |
| 390, `lem:inexact-oracle` | `SmoothModel.convex_supporting`, `smooth_remainder`; `FiniteDifferenceUpper.finiteDifference_model`. Establishes the model on the entire inner ball, with `δℓ=Rδ`, `δu=δ²/(2β)`, and `L=2β`. |
| 484, `lem:accelerated-error` | `Acceleration`: `accelRun_invariant`, `accelRun_potential_upper`, `accelRun_error`. The full inductive invariant and error bound; `AccelerationWeights.accelerationWeight_lower` gives weight growth. The initial point is zero, as in the original algorithm. |
| 704, `lem:moreau` | `MoreauCompleteness`: `maxAffine_convex`, `maxAffine_lipschitz`, `moreau_unique_proximal_point`, `proximal_radius_and_gradient`; `Moreau.moreau_approximation`; convexity, C¹ regularity, gradient norm, and Lipschitz theorems in `Smoothness`. |
| 747, `lem:dual` | `Moreau.moreau_eq_dual` derives the simplex maximum representation from the primal infimum; `Chain.exists_dualMax` and `Moreau.primalCandidate_attains` prove that both optima are attained. |
| 794, `lem:shield` | `Chain.dualMax_tail_zero` restricts the support of every dual optimizer; `Moreau.moreau_exact_prefix_shielding` and `moreau_exact_zero_shielding` give exact value identities for the primal envelope. |
| 881, `lem:progressgap` | `Moreau.moreau_progress_gap`, including the primal Moreau value, the last-coordinate window, and the quantitative gap. |
| 918, `lem:cap` | `CapAvoidance.subspace_cap_avoidance`; exponential moments and existence of simultaneously small projections in `FiniteSigns`. The conclusion does not require the manuscript's assumption `ρ ≤ R`. |
| 961, `cor:capparameter` | `CapParameters.cap_parameter_condition` supplies `c₀=2⁻²⁴`, including the query count, subspace dimension, and logarithmic estimate. |
| 1125, `prop:transcript` | `OracleCompiler`: `prefixBlocks_local`, `exists_compiled_frame`, `prefixState_eq_oracle`, `exists_hard_frame_for_queries`; `DelayedFrame.exists_delayed_frame`. The complete frame and exact replay using one fixed objective. |
| 1162, `prop:smooth` | C¹ regularity, strong convexity, and Lipschitz gradient theorems in `Admissibility`; `HardObjectiveCompleteness.hard_objective_strict_smoothness`; `HardParameters.hard_objective_exact_modulus`. Includes a smoothness constant strictly below β and the greatest strong convexity modulus. |
| 1205, `prop:minloc` | `HardObjectiveCompleteness.hard_objective_strict_minimizer`: global existence, uniqueness, and strict interior location. `HardParameters.hard_objective_admissible` connects this to the function class with its closed-ball condition. |
| 1254, `prop:outputgap` | `HardParameters`: `comparisonPoint_coordinates`, `comparisonPoint_norm`, `hard_objective_output_gap`. The last-coordinate condition in the final integer theorem follows from the complete construction. |
| 1470, Projection and squared distance | `Projection`: `halfSquaredDistance_eq`, `halfSquaredDistance_convex`, `halfSquaredDistance_hasFDerivAt`, `halfSquaredDistance_contDiff`, `residual_lipschitz`. The actual projection, half the squared distance, and its 1-Lipschitz gradient; `BallPenalty.infDist_closedBall` gives the distance formula for the ball. |
| 1491, Chi-square lower tail | `GaussianTail.gaussian_chi_square_lower_tail`: `P{Σgᵢ² ≤ p/2} ≤ exp(-p/16)` under the standard Gaussian product measure; `gaussian_chi_square_lower_tail_of_law` applies to any measurable random vector with this law. Uses Gaussian integration, product integration, and Markov's inequality. |

## Model connections and proof strategy

- `AdmissibleObjective` includes convexity, global C¹ regularity, a globally β-Lipschitz gradient, and the promise that the unique global minimizer lies in the closed ball. Strong convexity is not added to the general function class.
- `ValueAlgorithm` uses full histories, including query points, and Borel policies. Policies beyond the budget make the representation a total function; `ofFinite` extends the manuscript's finite policies to this representation. `valueComplexity` is the infimum of successful budgets in the extended nonnegative reals.
- `ProjectedQuadratic` and `AccelerationGeometry` prove the projection subproblem and coupling step; `UpperConvergence.upper_iterate_accuracy` establishes the error calculation for the chosen step size, accuracy, and iteration count.
- `BatchProcedure` defines the algorithm using only past scalar replies; `BatchAlgorithm` proves Borel measurability, prefix dependence, and `batch_algorithm_result`, connecting the actual value-query process to the accelerated iterates.
- `IntegerLowerBound.padded_state` and `padded_output` prove that the virtual output query leaves the actual algorithm's state, output, and budget unchanged.
- Cap avoidance is proved using finite signs and an exponential potential, retaining the conclusion and constant conditions needed by the manuscript. The Gaussian appendix result is also proved independently.
- Moreau differentiability, smoothness, and uniqueness of the proximal point follow from the explicit dual representation and completing the square.
- The minimizer location is proved by minimization on a compact ball and radial comparison outside it, using `R/4+ρ<R/2`; the manuscript uses the tighter intermediate estimate `R/4+ρ/2`. The stated strict-interior conclusion is the same.
- The main lower bound and matching corollary use the conservative explicit dimension threshold `d₀=2⁶⁴`, satisfying the manuscript's existential quantifier.
- The manuscript's chain of query-count inequalities is interpreted in positive dimension; `ZeroDimension` additionally proves that the zero-dimensional complexity is zero.

This list covers the manuscript's mathematical results. Related work, historical statements in the references, and discussion paragraphs are not formalized propositions.
