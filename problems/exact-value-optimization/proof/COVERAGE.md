# 原文数学结果与 Lean 证明对应

来源：*Near-Optimal Deterministic Exact-Value Complexity for Smooth Convex Optimization*，2026 年 9 月工作稿；版本指纹见[来源记录](../PROVENANCE.md)。下表覆盖原文全部 20 个具有标题的定理、命题、推论和引理，行号对应该版本。总入口 `ExactValue.lean` 导入全部 37 个模块，统一参与构建和传递公理审计。

表中的 `文件：定理` 用于定位源码。项目定理位于 `ExactValue` 命名空间；投影定理另位于 `ExactValue.ClosedConvexDomain`。

| 原文行号、标签 | Lean 入口与覆盖内容 |
|---|---|
| 251，`thm:upper` | `UpperBound`：`valueComplexity_upper_calls`、`valueComplexity_upper`、`acceleratedValueAlgorithm_guarantees`、`acceleratedValueAlgorithm_output_inner`。实际 Borel 算法、精确调用数、误差保证、查询合法性和内球输出。 |
| 267，`thm:integer` | `IntegerLowerBound`：`integer_parameter_lower_bound`；`ValueAlgorithm`：`algorithm_integer_lower_bound_with_modulus`。合法硬函数、真实运行误差、精确强凸模量。误差常数 `11/131072` 强于原文 `1/131072`。 |
| 286，`thm:main` | `ComplexityLower`：`dimension_accuracy_lower`、`main_lower_rate`。`DimensionScale.lowerScale_floor` 完成整数选择、维度和尺度约束及严格误差比较。 |
| 307，`cor:matching` | `MainTheorems`：`matching_complexity`、`matching_rate`。包括精度区间及统一常数存在量词。 |
| 329，`cor:regimes` | `MainTheorems`：`low_accuracy_regime`、`high_accuracy_regime`。实数分数幂与对数的等式也经过证明。 |
| 357，`lem:fd` | `SmoothModel`：`smooth_remainder`、`finiteGradient_error`。从真实导数及梯度 Lipschitz 条件推导余项和误差 `βh√d/2`；`Bounds.displaced_query_in_ball` 证明查询位置。 |
| 390，`lem:inexact-oracle` | `SmoothModel.convex_supporting`、`smooth_remainder`；`FiniteDifferenceUpper.finiteDifference_model`。证明整个内球上的模型，`δℓ=Rδ`、`δu=δ²/(2β)`、`L=2β`。 |
| 484，`lem:accelerated-error` | `Acceleration`：`accelRun_invariant`、`accelRun_potential_upper`、`accelRun_error`。完整递推不变量与误差界；`AccelerationWeights.accelerationWeight_lower` 给出权重增长。初点按原算法为零。 |
| 704，`lem:moreau` | `MoreauCompleteness`：`maxAffine_convex`、`maxAffine_lipschitz`、`moreau_unique_proximal_point`、`proximal_radius_and_gradient`；`Moreau.moreau_approximation`；`Smoothness` 中的凸性、C¹、梯度范数及 Lipschitz 定理。 |
| 747，`lem:dual` | `Moreau.moreau_eq_dual` 从原始下确界证明单纯形最大值表示；`Chain.exists_dualMax` 与 `Moreau.primalCandidate_attains` 证明两端实际达到最优值。 |
| 794，`lem:shield` | `Chain.dualMax_tail_zero` 限制所有对偶最优解支撑；`Moreau.moreau_exact_prefix_shielding`、`moreau_exact_zero_shielding` 给出原始包络的精确值等式。 |
| 881，`lem:progressgap` | `Moreau.moreau_progress_gap`，包括原始 Moreau 值、末坐标窗口及定量差距。 |
| 918，`lem:cap` | `CapAvoidance.subspace_cap_avoidance`；`FiniteSigns` 中的指数矩与同时小投影存在性。结论甚至无需原文的 `ρ ≤ R` 条件。 |
| 961，`cor:capparameter` | `CapParameters.cap_parameter_condition`，给出 `c₀=2⁻²⁴`，包括查询数量、子空间维数和对数估计。 |
| 1125，`prop:transcript` | `OracleCompiler`：`prefixBlocks_local`、`exists_compiled_frame`、`prefixState_eq_oracle`、`exists_hard_frame_for_queries`；`DelayedFrame.exists_delayed_frame`。完整标架与同一固定函数的精确重放。 |
| 1162，`prop:smooth` | `Admissibility` 中的 C¹、强凸及梯度 Lipschitz 定理；`HardObjectiveCompleteness.hard_objective_strict_smoothness`；`HardParameters.hard_objective_exact_modulus`。包括严格小于 β 的光滑常数与最大强凸模量。 |
| 1205，`prop:minloc` | `HardObjectiveCompleteness.hard_objective_strict_minimizer`：全局存在、唯一性和严格内点。`HardParameters.hard_objective_admissible` 对接闭球版本的函数类。 |
| 1254，`prop:outputgap` | `HardParameters`：`comparisonPoint_coordinates`、`comparisonPoint_norm`、`hard_objective_output_gap`。最终整数定理中的末坐标条件由完整构造导出。 |
| 1470，Projection and squared distance | `Projection`：`halfSquaredDistance_eq`、`halfSquaredDistance_convex`、`halfSquaredDistance_hasFDerivAt`、`halfSquaredDistance_contDiff`、`residual_lipschitz`。真实投影、半距离平方及 1-Lipschitz 梯度；`BallPenalty.infDist_closedBall` 给出球距离公式。 |
| 1491，Chi-square lower tail | `GaussianTail.gaussian_chi_square_lower_tail`：标准高斯乘积测度下 `P{Σgᵢ² ≤ p/2} ≤ exp(-p/16)`；`gaussian_chi_square_lower_tail_of_law` 对接具有该分布的任意可测随机向量。使用高斯积分、乘积积分及 Markov 不等式。 |

## 模型连接与证明路线

- `AdmissibleObjective` 包含凸性、全局 C¹、全局 β-Lipschitz 梯度和唯一全局极小点的闭球承诺。一般函数类没有增加强凸要求。
- `ValueAlgorithm` 使用带查询点的完整历史和 Borel 策略。预算外规则用于总函数表示，`ofFinite` 将原文有限策略扩展到该表示。`valueComplexity` 是成功预算的扩展非负实下确界。
- `ProjectedQuadratic` 和 `AccelerationGeometry` 证明投影子问题及耦合步；`UpperConvergence.upper_iterate_accuracy` 完成步长、精度和迭代次数下的误差计算。
- `BatchProcedure` 只使用历史标量回复定义算法；`BatchAlgorithm` 证明 Borel 性、前缀依赖和 `batch_algorithm_result`，连接真正的值查询过程与加速迭代。
- `IntegerLowerBound.padded_state`、`padded_output` 证明虚拟输出查询不改变真实算法的状态、输出及预算。
- 球冠避让采用有限符号和指数势证明，保留原文所需结论及常数条件。高斯附录结论也独立完成。
- Moreau 微分、光滑性与近端点唯一性由显式对偶和配方证明。
- 极小点位置通过紧球取最小值和球外径向比较证明，使用 `R/4+ρ<R/2`；原文证明使用更紧的中间估计 `R/4+ρ/2`。命题声明的严格内点结论相同。
- 主下界及匹配推论使用保守的显式维度门槛 `d₀=2⁶⁴`，满足原文的存在量词。
- 原文调用数链式不等式按正维度理解；`ZeroDimension` 额外证明零维复杂度为零。

该清单覆盖论文的数学定理体系。相关工作、参考文献的历史叙述和讨论段落不属于形式化命题。
