# 精确函数值下的光滑凸优化

[English](README.md) | **简体中文**

本项目形式化了 *Near-Optimal Deterministic Exact-Value Complexity for Smooth Convex Optimization* 中的主上界、整数参数下界、维度—精度下界、匹配推论、两个精度区间及辅助引理。原文的 20 个具名数学结果均有对应证明，包括两个附录引理。逐项入口见 [覆盖清单](proof/COVERAGE.zh-CN.md)。

这是确定性、自适应、精确函数值 oracle 模型下的零阶优化问题。每轮上界算法沿全部坐标做有限差分，再执行投影加速更新；下界适用于整个确定性算法类，不包含随机化算法。原稿版本与文件指纹见 [来源记录](PROVENANCE.zh-CN.md)。

## 主要结论

记 `Q = βR²/ε`、`log(ed) = 1 + log d`。`valueComplexity` 是对实际 Borel 自适应精确函数值算法定义的 minimax 调用复杂度，取值于 `ℝ≥0∞`，空集合的下确界为无穷大。

| 结论 | 已证明的界 | Lean 入口 |
|---|---|---|
| 完整上界 | `N ≤ (d+1)⌈2√Q⌉ ≤ 6d√Q`，`d ≥ 1`、`0 < ε ≤ βR²` | [UpperBound.lean](ExactValue/UpperBound.lean)：`valueComplexity_upper_calls`、`valueComplexity_upper` |
| 整数参数下界 | `8T < dm` 时存在合法硬函数，输出误差至少 `11/131072 · βR²/m²` | [IntegerLowerBound.lean](ExactValue/IntegerLowerBound.lean)：`integer_parameter_lower_bound` |
| Borel 算法的整数下界与精确模量 | 同一下界；硬函数最大强凸参数恰为 `β/(4096m²)` | [ValueAlgorithm.lean](ExactValue/ValueAlgorithm.lean)：`algorithm_integer_lower_bound_with_modulus` |
| 主下界 | `N ≥ c d min{√Q, (d/log(ed))^(1/3)}` | [ComplexityLower.lean](ExactValue/ComplexityLower.lean)：`main_lower_rate` |
| 中等精度的匹配界 | 原文指定区间内，`c d√Q ≤ N ≤ C d√Q` | [MainTheorems.lean](ExactValue/MainTheorems.lean)：`matching_rate` |
| 两个精度区间 | 平方根精度项与 `d^(4/3)/log(ed)^(1/3)` 项 | [MainTheorems.lean](ExactValue/MainTheorems.lean)：`low_accuracy_regime`、`high_accuracy_regime` |

整数参数定理还要求 `d ≥ 8`、`1 ≤ m`、`4m ≤ d` 和 `m³(1+log d) ≤ 2⁻²⁴d`，且 `β,R > 0`。维度—精度定理适用于 `d ≥ d₀`、`0 < ε ≤ cεβR²`。匹配区间为 `βR²(log(ed)/d)^(2/3) ≤ ε ≤ cεβR²`。使用的显式统一常数为：

```
c = 2⁻¹³,   C = 6,   cε = 2⁻²⁰,   d₀ = 2⁶⁴.
```

维度门槛取保守值，以简化对数和整数取整证明；原文仅要求存在这些统一常数。高精度区间仍只得到原文声明的下界，不作该区间上下界匹配的额外主张。

## 复现与验证

安装 [elan](https://github.com/leanprover/elan#installation)，确保 `lake` 位于 PATH；验证脚本需要 Python 3.10 或更高版本。在本目录运行以下命令，Windows、macOS、Linux 均适用：

```sh
lake exe cache get
python scripts/verify.py
```

第一步下载固定版本的 Mathlib 编译缓存。验证脚本检查全部 37 个模块均由总入口导入，扫描占位证明和信任绕过，再编译整个项目并审计所有项目定理的传递公理依赖。日志在本地生成为 `proof/build.log`、`proof/audit.log`，摘要生成为 `proof/verification.json`；CI 也会将这些文件保存为 [Actions 运行附件](https://github.com/WU-Wendao/ZERO-Lab-Lean/actions/workflows/lean.yml)。生成日志不提交到仓库。

**首次完整验证于 2026-09-09 通过；2026-09-29 迁入本仓库后，本地验证及 [GitHub CI](https://github.com/WU-Wendao/ZERO-Lab-Lean/actions/runs/36542248703) 再次通过：37 个模块、255 个手写定理；公理审计覆盖 449 个定理常量（包含自动生成的辅助定理），全部仅依赖标准基础公理。**

- Lean：4.19.0。
- Mathlib：v4.19.0，提交 `c44e0c8ee63ca166450922a373c7409c5d26b00b`。
- 依赖版本固定在 [lake-manifest.json](lake-manifest.json)。
- elan 按本目录的 `lean-toolchain` 自动选择版本，无需本机专用目录或 PowerShell 包装脚本。
- 单独编译使用 `lake build`；单独审计使用 `lake env lean proof/Audit.lean`。
- 源码总入口：[ExactValue.lean](ExactValue.lean)。

## 形式化约定

`AdmissibleObjective` 使用真正的欧氏空间、Fréchet 导数及 `ContDiff ℝ 1`。函数类的唯一全局极小点位于半径 `R/2` 的**闭球**，与原文定义一致；构造的硬函数另有严格内点定理。

上界算法从历史精确函数值构造有限差分，每次迭代计入 `d+1` 次调用。查询和输出规则的 Borel 性、所有历史上的查询合法性、输出位于内球，以及真实 oracle 运行与加速迭代的一致性均已证明。误差证明包含完整递推不变量，未把 Taylor 余项或最终估计序列不等式当作未证前提。

下界先对所有有界确定性状态算法证明，再连接到原文 Borel 历史算法。延迟标架构造生成同一个固定目标函数，并逐次证明它重放全部精确回复。输出作为虚拟查询参与硬函数构造，不增加实际调用预算。

球冠避让采用有限符号向量和指数势函数证明，得到原文所需结论及常数条件。附录高斯卡方下尾界也已单独用真正的高斯乘积测度证明。Moreau 包络性质通过显式单纯形对偶证明。硬函数极小点位置通过径向比较与紧致性证明，使用足够的界 `R/4 + ρ < R/2`。路线调整详见覆盖清单。

`Fin m` 从 0 编号，偏置使用 `i.val + 1`。`noncomputable` 用于实数、确界和经典选择。全部证明均由 Lean 检查；审计仅允许标准基础公理 `propext`、`Classical.choice`、`Quot.sound`。

Lean 的自然数包含零；[ZeroDimension.lean](ExactValue/ZeroDimension.lean) 额外证明零维时 `N = 0`，并给出所有自然数维度上的 `N ≤ 6d√Q`。原文中含 `(d+1)⌈2√Q⌉ ≤ 6d√Q` 的调用数比较按正维度解释。

返回[仓库首页](../../README.zh-CN.md)；添加其他研究问题请参见[维护指南](../../CONTRIBUTING.zh-CN.md)。
