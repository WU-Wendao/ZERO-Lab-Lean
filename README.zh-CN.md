# ZERO-Lab-Lean

[English](README.md) | **简体中文**

[![Lean verification](https://github.com/WU-Wendao/ZERO-Lab-Lean/actions/workflows/lean.yml/badge.svg)](https://github.com/WU-Wendao/ZERO-Lab-Lean/actions/workflows/lean.yml)

**ZERO Lab 的 Lean 4 形式化证明集合。** 每个研究问题拥有独立目录、工具链和依赖，集中保存数学结论、Lean 证明及复现方法。

## 问题索引

| 问题 | 内容 | 环境 | 验证 |
|---|---|---|---|
| [精确函数值下的光滑凸优化](problems/exact-value-optimization/README.zh-CN.md) | 确定性零阶查询复杂度：完整上界、整数参数下界、维度—精度下界与中等精度匹配结果 | Lean 4.19.0 / Mathlib v4.19.0 | 37 个模块、255 个手写定理；449 个定理常量通过公理审计 |

该问题对应 *Near-Optimal Deterministic Exact-Value Complexity for Smooth Convex Optimization*。在文中指定的维度及中等精度区间内，精确函数值查询复杂度为

$$
N_\epsilon=\Theta\!\left(d\sqrt{\frac{\beta R^2}{\epsilon}}\right).
$$

具体假设、适用范围、常数与形式化中的证明路线见[问题说明](problems/exact-value-optimization/README.zh-CN.md)和[定理覆盖清单](problems/exact-value-optimization/proof/COVERAGE.zh-CN.md)。

## 快速开始

安装 [elan](https://github.com/leanprover/elan#installation)，确保 `lake` 可用；验证脚本需要 Python 3.10 或更高版本。每个问题的 `lean-toolchain` 会选择相应的 Lean 版本。

```sh
git clone https://github.com/WU-Wendao/ZERO-Lab-Lean.git
cd ZERO-Lab-Lean/problems/exact-value-optimization
lake exe cache get
python scripts/verify.py
```

`lake exe cache get` 下载该项目固定版本的 Mathlib 编译缓存，首次运行需要网络和足够磁盘空间。验证脚本随后检查源码覆盖、编译全部模块并运行传递公理审计。macOS/Linux 上可按安装方式将 `python` 换成 `python3`。

若只需要编译或单独审计：

```sh
lake build
lake env lean proof/Audit.lean
```

## 仓库结构

```text
ZERO-Lab-Lean/
├── README.md / README.zh-CN.md
├── CONTRIBUTING.md / CONTRIBUTING.zh-CN.md  # 新问题接入与维护约定
├── scripts/                               # 问题发现、统一验证入口
├── .github/workflows/lean.yml              # 按问题分别运行 CI
└── problems/
    └── exact-value-optimization/
        ├── README.md / README.zh-CN.md     # 数学问题、主要定理、复现方法
        ├── PROVENANCE.md / PROVENANCE.zh-CN.md  # 原稿标题、版本与来源指纹
        ├── lean-toolchain
        ├── lakefile.toml
        ├── lake-manifest.json
        ├── ExactValue.lean                # 总导入入口
        ├── ExactValue/                    # 证明源码
        ├── proof/
        │   ├── COVERAGE.md / COVERAGE.zh-CN.md  # 原文结论与 Lean 定理的对应
        │   └── Audit.lean                 # 传递公理检查
        └── scripts/verify.py
```

各问题是独立 Lake 项目。请进入对应问题目录运行 `lake`；仓库根目录不绑定统一 Lean/Mathlib 版本。

从仓库根目录也可以统一操作：

```sh
python scripts/projects.py                              # 列出问题
python scripts/verify.py --project exact-value-optimization
python scripts/verify.py                                # 验证全部问题
python scripts/verify.py --static                        # 仅检查目录及源码
```

## 验证与维护

- 每个问题提交 `lean-toolchain` 和 `lake-manifest.json`，固定可复现环境。
- 证明模块必须进入总导入入口；验证脚本检查遗漏以及占位证明和信任绕过。
- 公理审计检查定理的传递依赖，仅允许 `propext`、`Classical.choice` 和 `Quot.sound`。
- CI 在推送、Pull Request 和手动触发时发现 `problems/` 下的全部项目，分别构建及审计，日志作为运行附件保存。
- `.lake/`、工具链、依赖源码及生成日志不进入 Git。日志可在本地重新生成，或从 [Actions](https://github.com/WU-Wendao/ZERO-Lab-Lean/actions) 下载。
- 新问题按[贡献指南](CONTRIBUTING.zh-CN.md)添加独立目录，再更新上方索引。已有问题的依赖升级应在自身目录内完成验证。

## 文档语言

英文文档使用 `README.md`、`CONTRIBUTING.md` 等默认文件名，中文版本使用 `.zh-CN.md` 后缀，各页顶部提供语言切换。两版中的数学假设、常数、定理名称、覆盖范围和验证状态应在同一次提交中同步更新；Lean 证明源码由两种语言共用。
