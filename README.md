# ZERO-Lab-Lean

**English** | [简体中文](README.zh-CN.md)

[![Lean verification](https://github.com/WU-Wendao/ZERO-Lab-Lean/actions/workflows/lean.yml/badge.svg)](https://github.com/WU-Wendao/ZERO-Lab-Lean/actions/workflows/lean.yml)

**A collection of Lean 4 formalizations from ZERO Lab.** Each research problem has its own directory, toolchain, and dependencies, with mathematical statements, Lean proofs, and reproducible verification instructions.

## Problem index

| Problem | Scope | Environment | Verification |
|---|---|---|---|
| [Smooth convex optimization with exact function values](problems/exact-value-optimization/) | Deterministic zeroth-order query complexity: a complete upper bound, an integer-parameter lower bound, a dimension–accuracy lower bound, and matching bounds at moderate accuracy | Lean 4.19.0 / Mathlib v4.19.0 | 37 modules and 255 handwritten theorems; 449 theorem constants passed the axiom audit |

This project formalizes *Near-Optimal Deterministic Exact-Value Complexity for Smooth Convex Optimization*. Under the manuscript's dimension and moderate-accuracy conditions, the exact-value query complexity is

$$
N_\epsilon=\Theta\!\left(d\sqrt{\frac{\beta R^2}{\epsilon}}\right).
$$

See the [problem README](problems/exact-value-optimization/README.md) and [theorem coverage map](problems/exact-value-optimization/proof/COVERAGE.md) for the assumptions, scope, constants, and proof approaches used in the formalization.

## Quick start

Install [elan](https://github.com/leanprover/elan#installation) and make sure `lake` is on your PATH. The verification scripts require Python 3.10 or later. Each project's `lean-toolchain` selects its Lean version.

```sh
git clone https://github.com/WU-Wendao/ZERO-Lab-Lean.git
cd ZERO-Lab-Lean/problems/exact-value-optimization
lake exe cache get
python scripts/verify.py
```

`lake exe cache get` downloads compiled Mathlib artifacts for the project's pinned version. The first run requires network access and sufficient disk space. The verification script then checks source coverage, builds every module, and audits transitive axiom dependencies. On macOS/Linux, use `python3` instead of `python` if required by your installation.

To run the build or audit separately:

```sh
lake build
lake env lean proof/Audit.lean
```

## Repository layout

```text
ZERO-Lab-Lean/
├── README.md / README.zh-CN.md
├── CONTRIBUTING.md / CONTRIBUTING.zh-CN.md  # Adding and maintaining projects
├── scripts/                               # Project discovery and verification
├── .github/workflows/lean.yml              # CI for each independent project
└── problems/
    └── exact-value-optimization/
        ├── README.md / README.zh-CN.md     # Problem, main theorems, reproduction
        ├── PROVENANCE.md / PROVENANCE.zh-CN.md  # Source title, version, fingerprint
        ├── lean-toolchain
        ├── lakefile.toml
        ├── lake-manifest.json
        ├── ExactValue.lean                # Top-level import module
        ├── ExactValue/                    # Proof sources
        ├── proof/
        │   ├── COVERAGE.md / COVERAGE.zh-CN.md  # Manuscript-to-Lean correspondence
        │   └── Audit.lean                 # Transitive axiom checks
        └── scripts/verify.py
```

Each problem is an independent Lake project. Run `lake` from the corresponding problem directory; the repository root does not impose a shared Lean/Mathlib version.

You can also manage verification from the repository root:

```sh
python scripts/projects.py                              # List projects
python scripts/verify.py --project exact-value-optimization
python scripts/verify.py                                # Verify all projects
python scripts/verify.py --static                        # Check layout and sources only
```

## Verification and maintenance

- Commit each project's `lean-toolchain` and `lake-manifest.json` to pin its environment.
- Include every proof module in the top-level import module. The verification script checks for omissions, proof placeholders, and trust escapes.
- The axiom audit checks transitive theorem dependencies and allows only `propext`, `Classical.choice`, and `Quot.sound`.
- On pushes, pull requests, and manual runs, CI discovers all projects under `problems/`, builds and audits them separately, and preserves logs as workflow artifacts.
- Keep `.lake/`, toolchains, dependency checkouts, and generated logs out of Git. Regenerate logs locally or download them from [Actions](https://github.com/WU-Wendao/ZERO-Lab-Lean/actions).
- Add new problems in separate directories following [CONTRIBUTING.md](CONTRIBUTING.md), then update the index above. Verify dependency upgrades within the affected project.

## Documentation languages

English documentation uses default filenames such as `README.md` and `CONTRIBUTING.md`; Simplified Chinese versions use the `.zh-CN.md` suffix. Each page links to its counterpart at the top. Update mathematical assumptions, constants, theorem names, coverage, and verification status in both versions in the same commit. Both languages share the same Lean proof sources.
