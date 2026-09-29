# Provenance and migration record

**English** | [简体中文](PROVENANCE.zh-CN.md)

- Manuscript title: *Near-Optimal Deterministic Exact-Value Complexity for Smooth Convex Optimization*.
- Manuscript version: Working draft, September 2026.
- Input filename: `main (1).tex`.
- Manuscript SHA256: `EA60410BCBE01FB2909D1F37610DE27D26AEBC40B49FCD8E696FDA79070E048A`.
- First complete verification: 2026-09-09; 37 modules, 255 handwritten theorems, and 449 audited theorem constants.
- Repository migration: 2026-09-29. All Lean proofs, the top-level import module, dependency lockfile, and axiom-audit source were preserved. The verification script was adapted to cross-platform calls to standard `lake` and Python, and repository-level project discovery and CI were added.

The full manuscript is retained in the research workspace. This repository contains the Lean code and the necessary provenance information. Building and auditing do not require the manuscript file.

Manuscript line numbers in the [coverage map](proof/COVERAGE.md) refer to the LaTeX version identified by the fingerprint above. See that map and the problem README for model conventions, changes in proof approach, and explicit constants.

Local compilation, the axiom audit, and [GitHub CI](https://github.com/WU-Wendao/ZERO-Lab-Lean/actions/runs/36542248703) all passed after the migration on 2026-09-29.
