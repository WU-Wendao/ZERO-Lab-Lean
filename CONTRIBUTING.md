# Adding and maintaining formalization projects

**English** | [简体中文](CONTRIBUTING.zh-CN.md)

## Add a problem

1. Create an independent Lake project under `problems/<problem-slug>/`. Use lowercase letters and hyphens, for example `exact-value-optimization`, and give each problem its own Lean module namespace.
2. Create and commit `lean-toolchain`, `lakefile.toml` (or `lakefile.lean`), and `lake-manifest.json` in that directory. Pin dependencies to versions or commit hashes.
3. Provide a top-level import module and the proof modules. The entry point must cover all sources that need verification.
4. Add an English `README.md`, a Chinese `README.zh-CN.md`, `proof/COVERAGE.md`, `proof/COVERAGE.zh-CN.md`, `proof/Audit.lean`, and `scripts/verify.py`. Follow the existing project's layout, adapting the library name, source directory, and audited namespace.
5. Run `python scripts/verify.py --project <problem-slug>` from the repository root. Once the build and axiom audit pass, add the problem to the indexes in both root README files.

CI discovers projects directly under `problems/`; its project list does not need manual updates. Incomplete project layouts produce an explicit error so that a project cannot be silently skipped.

## What a problem README should include

- The problem and mathematical results, with explicit assumptions on dimension, parameter ranges, function classes, and algorithm models.
- The filenames and names of the main Lean theorems, and an accurate description of formalization coverage.
- Lean/Mathlib versions, build instructions, and axiom-audit instructions.
- Any changes to proof approaches, assumptions, constants, or notation relative to the manuscript.
- The source title and version. A file fingerprint or public link is sufficient. The full manuscript is not a build dependency; include it only when publishing the manuscript is intended.
- The latest actual verification result, distinguishing handwritten theorems from audited constants that include generated auxiliary declarations.

Both coverage documents should map manuscript results to actual Lean declarations. Successful compilation verifies the statements expressed in Lean; correspondence with the manuscript still requires checking definitions and assumptions.

## Verification interface

Each project's `scripts/verify.py` supports:

```sh
python scripts/verify.py           # Source checks, lake build, transitive axiom audit
python scripts/verify.py --static  # Source coverage checks only; no Lean installation needed
```

The script uses `lake` from PATH, runs in its own problem directory, and exits with a nonzero status on failure. Generated logs go into that project's `proof/` directory. Ensure that the top-level module imports every proof module, and reject proof placeholders, custom axioms, and native execution used in place of proof. Audit the transitive dependencies of every project theorem, allowing only Lean's standard foundational axioms.

Mark a project as verified only after both the build and audit succeed. Record the status of newly added proofs accurately in the problem README.

## Keep projects independent

- Do not import sources across problem directories or depend on machine-specific absolute paths, parent-directory caches, or private toolchains.
- Do not commit `.lake/`, `.tools/`, compiled artifacts, access tokens, or machine-specific settings.
- Update the lockfile when changing dependencies and run all verification steps within that project.
- Keep changes focused. In pull requests, explain whether mathematical statements, assumptions, or coverage changed, and report the checks performed.

## Bilingual documentation conventions

- Use default filenames for English and the `.zh-CN.md` suffix for Simplified Chinese. Each document pair links to the other language at the top.
- Chinese pages should link to Chinese explanations when available; English pages should link to English explanations. Keep Lean files, commands, and theorem identifiers consistent.
- Update mathematical claims, assumptions, constants, applicability, known limitations, and verification status in both languages in the same commit. Check language-switch links and relative links before submitting.
- Maintain one shared set of Lean proofs. Language variants apply to documentation only.
