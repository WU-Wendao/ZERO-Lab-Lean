import ExactValue
import Lean.Util.CollectAxioms

/-! Reject any theorem in this project whose transitive axiom dependencies
include anything beyond Lean's standard classical foundations. -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (name, info) in env.constants.toList do
    if name.getRoot == `ExactValue then
      match info with
      | .thmInfo _ => names := names.push name
      | _ => pure ()
  names := names.qsort (fun a b => a.toString < b.toString)
  if names.isEmpty then throwError "No project theorems found."
  for name in names do
    let axioms ← Lean.collectAxioms name
    let unexpected := axioms.filter (fun a =>
      a != `propext && a != `Classical.choice && a != `Quot.sound)
    unless unexpected.isEmpty do
      throwError "{name}: unexpected axiom dependencies {unexpected}"
    logInfo m!"PASS {name}: {axioms}"
  logInfo m!"AUDIT PASSED: {names.size} project theorems; standard axioms only."
