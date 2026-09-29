import ForestSampling
import Lean.Util.CollectAxioms

/-!
Audit every declaration in the project namespace, including transitive
proof dependencies. Only Lean's three standard classical foundations are
permitted. An admitted proof or an additional axiom makes this command fail.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let permitted : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in env.constants.toList do
    if (`ForestSampling).isPrefixOf name then
      let axioms ← Lean.collectAxioms name
      for axiomName in axioms do
        unless permitted.contains axiomName do
          throwError "Unapproved axiom {axiomName} in {name}"
      checked := checked + 1
  logInfo m!"Axiom audit passed for {checked} project declarations. Allowed: propext, Classical.choice, Quot.sound."
