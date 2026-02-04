import CondensedTEL.ComposedContracts

/-!
# Compositional Contract CLI

Export composed contracts as JSON for Rust integration.

Usage:
  lake exe composed_contracts compose frobenius 5 stratify 3
  lake exe composed_contracts pipeline stratify 3 frobenius 5 frobenius 7
-/

open OperatorContracts

def main (args : List String) : IO Unit := do
  match args with
  | ["compose", op1_name, op1_param, op2_name, op2_param] =>
      -- Parse operator 1
      let op1 ← parseOperator op1_name op1_param
      -- Parse operator 2
      let op2 ← parseOperator op2_name op2_param

      -- Compose
      match composeContracts op1 op2 with
      | some composed =>
          IO.println (composedContractToJson composed)
      | none =>
          IO.eprintln "Error: Operators are incompatible"

  | "pipeline" :: rest =>
      -- Parse all operators
      let ops ← parseOperatorList rest

      -- Compose many
      match composeMany ops with
      | some composed =>
          IO.println (composedContractToJson composed)
      | none =>
          IO.eprintln "Error: Pipeline contains incompatible operators"

  | _ =>
      IO.eprintln "Usage:"
      IO.eprintln "  composed_contracts compose <op1> <param1> <op2> <param2>"
      IO.eprintln "  composed_contracts pipeline <op1> <param1> <op2> <param2> ..."
      IO.eprintln ""
      IO.eprintln "Operators: frobenius, stratify, lift"

where
  parseOperator (name : String) (param : String) : IO OperatorContract := do
    match name, param.toNat? with
    | "frobenius", some p => pure (frobeniusContract p)
    | "stratify", some λ => pure (stratifyContract λ)
    | "lift", some p => pure (liftContract p)
    | _, _ => throw (IO.userError s!"Invalid operator: {name} {param}")

  parseOperatorList : List String → IO (List OperatorContract)
    | [] => pure []
    | name :: param :: rest => do
        let op ← parseOperator name param
        let ops ← parseOperatorList rest
        pure (op :: ops)
    | _ => throw (IO.userError "Invalid operator list (must be pairs)")
