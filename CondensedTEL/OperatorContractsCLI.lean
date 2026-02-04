-- Operator Contract CLI
-- Export operator contracts as JSON for Rust runtime
-- Copyright (c) 2026 TEL Project

import CondensedTEL.OperatorContracts

open OperatorContracts

def main (args : List String) : IO UInt32 := do
  match args with
  | ["frobenius", p_str] =>
    match p_str.toNat? with
    | some p =>
      -- Supported primes with explicit Fact instances
      match p with
      | 2 =>
        have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        IO.println (getFrobeniusContractJson 2)
        return 0
      | 3 =>
        have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
        IO.println (getFrobeniusContractJson 3)
        return 0
      | 5 =>
        have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
        IO.println (getFrobeniusContractJson 5)
        return 0
      | 7 =>
        have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
        IO.println (getFrobeniusContractJson 7)
        return 0
      | 11 =>
        have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
        IO.println (getFrobeniusContractJson 11)
        return 0
      | 13 =>
        have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
        IO.println (getFrobeniusContractJson 13)
        return 0
      | _ =>
        IO.eprintln s!"Unsupported prime: {p}"
        IO.eprintln "Supported primes: 2, 3, 5, 7, 11, 13"
        return 1
    | none =>
      IO.eprintln s!"Invalid prime: {p_str}"
      return 1

  | ["stratify", λ_str] =>
    match λ_str.toNat? with
    | some λ =>
      IO.println (getStratifyContractJson λ)
      return 0
    | none =>
      IO.eprintln s!"Invalid stratification level: {λ_str}"
      return 1

  | ["lift", p_str] =>
    match p_str.toNat? with
    | some p =>
      match p with
      | 2 =>
        have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        IO.println (getLiftContractJson 2)
        return 0
      | 3 =>
        have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
        IO.println (getLiftContractJson 3)
        return 0
      | 5 =>
        have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
        IO.println (getLiftContractJson 5)
        return 0
      | 7 =>
        have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
        IO.println (getLiftContractJson 7)
        return 0
      | 11 =>
        have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
        IO.println (getLiftContractJson 11)
        return 0
      | 13 =>
        have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
        IO.println (getLiftContractJson 13)
        return 0
      | _ =>
        IO.eprintln s!"Unsupported prime: {p}"
        return 1
    | none =>
      IO.eprintln s!"Invalid prime: {p_str}"
      return 1

  | _ =>
    IO.eprintln "Usage: contracts <operator> <args>"
    IO.eprintln ""
    IO.eprintln "Operators:"
    IO.eprintln "  frobenius <prime>        Export Frobenius contract"
    IO.eprintln "  stratify <lambda>        Export stratification contract"
    IO.eprintln "  lift <prime>             Export p-adic lift contract"
    IO.eprintln ""
    IO.eprintln "Examples:"
    IO.eprintln "  contracts frobenius 5"
    IO.eprintln "  contracts stratify 3"
    IO.eprintln "  contracts lift 7"
    return 1
