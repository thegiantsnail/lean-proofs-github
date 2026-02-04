-- Priority 4: Operational Layer
-- NullSTHOperational: Executable API for Rust integration
-- Copyright (c) 2026 TEL Project

import CondensedTEL.NullSTH

namespace NullSTH

/-! ## Operational Payloads
Computable functions and JSON serialization for Rust runtime integration.
-/

/-- Operational payload structure: certified constants from formal proofs -/
structure NullPayload where
  betti0 : Nat
  euler  : Int
  h00    : Nat
  vp0_is_infinite : Bool
  perfectoidExtensions : Nat
  frobeniusIterates : Nat
  deriving Repr

/-- Compute the null signature payload for prime p -/
def payload (p : Nat) [Fact p.Prime] : NullPayload :=
  {
    betti0 := bettiNumber 0,
    euler  := eulerCharacteristic,
    h00    := hodgeNumber 0 0,
    vp0_is_infinite := (padicValuation p 0 = none),
    perfectoidExtensions := nullWitness.perfectoidExtensions,
    frobeniusIterates := nullWitness.frobeniusIterates
  }

/-- Simple JSON encoding for stable wire format -/
def payloadToJson (p : NullPayload) : String :=
  let eulerNat := if p.euler >= 0 then p.euler.toNat else 0
  "{" ++
  "\"betti0\":" ++ toString p.betti0 ++ "," ++
  "\"euler\":" ++ toString eulerNat ++ "," ++
  "\"h00\":" ++ toString p.h00 ++ "," ++
  "\"vp0_is_infinite\":" ++ (if p.vp0_is_infinite then "true" else "false") ++ "," ++
  "\"perfectoidExtensions\":" ++ toString p.perfectoidExtensions ++ "," ++
  "\"frobeniusIterates\":" ++ toString p.frobeniusIterates ++
  "}"

/-- Get JSON payload for a specific prime -/
def getPayloadJson (p : Nat) [Fact p.Prime] : String :=
  payloadToJson (payload p)

/-- CLI entrypoint: prints JSON payload for given prime -/
def main (args : List String) : IO UInt32 := do
  -- Get prime from command line (default: 5)
  let pStr := args.getD 0 "5"
  let p : Nat := pStr.toNat?.getD 5

  -- Support common small primes operationally
  let out : String :=
    match p with
    | 2  => getPayloadJson (p := 2)
    | 3  => getPayloadJson (p := 3)
    | 5  => getPayloadJson (p := 5)
    | 7  => getPayloadJson (p := 7)
    | 11 => getPayloadJson (p := 11)
    | 13 => getPayloadJson (p := 13)
    | 17 => getPayloadJson (p := 17)
    | 19 => getPayloadJson (p := 19)
    | 23 => getPayloadJson (p := 23)
    | 29 => getPayloadJson (p := 29)
    | 31 => getPayloadJson (p := 31)
    | _  => "{\"error\":\"unsupported prime: " ++ toString p ++ "\"}"

  IO.println out
  return 0

end NullSTH
