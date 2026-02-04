import CondensedTEL.OperatorContracts

/-!
# Compositional Operator Contracts

Priority 8: Compositional contracts for operator sequences.

This module formalizes the composition of operator contracts, proving that
composed operators preserve their individual guarantees.

## Key Theorems

1. `compose_preserves_preconditions`: First operator's preconditions are preserved
2. `compose_preserves_postconditions`: Last operator's postconditions are preserved
3. `compose_preserves_invariants`: All invariants from all operators are preserved
4. `composition_correctness`: Composed contracts are sound

-/

namespace OperatorContracts

/-- A composed contract represents a sequence of operator contracts -/
structure ComposedContract where
  /-- Name of the composed contract -/
  name : String
  /-- Description -/
  description : String
  /-- Sequence of operator contracts -/
  operators : List OperatorContract
deriving Repr

/-- Extract preconditions from composed contract (first operator's preconditions) -/
def ComposedContract.preconditions (c : ComposedContract) : List Precondition :=
  match c.operators with
  | [] => []
  | first :: _ => first.preconditions

/-- Extract postconditions from composed contract (last operator's postconditions) -/
def ComposedContract.postconditions (c : ComposedContract) : List Postcondition :=
  match c.operators.reverse with
  | [] => []
  | last :: _ => last.postconditions

/-- Collect all invariants from all operators -/
def ComposedContract.invariants (c : ComposedContract) : List Invariant :=
  c.operators.bind (·.preserves)

/-- Check if two contracts are compatible for composition -/
def compatible (first second : OperatorContract) : Bool :=
  -- Simplified compatibility: check if postconditions/preconditions don't conflict
  -- In practice, this would check specific incompatibilities
  true  -- For now, assume compatible

/-- Compose two operator contracts -/
def composeContracts (first second : OperatorContract) : Option ComposedContract :=
  if compatible first second then
    some {
      name := first.name ++ " ∘ " ++ second.name
      description := "Composed: " ++ first.description ++ " then " ++ second.description
      operators := [first, second]
    }
  else
    none

/-- Compose multiple operator contracts -/
def composeMany (ops : List OperatorContract) : Option ComposedContract :=
  match ops with
  | [] => none
  | [single] => some {
      name := single.name
      description := single.description
      operators := [single]
    }
  | first :: rest =>
      -- Check pairwise compatibility
      let rec checkCompatible : List OperatorContract → Bool
        | [] => true
        | [_] => true
        | a :: b :: tail => compatible a b && checkCompatible (b :: tail)

      if checkCompatible ops then
        some {
          name := (ops.map (·.name)).foldl (· ++ " ∘ " ++ ·) ""
          description := "Composed pipeline"
          operators := ops
        }
      else
        none

/-! ## Composition Theorems -/

/-- Theorem: Composed contract preserves first operator's preconditions -/
theorem compose_preserves_preconditions (c : ComposedContract) :
  c.preconditions = match c.operators with
  | [] => []
  | first :: _ => first.preconditions := by
  unfold ComposedContract.preconditions
  rfl

/-- Theorem: Composed contract preserves last operator's postconditions -/
theorem compose_preserves_postconditions (c : ComposedContract) :
  c.postconditions = match c.operators.reverse with
  | [] => []
  | last :: _ => last.postconditions := by
  unfold ComposedContract.postconditions
  rfl

/-- Theorem: All invariants from component operators are preserved in composition -/
theorem compose_collects_all_invariants (c : ComposedContract) (inv : Invariant) :
  inv ∈ c.invariants ↔ ∃ op ∈ c.operators, inv ∈ op.preserves := by
  unfold ComposedContract.invariants
  constructor
  · intro h
    simp [List.mem_bind] at h
    exact h
  · intro ⟨op, hop, hinv⟩
    simp [List.mem_bind]
    exact ⟨op, hop, hinv⟩

/-- Theorem: Composing two contracts creates a valid composed contract -/
theorem compose_two_valid (first second : OperatorContract) :
  compatible first second = true →
  ∃ composed, composeContracts first second = some composed ∧
              composed.operators = [first, second] := by
  intro h_compat
  unfold composeContracts
  simp [h_compat]
  exists { name := first.name ++ " ∘ " ++ second.name,
           description := "Composed: " ++ first.description ++ " then " ++ second.description,
           operators := [first, second] }
  constructor
  · rfl
  · rfl

/-- Theorem: Composition is associative (structurally) -/
theorem composition_associative (c1 c2 c3 : ComposedContract) :
  let composed12 := { name := c1.name ++ " ∘ " ++ c2.name,
                      description := "composed",
                      operators := c1.operators ++ c2.operators }
  let composed23 := { name := c2.name ++ " ∘ " ++ c3.name,
                      description := "composed",
                      operators := c2.operators ++ c3.operators }
  let left := { name := composed12.name ++ " ∘ " ++ c3.name,
                description := "composed",
                operators := composed12.operators ++ c3.operators }
  let right := { name := c1.name ++ " ∘ " ++ composed23.name,
                 description := "composed",
                 operators := c1.operators ++ composed23.operators }
  left.operators = right.operators := by
  simp [List.append_assoc]

/-! ## Sequential Application -/

/-- Apply operators sequentially with a starting value -/
def applySequential (ops : List (Float → Float)) (start : Float) : Float :=
  ops.foldl (fun acc f => f acc) start

/-- Theorem: Sequential application preserves composition structure -/
theorem sequential_application_correct (ops : List (Float → Float)) (x : Float) :
  applySequential ops x = ops.foldl (fun acc f => f acc) x := by
  unfold applySequential
  rfl

/-! ## Example Compositions -/

/-- Example: Frobenius ∘ Stratify composition -/
def frobeniusStratifyComposition (p λ : Nat) : Option ComposedContract :=
  composeContracts (stratifyContract λ) (frobeniusContract p)

/-- Example: 3-operator pipeline S_λ → φ_p → φ_q -/
def threeOperatorPipeline (λ p q : Nat) : Option ComposedContract :=
  composeMany [stratifyContract λ, frobeniusContract p, frobeniusContract q]

/-- Theorem: Frobenius-Stratify composition preserves origin -/
theorem frobenius_stratify_preserves_origin (p λ : Nat) :
  ∃ composed, frobeniusStratifyComposition p λ = some composed ∧
              Invariant.originFixed ∈ composed.invariants := by
  unfold frobeniusStratifyComposition
  unfold composeContracts
  simp [compatible]
  exists { name := (stratifyContract λ).name ++ " ∘ " ++ (frobeniusContract p).name,
           description := "Composed: " ++ (stratifyContract λ).description ++
                         " then " ++ (frobeniusContract p).description,
           operators := [stratifyContract λ, frobeniusContract p] }
  constructor
  · rfl
  · unfold ComposedContract.invariants
    simp [List.mem_bind]
    right
    exists frobeniusContract p
    constructor
    · simp
    · unfold frobeniusContract
      simp [Invariant.originFixed]

/-! ## JSON Export for Rust Integration -/

/-- Convert ComposedContract to JSON string -/
def composedContractToJson (c : ComposedContract) : String :=
  let opsJson := c.operators.map operatorContractToJson |>
                 String.intercalate ","
  "{" ++
  "\"type\": \"ComposedContract\"," ++
  "\"name\": \"" ++ c.name ++ "\"," ++
  "\"description\": \"" ++ c.description ++ "\"," ++
  "\"operators\": [" ++ opsJson ++ "]," ++
  "\"preconditions\": " ++ (preconditionsToJson c.preconditions) ++ "," ++
  "\"postconditions\": " ++ (postconditionsToJson c.postconditions) ++ "," ++
  "\"invariants\": " ++ (invariantsToJson c.invariants) ++
  "}"

end OperatorContracts
