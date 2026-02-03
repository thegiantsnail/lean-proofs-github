import Mathlib.Data.Nat.Basic

-- Test decidability
structure TestInterval where
  start : ℕ
  finish : ℕ

def TestInterval.contains (i : TestInterval) (t : ℕ) : Prop :=
  i.start ≤ t ∧ t ≤ i.finish

instance instDecTestContains (i : TestInterval) (t : ℕ) :
    Decidable (i.contains t) :=
  And.decidable

def testRestrict (i : TestInterval) (t : ℕ) : ℕ :=
  if h : i.contains t then t else 0

#check testRestrict

-- Test filter
def testFilter (i : TestInterval) (ts : List ℕ) : List ℕ :=
  ts.filter (fun t => decide (i.contains t))

#check testFilter
