import Mathlib.Data.Nat.Basic

theorem simple_test : 1 + 1 = 2 := by
  rfl

-- New theorem about multiplication
theorem mul_comm_example (a b : Nat) : a * b = b * a := by
  exact Nat.mul_comm a b

-- Another theorem about addition associativity
theorem add_assoc_example (a b c : Nat) : (a + b) + c = a + (b + c) := by
  exact Nat.add_assoc a b c

-- Simple theorem about zero
theorem add_zero_example (n : Nat) : n + 0 = n := by
  exact Nat.add_zero n
