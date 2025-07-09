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

-- Theorem about multiplication by zero
theorem mul_zero_example (n : Nat) : n * 0 = 0 := by
  exact Nat.mul_zero n

-- Theorem about multiplication by one
theorem mul_one_example (n : Nat) : n * 1 = n := by
  exact Nat.mul_one n

-- Theorem about subtraction identity
theorem sub_self_example (n : Nat) : n - n = 0 := by
  exact Nat.sub_self n

-- Theorem about distributivity of multiplication over addition
theorem mul_add_example (a b c : Nat) : a * (b + c) = a * b + a * c := by
  exact Nat.mul_add a b c

-- Theorem about powers of numbers
theorem pow_zero_example (n : Nat) : n ^ 0 = 1 := by
  exact Nat.pow_zero n

-- Theorem about powers of one
theorem pow_one_example (n : Nat) : n ^ 1 = n := by
  exact Nat.pow_one n

-- Theorem about addition being left cancellative
theorem add_left_cancel_example (a b c : Nat) : a + b = a + c → b = c := by
  exact Nat.add_left_cancel

-- Theorem about multiplication being left cancellative (when first factor is positive)
theorem mul_left_cancel_example (a b c : Nat) (h : a > 0) : a * b = a * c → b = c := by
  exact Nat.mul_left_cancel h

-- Theorem about successor
theorem succ_example (n : Nat) : n.succ = n + 1 := by
  rfl
