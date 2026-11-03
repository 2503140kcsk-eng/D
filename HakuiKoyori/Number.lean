import Mathlib

/-!
# Hakui Koyori Number — arithmetic core

The core is deliberately benchmark-parametric. It does not assume that an
external googological specification already determines a unique Nat.
-/

namespace HakuiKoyori

/-- One Koyori Spark experiment applies one base-2 exponentiation stage. -/
def sparkIteration (seed : Nat) : Nat → Nat
  | 0 => seed
  | depth + 1 => 2 ^ sparkIteration seed depth

/-- Every natural number is bounded by the corresponding power of two. -/
theorem nat_le_two_pow (n : Nat) : n ≤ 2 ^ n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hpos : 0 < 2 ^ n := by
        positivity
      calc
        n + 1 ≤ 2 ^ n + 1 := Nat.add_le_add_right ih 1
        _ ≤ 2 ^ n + 2 ^ n := by
          omega
        _ = 2 ^ (n + 1) := by
          rw [pow_succ]
          ring

/-- Each finite number of Spark stages is at least its initial seed. -/
theorem sparkIteration_ge_seed (seed depth : Nat) :
    seed ≤ sparkIteration seed depth := by
  induction depth with
  | zero =>
      simp [sparkIteration]
  | succ depth ih =>
      simp only [sparkIteration]
      exact le_trans ih (nat_le_two_pow (sparkIteration seed depth))

/--
The benchmark-relative Hakui Koyori Number.

For a fixed benchmark L, the iteration starts at L+2 and performs L+1
successive exponentiation stages.
-/
def hakuiKoyoriNumber (gardenBenchmark : Nat) : Nat :=
  sparkIteration (gardenBenchmark + 2) (gardenBenchmark + 1)

/-- The HKN construction is at least two greater than its benchmark. -/
theorem hakuiKoyoriNumber_ge (gardenBenchmark : Nat) :
    gardenBenchmark + 2 ≤ hakuiKoyoriNumber gardenBenchmark := by
  exact sparkIteration_ge_seed
    (gardenBenchmark + 2) (gardenBenchmark + 1)

/-- Main comparison theorem: HKN(L) is strictly greater than every Nat L. -/
theorem hakuiKoyoriNumber_gt (gardenBenchmark : Nat) :
    gardenBenchmark < hakuiKoyoriNumber gardenBenchmark := by
  unfold hakuiKoyoriNumber
  have h := sparkIteration_ge_seed
    (gardenBenchmark + 2) (gardenBenchmark + 1)
  omega

end HakuiKoyori
