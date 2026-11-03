import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

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
          nlinarith [hpos]
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

/-- A final exponential tower that strictly exceeds any fixed finite benchmark. -/
def towerAboveBenchmark (gardenBenchmark : Nat) : Nat :=
  sparkIteration (gardenBenchmark + 2) (gardenBenchmark + 1)

/-- The tower starts at least two above its benchmark. -/
theorem towerAboveBenchmark_ge (gardenBenchmark : Nat) :
    gardenBenchmark + 2 ≤ towerAboveBenchmark gardenBenchmark := by
  exact sparkIteration_ge_seed
    (gardenBenchmark + 2) (gardenBenchmark + 1)

/-- Main benchmark lemma: the tower is strictly greater than every Nat benchmark. -/
theorem towerAboveBenchmark_gt (gardenBenchmark : Nat) :
    gardenBenchmark < towerAboveBenchmark gardenBenchmark := by
  unfold towerAboveBenchmark
  have h := sparkIteration_ge_seed
    (gardenBenchmark + 2) (gardenBenchmark + 1)
  nlinarith [h]

end HakuiKoyori
