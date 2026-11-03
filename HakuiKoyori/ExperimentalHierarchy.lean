import Mathlib
import HakuiKoyori.Number

namespace HakuiKoyori

/-- Iterate a natural-number endofunction exactly steps times. -/
def natIterate (f : Nat → Nat) : Nat → Nat → Nat
  | 0, seed => seed
  | steps + 1, seed => f (natIterate f steps seed)

/--
Knuth up-arrow notation on natural numbers.

Rank 0 is multiplication. Rank k+1 is iteration of rank k, starting at 1.
Thus rank 1 is exponentiation, rank 2 is tetration, and so on.
-/
def knuthUpArrow (base : Nat) : Nat → Nat → Nat
  | 0, right => base * right
  | rank + 1, right => natIterate (knuthUpArrow base rank) right 1

/-- The exact seed appearing in the published LNGN expression 10↑^10 10. -/
def gardenSeed : Nat := knuthUpArrow 10 10 10

/--
The running maximum of f on the finite initial segment {0,...,n}.
This makes the comparison transform monotone even when f itself is not.
-/
def prefixMaximum (f : Nat → Nat) : Nat → Nat
  | 0 => f 0
  | n + 1 => max (prefixMaximum f n) (f (n + 1))

/-- Every value f(n) is bounded by its finite running maximum. -/
theorem le_prefixMaximum (f : Nat → Nat) (n : Nat) :
    f n ≤ prefixMaximum f n := by
  induction n with
  | zero =>
      simp [prefixMaximum]
  | succ n ih =>
      exact le_max_right _ _

/-- The running maximum is monotone in its natural-number index. -/
theorem prefixMaximum_monotone (f : Nat → Nat) :
    Monotone (prefixMaximum f) := by
  intro a b hab
  induction hab with
  | refl =>
      exact le_rfl
  | @step b hab ih =>
      exact le_trans ih (le_max_left _ _)

/--
One Koyori Spark transformation of the Garden function.

It uses the maximum of all earlier function values, not merely f(n).
This monotone envelope is the key that removes any monotonicity assumption
on the original Garden function.
-/
def koyoriSparkTransform (gardenFunction : Nat → Nat) (n : Nat) : Nat :=
  2 ^ (prefixMaximum gardenFunction n + n + 3)

/-- Every Spark value strictly exceeds the Garden function at that input. -/
theorem koyoriSparkTransform_gt (gardenFunction : Nat → Nat) (n : Nat) :
    gardenFunction n < koyoriSparkTransform gardenFunction n := by
  have hmax : gardenFunction n ≤ prefixMaximum gardenFunction n :=
    le_prefixMaximum gardenFunction n
  have hmargin :
      gardenFunction n ≤ prefixMaximum gardenFunction n + n + 2 := by
    omega
  have hpow := nat_le_two_pow (prefixMaximum gardenFunction n + n + 2)
  have hpos :
      0 < 2 ^ (prefixMaximum gardenFunction n + n + 2) := by
    positivity
  have hexp :
      2 ^ (prefixMaximum gardenFunction n + n + 2 + 1) =
        2 ^ (prefixMaximum gardenFunction n + n + 2) * 2 := by
    rw [pow_succ]
  change gardenFunction n <
    2 ^ (prefixMaximum gardenFunction n + n + 2 + 1)
  calc
    gardenFunction n ≤ prefixMaximum gardenFunction n + n + 2 := hmargin
    _ ≤ 2 ^ (prefixMaximum gardenFunction n + n + 2) := hpow
    _ < 2 ^ (prefixMaximum gardenFunction n + n + 2 + 1) := by
      rw [← hexp]
      nlinarith [hpos]

/-- The Koyori Spark transform is monotone, regardless of f's behavior. -/
theorem koyoriSparkTransform_monotone (gardenFunction : Nat → Nat) :
    Monotone (koyoriSparkTransform gardenFunction) := by
  intro a b hab
  unfold koyoriSparkTransform
  have hmax : prefixMaximum gardenFunction a ≤ prefixMaximum gardenFunction b :=
    prefixMaximum_monotone gardenFunction hab
  have hexp :
      prefixMaximum gardenFunction a + a + 3 ≤
        prefixMaximum gardenFunction b + b + 3 := by
    omega
  gcongr

/--
If g is monotone and pointwise strictly dominates f, then every positive
iterate of g is strictly above the corresponding iterate of f.  Notice that
f itself need not be monotone.
-/
theorem natIterate_strict_of_monotone_majorant
    {f g : Nat → Nat}
    (hg : Monotone g)
    (hfg : ∀ n, f n < g n) :
    ∀ (steps : Nat), 0 < steps →
      ∀ seed, natIterate f steps seed < natIterate g steps seed := by
  intro steps
  induction steps with
  | zero =>
      intro h
      omega
  | succ steps ih =>
      intro h seed
      cases steps with
      | zero =>
          simpa [natIterate] using hfg seed
      | succ steps =>
          have hprev :
              natIterate f (steps + 1) seed <
                natIterate g (steps + 1) seed :=
            ih (by omega) seed
          change f (natIterate f (steps + 1) seed) <
            g (natIterate g (steps + 1) seed)
          exact lt_of_lt_of_le
            (hfg (natIterate f (steps + 1) seed))
            (hg hprev.le)

/-- The source-comparison value f^10(10↑^10 10), with f left explicit. -/
def gardenNumber (gardenFunction : Nat → Nat) : Nat :=
  natIterate gardenFunction 10 gardenSeed

/-- Ten Koyori Spark experiments, using the same ten-step input shape as LNGN. -/
def koyoriSparkNumber (gardenFunction : Nat → Nat) : Nat :=
  natIterate (koyoriSparkTransform gardenFunction) 10 gardenSeed

/--
The final Hakui Koyori Number: a second, finite tower amplification whose
height is determined by the already amplified Spark value.
-/
def hakuiKoyoriNumber (gardenFunction : Nat → Nat) : Nat :=
  towerAboveBenchmark (koyoriSparkNumber gardenFunction)

/--
Main comparison theorem.

For every total function f : Nat → Nat, with no monotonicity hypothesis,
HKN(f) strictly exceeds f^10(10↑^10 10).  Thus once the source's U-model
semantics fixes its Garden function as a Nat-valued total function, the
strict comparison follows immediately.
-/
theorem hakuiKoyoriNumber_gt_gardenNumber
    (gardenFunction : Nat → Nat) :
    gardenNumber gardenFunction < hakuiKoyoriNumber gardenFunction := by
  have h₁ :
      gardenNumber gardenFunction < koyoriSparkNumber gardenFunction := by
    unfold gardenNumber koyoriSparkNumber
    exact natIterate_strict_of_monotone_majorant
      (koyoriSparkTransform_monotone gardenFunction)
      (fun n => koyoriSparkTransform_gt gardenFunction n)
      10
      (by decide)
      gardenSeed
  have h₂ :
      koyoriSparkNumber gardenFunction <
        hakuiKoyoriNumber gardenFunction := by
    change koyoriSparkNumber gardenFunction <
      towerAboveBenchmark (koyoriSparkNumber gardenFunction)
    exact towerAboveBenchmark_gt (koyoriSparkNumber gardenFunction)
  exact lt_trans h₁ h₂

end HakuiKoyori
