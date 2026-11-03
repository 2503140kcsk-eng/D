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
  | rank + 1, right => Function.iterate (knuthUpArrow base rank) right 1

/-- The exact seed appearing in the published LNGN expression 10↑^10 10. -/
def gardenSeed : Nat := knuthUpArrow 10 10 10

/--
One Koyori Spark transformation of the Garden function.

The extra + n + 3 makes the exponent strictly exceed the Garden response
before exponentiation; this is a total natural-number expression.
-/
def koyoriSparkTransform (gardenFunction : Nat → Nat) (n : Nat) : Nat :=
  2 ^ (gardenFunction n + n + 2 + 1)

/-- Each Spark transformation is pointwise strictly above the Garden function. -/
theorem koyoriSparkTransform_gt (gardenFunction : Nat → Nat) (n : Nat) :
    gardenFunction n < koyoriSparkTransform gardenFunction n := by
  have hmargin : gardenFunction n ≤ gardenFunction n + n + 2 := by
    omega
  have hpow := nat_le_two_pow (gardenFunction n + n + 2)
  have hpos : 0 < 2 ^ (gardenFunction n + n + 2) := by
    positivity
  change gardenFunction n <
    2 ^ (gardenFunction n + n + 2 + 1)
  calc
    gardenFunction n ≤ gardenFunction n + n + 2 := hmargin
    _ ≤ 2 ^ (gardenFunction n + n + 2) := hpow
    _ < 2 ^ (gardenFunction n + n + 2 + 1) := by
      rw [pow_succ]
      nlinarith [hpos]

/--
If f is monotone and f(n) < g(n) at every input, then every positive iterate
of g is strictly above the corresponding iterate of f.
-/
theorem natIterate_strict_of_monotone
    {f g : Nat → Nat}
    (hf : Monotone f)
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
          exact lt_of_le_of_lt
            (hf hprev.le)
            (hfg (natIterate g (steps + 1) seed))

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
Conditional comparison theorem.

For every monotone Garden function f, the constructed HKN strictly exceeds
f^10(10↑^10 10). In particular, once the source's semantic Garden function
has been fixed and its monotonicity proved, this theorem gives HKN > LNGN.
-/
theorem hakuiKoyoriNumber_gt_gardenNumber
    (gardenFunction : Nat → Nat)
    (hmono : Monotone gardenFunction) :
    gardenNumber gardenFunction < hakuiKoyoriNumber gardenFunction := by
  have h₁ :
      gardenNumber gardenFunction < koyoriSparkNumber gardenFunction := by
    unfold gardenNumber koyoriSparkNumber
    exact natIterate_strict_of_monotone
      hmono
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
