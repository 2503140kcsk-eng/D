import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Tactic.Omega
import HakuiKoyori.GodelSyntax

/-!
# Gödel coding fixed from the Large Number Garden source

The source uses p_i for the (i+1)-st prime, so p_0 = 2, p_1 = 3, ...
For a list a of length h, its code is

  Encode(a) = 2^h * product_{i < h} p_{i+1}^{a_i} - 1.

In Lean, subtraction is natural-number truncated subtraction. The proof below
establishes injectivity by recovering the length from the 2-adic exponent,
then recovering every entry from the exponent of p_{i+1}. The initial factor
2^h is disjoint from all entry primes because p_{i+1} >= 3.
-/

namespace HakuiKoyori
namespace Godel

/-- Zero-based indexing of the primes: p₀ = 2, p₁ = 3, and so on. -/
noncomputable def primeAt (i : Nat) : Nat :=
  Nat.nth Nat.Prime i

theorem primeAt_prime (i : Nat) : Nat.Prime (primeAt i) :=
  Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime i

theorem primeAt_injective : Function.Injective primeAt :=
  Nat.nth_injective Nat.infinite_setOfPred_prime

@[simp] theorem primeAt_zero : primeAt 0 = 2 := by
  simp [primeAt]

@[simp] theorem primeAt_one : primeAt 1 = 3 := by
  simp [primeAt]

/-- Every prime used for a sequence entry is strictly greater than 2. -/
theorem primeAt_gt_two (i : Nat) : 2 < primeAt (i + 1) := by
  have hmono := Nat.nth_strictMono Nat.infinite_setOfPred_prime (Nat.succ_pos i)
  simpa [primeAt] using hmono

/-- The prime-product part of the source's finite-sequence code. -/
noncomputable def sequencePrimeProduct (xs : List Nat) : Nat :=
  (Finset.range xs.length).prod
    (fun i => (primeAt (i + 1)) ^ xs[i]!)

theorem sequencePrimeProduct_pos (xs : List Nat) :
    0 < sequencePrimeProduct xs := by
  unfold sequencePrimeProduct
  apply Finset.prod_pos
  intro i hi
  exact pow_pos (Nat.Prime.pos (primeAt_prime (i + 1))) _

theorem sequencePrimeProduct_ne_zero (xs : List Nat) :
    sequencePrimeProduct xs ≠ 0 :=
  (sequencePrimeProduct_pos xs).ne'

/-- A prime cannot divide a finite product when it divides none of its factors. -/
theorem prime_not_dvd_finset_product {α : Type} (s : Finset α) (g : α → Nat)
    {p : Nat} (hp : Nat.Prime p)
    (h : ∀ i ∈ s, ¬ p ∣ g i) :
    ¬ p ∣ s.prod g := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha]
      apply hp.not_dvd_mul
      · exact h a (by simp)
      · apply ih
        intro b hb
        exact h b (Finset.mem_insert_of_mem hb)

/-- The entry-prime product is odd: none of its factors is divisible by 2. -/
theorem two_not_dvd_sequencePrimeProduct (xs : List Nat) :
    ¬ 2 ∣ sequencePrimeProduct xs := by
  unfold sequencePrimeProduct
  apply prime_not_dvd_finset_product (Finset.range xs.length)
    (fun i => (primeAt (i + 1)) ^ xs[i]!) Nat.prime_two
  intro i hi hpow
  have hdiv : 2 ∣ primeAt (i + 1) :=
    Nat.Prime.dvd_of_dvd_pow Nat.prime_two hpow
  have heq : 2 = primeAt (i + 1) :=
    (Nat.prime_dvd_prime_iff_eq Nat.prime_two (primeAt_prime (i + 1))).mp hdiv
  have hgt := primeAt_gt_two i
  omega

/--
The complete positive integer before subtracting one in Encode(a):
2^length(a) times the indexed-prime product.
-/
noncomputable def encodeCore (xs : List Nat) : Nat :=
  2 ^ xs.length * sequencePrimeProduct xs

theorem encodeCore_pos (xs : List Nat) : 0 < encodeCore xs := by
  unfold encodeCore
  exact Nat.mul_pos (pow_pos (by decide : 0 < 2) _) (sequencePrimeProduct_pos xs)

/-- The original finite-sequence Gödel encoding. -/
noncomputable def encodeSequence (xs : List Nat) : Nat :=
  encodeCore xs - 1

theorem encodeSequence_add_one (xs : List Nat) :
    encodeSequence xs + 1 = encodeCore xs := by
  unfold encodeSequence
  have hp := encodeCore_pos xs
  omega

/-- Factorization of the prime-product part, evaluated at a chosen prime. -/
theorem sequencePrimeProduct_factorization_at (xs : List Nat) (i : Nat)
    (hi : i < xs.length) :
    (sequencePrimeProduct xs).factorization (primeAt (i + 1)) = xs[i]! := by
  classical
  have hprod :=
    Nat.factorization_prod_apply
      (S := Finset.range xs.length)
      (g := fun j => (primeAt (j + 1)) ^ xs[j]!)
      (p := primeAt (i + 1))
      (by
        intro j hj
        exact pow_ne_zero _ (Nat.Prime.ne_zero (primeAt_prime (j + 1))))
  rw [hprod]
  rw [Finset.sum_eq_single i]
  · simp [Nat.factorization_pow, Nat.Prime.factorization_self (primeAt_prime (i + 1))]
  · intro j hj hji
    have hneq : primeAt (i + 1) ≠ primeAt (j + 1) := by
      intro heq
      have hidx := primeAt_injective heq
      omega
    have hnot : ¬ primeAt (i + 1) ∣ primeAt (j + 1) := by
      intro hdvd
      have heq := (Nat.prime_dvd_prime_iff_eq
        (primeAt_prime (i + 1)) (primeAt_prime (j + 1))).mp hdvd
      exact hneq heq
    simp [Nat.factorization_pow, Nat.factorization_eq_zero_of_not_dvd, hnot]
  · intro hnot
    exact (hnot hi).elim

/-- The factor of 2 in encodeCore records exactly the sequence length. -/
theorem encodeCore_factorization_at_two (xs : List Nat) :
    (encodeCore xs).factorization 2 = xs.length := by
  unfold encodeCore
  rw [Nat.factorization_mul (by positivity) (sequencePrimeProduct_ne_zero xs)]
  have hzero :
      (sequencePrimeProduct xs).factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (two_not_dvd_sequencePrimeProduct xs)
  simp [Nat.factorization_pow, Nat.Prime.factorization_self Nat.prime_two, hzero]

/-- At p_{i+1}, the exponent in encodeCore is exactly the i-th list entry. -/
theorem encodeCore_factorization_at_entry (xs : List Nat) (i : Nat)
    (hi : i < xs.length) :
    (encodeCore xs).factorization (primeAt (i + 1)) = xs[i]! := by
  unfold encodeCore
  rw [Nat.factorization_mul (by positivity) (sequencePrimeProduct_ne_zero xs)]
  have hzero :
      (2 ^ xs.length).factorization (primeAt (i + 1)) = 0 := by
    apply Nat.factorization_eq_zero_of_not_dvd
    intro hdvd
    have hdiv : primeAt (i + 1) ∣ 2 :=
      (primeAt_prime (i + 1)).dvd_of_dvd_pow hdvd
    have hle := Nat.le_of_dvd (by decide : 0 < 2) hdiv
    have hgt := primeAt_gt_two i
    omega
  have hentry := sequencePrimeProduct_factorization_at xs i hi
  simpa [Finsupp.add_apply, hzero] using hentry

/--
Injectivity of the source's Encode map. The proof uses unique prime
factorization rather than assuming a decoder or adding an axiom.
-/
theorem encodeSequence_injective : Function.Injective encodeSequence := by
  intro xs ys hxy
  have hcore : encodeCore xs = encodeCore ys := by
    calc
      encodeCore xs = encodeSequence xs + 1 :=
        (encodeSequence_add_one xs).symm
      _ = encodeSequence ys + 1 := congrArg (fun n => n + 1) hxy
      _ = encodeCore ys := encodeSequence_add_one ys
  have hlen :
      xs.length = ys.length := by
    have hfac := congrArg (fun n => n.factorization 2) hcore
    rw [encodeCore_factorization_at_two, encodeCore_factorization_at_two] at hfac
    exact hfac
  apply List.ext_get
  · exact hlen
  · intro i hix hiy
    have hfac :=
      congrArg (fun n => n.factorization (primeAt (i + 1))) hcore
    rw [encodeCore_factorization_at_entry xs i hix,
        encodeCore_factorization_at_entry ys i hiy] at hfac
    exact hfac

/-- The four natural coefficients of an element of ω⁴, in low-to-high order. -/
structure Code4 where
  a0 : Nat
  a1 : Nat
  a2 : Nat
  a3 : Nat
  deriving DecidableEq, Repr

/-- Exact source code for the unary function symbols U, Θ, and f_{a,i}. -/
def FunctionSymbol.code4 : FunctionSymbol → Code4
  | .U => ⟨8, 2, 0, 1⟩
  | .theta => ⟨8, 3, 0, 1⟩
  | .indexed a i => ⟨8, 4, i, a⟩

/-- Exact source code for the binary membership relation and r_{a,i}. -/
def RelationSymbol.code4 : RelationSymbol → Code4
  | .mem => ⟨9, 5, 0, 2⟩
  | .indexed a i => ⟨9, 6, i, a⟩

/-- The symbols used in finite strings of the quoted language L-hat. -/
inductive Symbol where
  | bot
  | imp
  | neg
  | exists
  | lparen
  | rparen
  | constant (index : Nat)
  | variable (index : Nat)
  | function (symbol : FunctionSymbol)
  | relation (symbol : RelationSymbol)
  deriving DecidableEq, Repr

/-- Exact ω⁴ coefficient tuple for each primitive symbol. -/
def Symbol.code4 : Symbol → Code4
  | .bot => ⟨0, 0, 0, 0⟩
  | .imp => ⟨1, 0, 0, 0⟩
  | .neg => ⟨2, 0, 0, 0⟩
  | .exists => ⟨3, 0, 0, 0⟩
  | .lparen => ⟨4, 0, 0, 0⟩
  | .rparen => ⟨5, 0, 0, 0⟩
  | .constant i => ⟨6, 0, i, 0⟩
  | .variable i => ⟨7, 1, i, 0⟩
  | .function f => f.code4
  | .relation r => r.code4

/-- Encode one ω⁴ symbol by applying the source's sequence code to its tuple. -/
noncomputable def Symbol.metaToken (s : Symbol) : Nat :=
  encodeSequence [s.code4.a0, s.code4.a1, s.code4.a2, s.code4.a3]

/-- Canonical token string for a term, using the source's primitive symbols. -/
def Term.symbols : Term → List Symbol
  | .var i => [.variable i]
  | .const i => [.constant i]
  | .app f args =>
      [.function f, .lparen] ++ args.flatMap Term.symbols ++ [.rparen]
termination_by t => sizeOf t
decreasing_by all_goals simp_wf

/--
Canonical token string for a formula. There are no comma tokens in the
source's primitive alphabet; argument counts are carried by symbol arities.
This is a parse-oriented serialization convention, with no new primitive
logical symbols.
-/
def Formula.symbols : Formula → List Symbol
  | .bot => [.bot]
  | .imp p q => [.lparen] ++ p.symbols ++ [.imp] ++ q.symbols ++ [.rparen]
  | .neg p => [.neg] ++ p.symbols
  | .exists i p => [.exists, .variable i, .lparen] ++ p.symbols ++ [.rparen]
  | .rel r args =>
      [.relation r, .lparen] ++ args.flatMap Term.symbols ++ [.rparen]
termination_by p => sizeOf p
decreasing_by all_goals simp_wf

/--
MetaCode(P): first encode each ω⁴ symbol tuple, then encode the resulting
finite sequence of symbol numbers. This follows the two-stage construction
stated in the original article.
-/
noncomputable def metaCode (P : Formula) : Nat :=
  encodeSequence (P.symbols.map Symbol.metaToken)

/-- Empty sequence has code zero under the author's -1 + 2^h product formula. -/
@[simp] theorem encodeSequence_nil : encodeSequence [] = 0 := by
  simp [encodeSequence, encodeCore, sequencePrimeProduct]

/-- First zero entry is coded by 1, fixing the length-prefix convention. -/
@[simp] theorem encodeSequence_single_zero : encodeSequence [0] = 1 := by
  simp [encodeSequence, encodeCore, sequencePrimeProduct, primeAt]

end Godel
end HakuiKoyori
