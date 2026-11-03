# Hakui Koyori Number（博衣こより数）

**A long-term, formally audited googology project inspired by Hakui Koyori's researcher / experiment motif.**

- Repository: [2503140kcsk-eng/D](https://github.com/2503140kcsk-eng/D)
- Project title: **Hakui Koyori Number**
- Status: **Phase 0 — comparator-parametric construction formalized; Large Number Garden Number instantiation remains open**
- Date: 2026-11-03

## Research objective

Develop a completely specified finite natural number, with a machine-checked definition and comparison proof. The first comparison target is the Large Number Garden Number (LNGN), reported as

\[
L = f^{10}(10\uparrow^{10}10).
\]

We do not assume that the phrase “largest well-defined googologism” means a mathematically absolute maximum. In unrestricted mathematics, every fixed finite natural number \(N\) is exceeded by the equally definable number \(N+1\). Any “largest” claim is relative to a stated language, theory, size convention, and catalogue.

## First construction: Koyori Spark Iteration

For every natural-number benchmark \(L\), define a finite sequence by primitive recursion:

\[
K_L(0)=L+2,\qquad K_L(r+1)=2^{K_L(r)}.
\]

Define the benchmark-relative Hakui Koyori number by

\[
\boxed{\operatorname{HKN}(L)=K_L(L+1).}
\]

The Lean development proves, for every \(L\in\mathbb N\),

\[
\boxed{L+2\leq \operatorname{HKN}(L),\quad L<\operatorname{HKN}(L).}
\]

Thus, **once LNGN has been fixed as a particular natural number**, substituting that value for \(L\) gives a finite integer that is strictly larger. The recursion performs \(L+1\) successive exponentiation stages, starting from \(L+2\).

This is a real proof of a parametric theorem, not yet a proof that the published LNGN specification denotes one interpretation-independent standard natural number. That separate foundation remains an explicit research gate.

## Why “Koyori Spark”?

The construction uses only mathematical content, not private information about the performer. The official Hololive profile describes Koyori as the researcher of Secret Society holoX, emphasizes her curiosity and research-mindedness, and lists “Kokoro,” the robot coyote companion in her lab-coat pocket. Cover Corp's announcement describes the 2nd album *Chemical Spark* as centered on her “science girl” concept. These motivate the public-facing metaphor of repeated, self-amplifying experiments.

This is an independent fan-inspired mathematical project. It is **not** an official Hololive / Cover Corp project and does not imply endorsement.

## Formal verification

- Lean 4 + mathlib4.
- No sorry, no project axioms, and no admitted theorem in the initial arithmetic core.
- GitHub Actions CI is configured to compile the Lean library.
- The theorem is parameterized by an arbitrary Nat, so it does not smuggle in an unverified definition of LNGN.

Main file: [HakuiKoyori/Number.lean](HakuiKoyori/Number.lean)

## LNGN audit gate

The original 2019 author-posted description defines the comparison object using a theory \(T\), a hierarchy of structures \(U(\alpha)\), a formula-coding map, a satisfaction/definability predicate, and an uncomputable function \(f\). Before claiming an unconditional HKN-over-LNGN result, we must:

1. Freeze the exact source text and all coding conventions.
2. Formalize the syntax, coding, substitution, and ordinal map.
3. Specify what interpretation/model of \(T\) determines the satisfaction statements.
4. Separate consistency assumptions from definitions and from the intended standard-natural-number value.
5. Prove that the resulting comparator is a unique natural number under the declared assumptions, or explicitly state the relative/model-dependent semantics.

See [docs/large-number-garden-audit.md](docs/large-number-garden-audit.md).

## Division of labour for the supplied open-source projects

These projects are independent reference tools, not agents that have been run or proof certificates for HKN:

| Project | Intended role |
|---|---|
| FLINT | Exact integer / polynomial arithmetic and cross-checks for computable test instances |
| TransfiniteOrdinalCalculator | Exploratory ε₀ Cantor-normal-form calculations; not a proof checker |
| basmat-2.x | Compare notation behaviour on finite test cases |
| incremental-googology | Map fast-growing notation and identify hierarchy assumptions |
| bbchallenge-proofs | Proof-writing and reproducibility standards for machine-certified results |
| busy-beaver | Coq-checked Busy Beaver examples and proof discipline |
| cryptids | Lean 4 examples connecting Turing-machine semantics with mathematical statements |
| Singular | Independent polynomial / ideal computation if the encoding work needs it |
| Macaulay2 | Commutative algebra and algebraic-geometry computations if later required |
| GAP | Finite group and combinatorial structure checks |
| SymPy | Independent symbolic simplification on finite, computable fragments |
| SageMath | Cross-checks for number theory, combinatorics, and ordinal-code experiments |
| Naproche | Human-readable proof checking as a secondary presentation audit |
| cvc5 | SAT/SMT counterexample search for bounded encodings; not a proof of class-theoretic semantics |
| LeanDojo-v2 | Optional theorem retrieval / proof-assistant research; no paid inference is assumed |
| mathlib4 | Primary Lean mathematics library and kernel-checked theorem development |

## Long-term milestones

- [x] Create the project specification and title the repository contents.
- [x] Define a finite, total, benchmark-parametric Koyori Spark iteration.
- [x] Prove the strict comparison theorem for every natural-number benchmark in Lean source.
- [ ] Obtain and freeze an authoritative LNGN source transcription.
- [ ] Formalize the exact LNGN coding and theory assumptions.
- [ ] Resolve the model/interpretation and consistency obligations.
- [ ] Instantiate \(L\) and prove the unconditional comparison in the declared foundation.
- [ ] Add independent review and reproducible CI evidence.

**Current claim boundary:** HKN(L) is fully defined and formally proved larger than L for every natural L. The concrete instantiation at the published LNGN remains conditional until the LNGN audit gate is discharged.
