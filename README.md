# Hakui Koyori Number（博衣こより数）

**A long-term, Lean-formalized googology project inspired by Hakui Koyori's researcher, experiment, and science-girl motifs.**

- Project title: **Hakui Koyori Number**
- Repository: https://github.com/2503140kcsk-eng/D
- Status: **Phase 1 — universal comparison construction written; CI verification in progress**
- Audit baseline: 2026-11-03

> Independent fan-inspired mathematics project. It is not affiliated with or endorsed by Cover Corp. or Hololive.

## Research objective

Define a completely specified finite natural number HKN that exceeds the Large Number Garden Number (LNGN) construction, and certify the arithmetic theorem in Lean 4.

The published LNGN expression is described as

\[
\operatorname{LNGN}=f^{10}(b),\qquad b=10\uparrow^{10}10,
\]

where \(f^{10}\) means tenfold function composition.

## Current HKN construction

For a total function \(f:\mathbb N\to\mathbb N\), define the finite running maximum

\[
M_f(n)=\max\{f(0),f(1),\ldots,f(n)\}.
\]

Define one Koyori Spark transformation by

\[
S_f(n)=2^{M_f(n)+n+3}.
\]

Put

\[
A_f=S_f^{10}(b)
\]

and define

\[
\boxed{\operatorname{HKN}(f)=E^{A_f+1}(A_f+2),\qquad E(x)=2^x.}
\]

Here \(S_f^{10}\) means tenfold composition, and \(E^{A_f+1}\) means exactly \(A_f+1\) successive applications of exponentiation by 2. These are finite recursions on natural numbers.

### Main theorem

The Lean module HakuiKoyori/ExperimentalHierarchy.lean defines the functions and proves:

\[
\boxed{\forall f:\mathbb N\to\mathbb N,\quad
f^{10}(b)<S_f^{10}(b)<\operatorname{HKN}(f).}
\]

**No monotonicity assumption on \(f\) is needed.** The running maximum \(M_f\) is monotone, so \(S_f\) is monotone. Also \(f(n)<S_f(n)\) for every \(n\). Monotonicity of this majorant lifts pointwise strict domination through ten iterates.

The final tower exceeds \(A_f\) because it starts at \(A_f+2\) and performs \(A_f+1\) exponentiation steps.

The theorem is parametric in \(f\). To obtain a single closed HKN natural number for the published LNGN, the project must formally fix the source's semantic Garden function \(f\), not merely use an arbitrary function parameter.

## Proof sketch

For every \(n\), set \(t=M_f(n)+n+2\). Then

\[
f(n)\le M_f(n)\le t\le2^t<2^{t+1}=S_f(n).
\]

The inequality \(t\le2^t\) is proved by induction. Since \(M_f\) is a running maximum, it is monotone. Thus \(S_f\) is monotone. If \(f^k(b)<S_f^k(b)\), then

\[
f^{k+1}(b)<S_f(f^k(b))
\le S_f(S_f^k(b))=S_f^{k+1}(b).
\]

This uses monotonicity of \(S_f\), not monotonicity of \(f\).

## Remaining research gates

1. Freeze an authoritative transcription of the original definition and its coding conventions.
2. Formalize the source language, formula codes, meta-codes, and capture-avoiding substitution.
3. Formalize the recursive map \(\mathrm{CNF}:\mathbb N\to\varepsilon_0\).
4. Specify the theory \(T\), hierarchy \(U(\alpha)\), and satisfaction relation used by the source.
5. State the model/consistency assumptions and decide whether the intended \(f\)-value is canonical or model-relative.
6. Define the exact source function \(f\) in the chosen semantics and prove it total as a map \(\mathbb N\to\mathbb N\).
7. Instantiate the parametric theorem with that exact \(f\), giving a closed HKN natural number.
8. Complete independent type checking, axiom auditing, and mathematical review.

The original author's article does give a detailed syntactic and semantic construction and discusses building a hierarchy using ZFC plus a Grothendieck-universe axiom. We treat those claims as research inputs to formalize, not as already verified Lean results.

## No absolute largest finite number

There is no greatest natural number among all finitely definable numbers in unrestricted mathematics: if \(N\) is definable, then \(N+1\) is also definable and larger. “Largest googologism” is relative to a specified language, theory, notation, resource convention, or catalogue.

## Roles for supplied open-source projects

These projects are assigned complementary roles as references and possible independent tools. This table does **not** mean all their code was executed or that they certify the HKN proof.

| Project | Assigned role |
|---|---|
| [FLINT](https://github.com/flintlib/flint) | Exact integer, polynomial, and number-theory calculations for computable test cases |
| [TransfiniteOrdinalCalculator](https://github.com/MeniRosenfeld/TransfiniteOrdinalCalculator) | Exploratory ordinal/CNF calculations; not a proof checker |
| [basmat-2.x](https://github.com/koteitan/basmat-2.x) | Compare Bashicu matrix notation and bounded examples |
| [incremental-googology](https://github.com/hypcos/incremental-googology) | Survey fast-growing hierarchies, ordinal notations, and googological constructions |
| [bbchallenge-proofs](https://github.com/bbchallenge/bbchallenge-proofs) | Reproducibility and machine-certified proof discipline |
| [busy-beaver](https://github.com/jeff87654/busy-beaver) | Coq-checked Busy Beaver examples and proof engineering references |
| [cryptids](https://github.com/google-deepmind/cryptids) | Lean formalization patterns for computation and Turing-machine semantics |
| [Singular](https://github.com/Singular/Singular) | Optional independent algebra computations |
| [Macaulay2](https://github.com/Macaulay2/M2) | Optional commutative algebra and algebraic geometry |
| [GAP](https://github.com/gap-system/gap) | Finite-group and discrete combinatorial computations |
| [SymPy](https://github.com/sympy/sympy) | Symbolic cross-checks on finite computable fragments |
| [SageMath](https://github.com/sagemath/sage) | Number theory, combinatorics, and computable ordinal-code experiments |
| [Naproche](https://github.com/naproche/naproche) | Secondary natural-language proof checking |
| [cvc5](https://github.com/cvc5/cvc5) | Bounded SAT/SMT counterexample search; not proof of set-theoretic semantics |
| [LeanDojo-v2](https://github.com/lean-dojo/LeanDojo-v2) | Optional theorem retrieval and proof-assistant research |
| [mathlib4](https://github.com/leanprover-community/mathlib4) | Main Lean library |

## Verification policy

- Lean 4 and mathlib4 versions are pinned by lean-toolchain and lake-manifest.json.
- CI uses GitHub-hosted runners when available.
- CI enables nanoda with sorry disabled and axiom-audit.
- A green workflow is not treated as proof unless its logs show the intended library was actually built and the independent checks ran.
- No paid APIs or services are required for the proof core.

## Project files

- HakuiKoyori/Number.lean — exponentiation iteration and universal tower amplifier.
- HakuiKoyori/ExperimentalHierarchy.lean — Knuth-arrow seed, running maximum, Koyori Spark transform, and direct comparison theorem.
- docs/definition.md — exact mathematical definition.
- docs/large-number-garden-audit.md — source and semantic audit.
- Issue #1: https://github.com/2503140kcsk-eng/D/issues/1
