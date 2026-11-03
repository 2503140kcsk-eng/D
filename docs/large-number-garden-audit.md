# Large Number Garden Number — source and semantics audit

Audit date: 2026-11-03.

## 1. Original source and stated expression

The source located for this project is the author-posted article:

- P進大好きbot, 「高階集合論を超えた1階述語論理」, 2019-12-03.
- Article transcription/mirror: https://googology.fandom.com/ja/wiki/ユーザーブログ:P進大好きbot/高階集合論を超えた1階述語論理
- Related number entry: https://googology.fandom.com/wiki/Large_Number_Garden_Number

The stated number is

\[
\operatorname{LNGN}=f^{10}(10\uparrow^{10}10).
\]

Here \(f^{10}\) means tenfold function composition, not the pointwise tenth power.

## 2. The source gives a substantial construction

The original article describes:

1. A first-order set-theoretic language with a unary structure function symbol \(U\).
2. Finite strings, symbols, formula syntax, and a numerical encoding of symbol sequences.
3. Formula/meta-formula codes and a capture-avoiding substitution convention using a fresh-variable selection.
4. A theory \(T=\mathrm{ZF}_L\cup\{U1,U2,U3\}\).
5. A hierarchy \(U(\alpha)\) of structures, with axioms imposing model, coherence, and rank-segment requirements.
6. A recursive map \(\mathrm{CNF}:\mathbb N\to\varepsilon_0\), intended to cover ordinals below \(\varepsilon_0\).
7. A definition predicate based on unique satisfaction in \(U(\mathrm{CNF}(i))\).
8. A function \(f(n)\) obtained by a finite sum of natural values satisfying bounded formula/code conditions, with each defining formula required to determine a unique value.
9. The final tenfold iterate at the Knuth-arrow seed.

The author also discusses constructing a suitable increasing hierarchy using ZFC together with a Grothendieck-universe axiom. Therefore the number should not be dismissed as merely an informal label.

## 3. Formal details to reproduce exactly

The article describes the following components. Each must be transcribed with the original conventions before porting it to Lean:

- Symbol and formula coding, including finite-sequence encoding.
- MetaCode and the bounded code conditions in the definition of f.
- The exact freshness predicate and substitution procedure that avoids variable capture.
- The recursive prime-factor definition of CNF(i), whose image is intended to be the ordinals below epsilon-zero.
- The exact axioms U1, U2, and U3, including domains and structure-coherence constraints.
- The satisfaction relation used to interpret formulas in U(CNF(i)).
- The finite-sum convention and uniqueness predicate defining f(n).

A convenient approximation is not the same object as the source-defined Garden function.

## 4. Semantic questions still open in this project

Three different matters must not be conflated:

1. Syntax: the formulas and codes are finitely specified.
2. Theory/model assumptions: T, its consistency or relative-consistency strength, and existence of a hierarchy satisfying its axioms.
3. Semantic value: the standard natural-number function f determined by the intended hierarchy and satisfaction relation.

The original article discusses a model-construction route under strong set-theoretic assumptions. This project has not yet proved in Lean that the relevant hierarchy exists from the declared assumptions, nor that all admissible hierarchies give the same standard-natural-number value of f. It has also not selected one canonical hierarchy in a formal semantic framework.

This does **not** prove that LNGN is inconsistent or undefined. It means only that this repository has not yet formalized and fixed the semantic object needed for a concrete closed instantiation.

## 5. Why the current HKN comparison is robust

The current theorem is parameterized by an arbitrary total function \(f:\mathbb N\to\mathbb N\):

\[
f^{10}(B)<\operatorname{HKN}(f),\qquad B=10\uparrow^{10}10.
\]

It requires neither computability nor monotonicity of f. Once the source's semantics is formalized as one total natural-number function, the comparison can be instantiated without proving any extra growth or monotonicity property of that f.

The open task is to formalize the exact source function f—not to prove the arithmetic comparison again.

## 6. No absolute maximum

No greatest finite natural number exists among all numbers definable in unrestricted mathematics: for any N, N+1 is larger. Any “largest googologism” ranking is relative to a restricted language, theory, convention, or catalogue.


## 7. Formalization increment (2026-11-03)

The source transcription, exact symbol tuples, least-fresh-variable convention, capture-avoiding substitution, prime indexing, sequence Encode, and its injectivity proof are recorded in [godel-formalization-audit.md](godel-formalization-audit.md). Lean modules added on the review branch:

- `HakuiKoyori/GodelSyntax.lean`
- `HakuiKoyori/GodelCode.lean`

The Encode proof extracts the sequence length from the exponent of 2 and each element from the exponent of its indexed prime. This uses the source convention `p_0=2`, with the first element encoded using `p_1=3`. The AST/string grammar equivalence, `Formalise`, `Code`, Henkin schema, structures/satisfaction, `U1`–`U3`, `CNF`, and the source-semantic Garden function remain open. The new branch is pending GitHub Actions; the previous main-branch CI result does not certify these added modules.
