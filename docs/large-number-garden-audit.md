# Large Number Garden Number: source audit

Audit date: 2026-11-03.

## 1. Source identity

The source-level definition located for this project is the author-posted article:

- P進大好きbot, 「高階集合論を超えた1階述語論理」, posted 2019-12-03.
- Mirror/transcription: https://googology.fandom.com/ja/wiki/ユーザーブログ:P進大好きbot/高階集合論を超えた1階述語論理
- The related number entry: https://googology.fandom.com/wiki/Large_Number_Garden_Number

The source identifies the comparison number as

\[
L=f^{10}(10\uparrow^{10}10).
\]

The arrow notation is Knuth's up-arrow notation; \(f^{10}\) denotes tenfold function composition.

## 2. Described theory

The article describes a first-order set-theoretic language \(L\) extended by a unary function symbol \(U\), then introduces an axiom system

\[
T=\mathrm{ZF}_L\cup\{U1,U2,U3\}.
\]

In the article's description:

- \(U1\) requires each ordinal-indexed structure \(U(\alpha)\) to satisfy a Henkin-expanded formalization of ZFC.
- \(U2\) imposes coherence of the interpretation of \(U\) between these structures.
- \(U3\) relates the domain of each \(U(\alpha)\) to a von Neumann rank segment.
- A coding of finite symbol sequences and formulas is introduced.
- An ordinal coding map \(\mathrm{CNF}:\mathbb N\to\varepsilon_0\) is specified recursively.
- A formula is treated as a definition when it has a unique satisfying value.
- \(\mathrm{Definable}(m,i,P)\) is evaluated using satisfaction in \(U(\mathrm{CNF}(i))\).
- \(f(n)\) is the sum of the natural numbers \(m\) admitted by the bounded formula/code conditions.

The article explicitly presents the construction as an uncomputable function and says that the strength is intended to come from definability / satisfaction across the hierarchy of structures.

## 3. Why our comparison is currently parametric

The HKN arithmetic proof needs only a natural number \(L\). It does not need to evaluate \(f\), which is not computationally available.

However, the current repository has not yet formalized all of the following source-level obligations:

1. The full syntax and exact Gödel/meta-code of the source language.
2. Capture-avoiding substitution, including the source's fresh-variable convention.
3. The recursive \(\mathrm{CNF}\) encoding and its claimed coverage of ordinals below \(\varepsilon_0\).
4. The exact formal satisfaction predicate used for \(U(\mathrm{CNF}(i))\).
5. The intended interpretation of the model hierarchy \(U\).
6. Consistency / relative consistency assumptions needed for the theory \(T\).
7. Whether the resulting standard-natural-number value of \(f^{10}(10\uparrow^{10}10)\) is invariant across admissible interpretations.

The existence of a syntactic formula in an axiom system, the consistency of that system, and the selection of a particular standard-model value are three different claims. They must not be conflated.

## 4. Current judgment

The source gives a substantial and concrete construction, so it should not be dismissed as a mere informal name. At the same time, this project has not independently established a unique, interpretation-independent standard natural number for every semantic component.

Therefore the main Lean theorem is stated for arbitrary \(L:\mathbb N\). It is valid under every possible natural-number interpretation of the comparison target:

\[
\forall L\in\mathbb N,\quad L<\operatorname{HKN}(L).
\]

The unconditional claim “the concrete HKN is larger than the concrete LNGN” is withheld until the seven obligations above are discharged.

## 5. No absolute largest finite integer

There is no greatest finite natural number among all numbers definable in unrestricted mathematics: if \(N\) is definable, then \(N+1\) is also definable and is larger. Labels such as “largest valid googologism” are relative to a community's accepted definition rules, language limits, and current catalogue; they are not a theorem asserting a global maximum of the natural numbers.
