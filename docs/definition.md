# Mathematical definition: Hakui Koyori Number

## 1. Domain

All parameters and values are in the standard natural numbers \(\mathbb N=\{0,1,2,\ldots\}\).

Let \(L\in\mathbb N\) be a fixed comparator.

## 2. Koyori Spark iteration

Define \(K_L:\mathbb N\to\mathbb N\) by primitive recursion:

\[
K_L(0)=L+2,
\]
\[
K_L(r+1)=2^{K_L(r)}.
\]

This is a total finite recursion for every natural input \(r\). It invokes only natural-number addition and exponentiation. There is no limiting process, infinite sum, unbounded search, oracle, or appeal to an undefined function.

## 3. Number

\[
\boxed{\operatorname{HKN}(L):=K_L(L+1).}
\]

Equivalently, this is a tower-like iteration with initial seed \(L+2\) and exactly \(L+1\) exponentiation steps.

The project uses “Hakui Koyori Number” for this benchmark-relative construction until a canonical formal natural-number value for the published LNGN comparator is fixed. On instantiation, the intended benchmark is \(L=\operatorname{LNGN}\).

## 4. Proof

First prove by induction on \(n\) that

\[
n\le 2^n.
\]

- Base case: \(0\le 1\).
- Inductive step: assume \(n\le 2^n\). Since \(2^n\ge1\),
  \[
  n+1\le 2^n+1\le 2^n+2^n=2^{n+1}.
  \]

Then prove by induction on \(r\) that

\[
L+2\le K_L(r).
\]

- At \(r=0\), equality holds.
- If \(L+2\le K_L(r)\), then
  \[
  L+2\le K_L(r)\le 2^{K_L(r)}=K_L(r+1),
  \]
  where the second inequality is the first lemma.

Taking \(r=L+1\) gives

\[
L+2\le K_L(L+1)=\operatorname{HKN}(L),
\]
hence \(L<\operatorname{HKN}(L)\).

The Lean source checks these claims in the project kernel.

## 5. Exact scope of the result

The theorem is **uniform**: it holds for every natural number \(L\), independently of how large or how difficult to compute \(L\) is.

It is not yet an unconditional instantiation theorem for LNGN. To obtain that, the LNGN construction must first be shown to denote a fixed natural number under a stated interpretation of its defining theory. If multiple interpretations yield different values, the project must either select and justify one interpretation or publish a family of relative HKN values.

## 6. What “overwhelmingly larger” means here

The formal comparison is strict and robust: the iteration count itself is \(L+1\), and the seed is \(L+2\). The resulting number is therefore an \(L+1\)-stage nested exponentiation, not merely \(L+1\) added to the benchmark.

The Lean theorem currently certifies the lower bound \(\operatorname{HKN}(L)\ge L+2\). A separate hierarchy-comparison paper may study its exact placement among fast-growing functions; no unsupported claim that it dominates every uncomputable function is made.
