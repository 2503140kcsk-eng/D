# Hakui Koyori Number — precise mathematical definition

## 1. Domain and finite recursion

Let \(\mathbb N=\{0,1,2,\ldots\}\), and let \(f:\mathbb N\to\mathbb N\) be any total function. No monotonicity or computability assumption on \(f\) is needed for the comparison theorem.

For \(g:\mathbb N\to\mathbb N\), define its iterate by

\[
g^{[0]}(x)=x,\qquad g^{[r+1]}(x)=g(g^{[r]}(x)).
\]

The superscript denotes composition, not ordinary exponentiation.

## 2. Knuth-arrow seed

Define \(U_0(a,b)=ab\), and recursively

\[
U_{r+1}(a,0)=1,\qquad
U_{r+1}(a,b+1)=U_r(a,U_{r+1}(a,b)).
\]

This is a finite recursion on arrow rank and right argument. Put

\[
B:=U_{10}(10,10)=10\uparrow^{10}10.
\]

## 3. Garden comparator

The published comparator is

\[
L_f:=f^{[10]}(B).
\]

The source's semantic function \(f\) remains an explicit function parameter in the present Lean theorem. Formalizing the source's model hierarchy is a separate obligation recorded in large-number-garden-audit.md.

## 4. Koyori running-maximum envelope

For each \(n\in\mathbb N\), define

\[
M_f(n):=\max_{0\le j\le n}f(j).
\]

This is the maximum of a nonempty finite set of natural numbers, so it exists for every n, even if f is noncomputable.

Define

\[
S_f(n):=2^{M_f(n)+n+3}.
\]

Two properties hold for every total f:

1. Pointwise strict domination:
   \[
   f(n)<S_f(n).
   \]
   Proof: set \(t=M_f(n)+n+2\). Since \(f(n)\le M_f(n)\), we have \(f(n)\le t\). The elementary lemma \(t\le2^t\) gives \(f(n)\le2^t\), while \(2^t<2^{t+1}=S_f(n)\).

2. Monotonicity of the majorant:
   \[
   a\le b\Longrightarrow M_f(a)\le M_f(b)
   \Longrightarrow S_f(a)\le S_f(b).
   \]
   This remains true even if f itself is not monotone.

## 5. Ten Koyori Spark experiments

Set

\[
A_f:=S_f^{[10]}(B).
\]

Because \(S_f\) is monotone and \(f(n)<S_f(n)\) pointwise, induction gives

\[
f^{[r]}(B)<S_f^{[r]}(B)\qquad(r\ge1).
\]

For the induction step, if \(f^{[r]}(B)<S_f^{[r]}(B)\), then

\[
\begin{aligned}
f^{[r+1]}(B)
&=f(f^{[r]}(B))\\
&<S_f(f^{[r]}(B))\\
&\le S_f(S_f^{[r]}(B))\\
&=S_f^{[r+1]}(B).
\end{aligned}
\]

The middle inequality uses monotonicity of \(S_f\), not f.

In particular,

\[
L_f=f^{[10]}(B)<A_f.
\]

## 6. Final tower amplification

Let \(E(x)=2^x\). For \(A\in\mathbb N\), define

\[
T_A(0)=A+2,\qquad T_A(r+1)=2^{T_A(r)}.
\]

Define

\[
\boxed{\operatorname{HKN}(f):=T_{A_f}(A_f+1).}
\]

Equivalently, exactly \(A_f+1\) exponentiation-by-2 stages are applied, starting at \(A_f+2\).

Every stage satisfies \(x\le2^x\), hence

\[
A_f+2\le T_{A_f}(A_f+1)
\]

and therefore \(A_f<\operatorname{HKN}(f)\).

Combining the inequalities:

\[
\boxed{f^{[10]}(10\uparrow^{10}10)
<A_f
<\operatorname{HKN}(f).}
\]

Thus the theorem proves strict domination of the corresponding Garden comparator for every total \(f:\mathbb N\to\mathbb N\).

## 7. Closed-numeral status

The expression \(\operatorname{HKN}(f)\) is fully specified for every total natural-valued function f. The Lean theorem is universal in f. This is a rigorous parametric construction, not an informal size claim.

A single closed numeral for the published LNGN still requires formally fixing the source's semantic function f and its model hierarchy. The project will not substitute an arbitrary function and call it the source's f.

## 8. Formal source

- HakuiKoyori/Number.lean: the lemma \(t\le2^t\), finite exponentiation iteration, and tower amplifier.
- HakuiKoyori/ExperimentalHierarchy.lean: Knuth-arrow seed, \(M_f\), \(S_f\), iterate comparison, and HKN theorem.
