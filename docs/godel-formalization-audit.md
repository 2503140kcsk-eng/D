# LNGN source / Lean audit

Date: 2026-11-03

## Source hierarchy

The normative source for exact notation is the Japanese article by P進大好きbot, 「高階集合論を超えた1階述語論理」 (first posted 2019-12-03):

- https://googology.fandom.com/ja/wiki/ユーザーブログ:P進大好きbot/高階集合論を超えた1階述語論理
- The English page identifies itself as a summary of the Japanese article:
  https://googology.fandom.com/wiki/User_blog:P%E9%80%B2%E5%A4%A7%E5%A5%BD%E3%81%8Dbot/First_Order_Theory_beyond_Higher_Order_Set_Theory

The target language L has variables x_i, binary relation ∈, and unary function U. ZF_L includes the ZF axioms, with Separation and Replacement ranging over all L-formulas, including U.

Do not conflate three levels: the metatheory in which the construction is described, object language L, and quoted/formalized language ⌜L⌝.

## Exact symbol codes

The source's ordinal tags are:
- ⊥, →, ¬, ∃, (, ) have codes 0,1,2,3,4,5.
- Constant, Variable, Function, Relation have base tags 6,7,8,9.
- Number = ω, Index = ω², Arity = ω³.

A code in ω⁴ is represented by its unique low-to-high coefficient tuple (a0,a1,a2,a3), for ordinal ω³a3 + ω²a2 + ωa1 + a0.

| Symbol | Tuple (a0,a1,a2,a3) |
|---|---|
| c_i | (6,0,i,0) |
| x_i | (7,1,i,0) |
| U | (8,2,0,1) |
| Θ | (8,3,0,1) |
| f_{a,i} | (8,4,i,a) |
| ∈ | (9,5,0,2) |
| r_{a,i} | (9,6,i,a) |

The primitive logic uses ⊥, →, ¬, ∃ and parentheses. ∧, ∨, ∀, and equality are abbreviations, not additional primitive tags. The extra c_i, f_{a,i}, and r_{a,i} families support embeddings of other theories; the author says they are not needed for the final number except for the role of Θ.

## Formula syntax and substitution

Formula is the set of legal finite symbol strings. Formula-minus is the subset not containing Θ.

For a finite set of symbol strings S, New(S) is the *least* i for which x_i occurs in none of them. If P = ∃y(Q) and y occurs in replacement term t, the source's substitution rule first renames y to x_New({P,t,x}), then substitutes t for free x in the renamed formula. Substitution acts on variable symbols, not on the numerical subscripts of function or relation symbols.

Implementation:
- HakuiKoyori/GodelSyntax.lean defines raw Term and Formula ASTs, function/relation arities, WellFormed predicates, FormulaMinus, New, and substitutions.
- New is defined using Nat.find, and its freshness and minimality properties are proved.
- Term.subst leaves constants and symbol indices unchanged.
- Formula.substFuel implements the source's binder-renaming branch.

Representation boundary: the article specifies finite symbol strings. The Lean module uses an AST and a deterministic symbols serialization with the same primitive token alphabet and parentheses. The proof that this serialization is bijective with every source-legal string remains open; no such equivalence is claimed yet.

## Encode and MetaCode

The source uses zero-based prime indexing p_0=2, p_1=3, p_2=5, ... and defines, for a sequence a of length h,

Encode(a) = 2^h * product_{i<h} p_{i+1}^{a_i} - 1.

The length marker uses prime 2; entry primes start at 3. This separation is essential for injectivity.

Lean's encodeSequence is the same natural-number formula, using truncated subtraction (the positive product makes it agree with minus one). Injectivity is proved by unique prime factorization:
1. the exponent of 2 recovers h;
2. the exponent of p_{i+1} recovers a_i;
3. unique factorization therefore recovers the whole list.

The main theorem is Godel.encodeSequence_injective in HakuiKoyori/GodelCode.lean. That file also defines the exact symbol tuples, token serialization, inner symbol codes, and two-stage MetaCode on well-formed formulas.

## Remaining source definitions

The Japanese article defines Formalise(n) as a quoted formula uniquely defining the von Neumann finite ordinal n, with x_0 as its only free variable. It gives Formalise(0) = ¬∃x_1(x_1 ∈ x_0), and describes general n as 0 plus 1 repeated n times. A fully expanded recursive string grammar for positive n is not supplied in the article text; this must be explicitly fixed in a later implementation rather than guessed.

Code(P) is Formalise(MetaCode(P)). Henkin_{i,P}, for i∈ω and P∈Formula-minus, says that if P has an x_i witness, then, when Code(P) holds, substituting Θ(x_0) for free x_i also satisfies P. The Henkin extension is ZFC_⌜L⌝ plus this schema.

The source defines T = ZF_L ∪ {U1,U2,U3}:
- U1: every ordinal-indexed U(α) satisfies the Henkin-extended formalized ZFC theory.
- U2: the quoted interpretation of U inside U(α) maps β∈α to U(β).
- U3: each U(α) has domain V_β for some ordinal β, with interpreted membership agreeing with actual membership on that domain.

It then defines CNF: ℕ→ε₀ by prime factorization of i+1, defines IsDefinition and Definable using satisfaction in U(CNF(i)), and defines f(n) as the finite sum of the m values with bounded witnesses i and formula P satisfying the source predicates. LNGN is f iterated ten times at 10↑^10 10.

## Scope and honest status

| Layer | Status |
|---|---|
| Exact symbol coefficient tuples | Implemented |
| Raw formula/term AST and arity predicates | Implemented |
| Least New({P,t,x}) and its properties | Implemented |
| Capture-avoiding substitution operation | Implemented |
| Source finite-sequence Encode | Implemented |
| Injectivity of Encode | Lean theorem added |
| Two-stage MetaCode | Defined on the canonical AST serialization |
| AST/string grammar equivalence | Open |
| Formalise, Code, Henkin sentences/schema | Open |
| Full structures, satisfaction, U1-U3 | Open |
| CNF, IsDefinition, Definable, source f | Open |
| Concrete closed HKN(LNGN) | Open |

The semantic gates are not cosmetic: the project still needs a formalized ZFC axiom collection, a hierarchy satisfying U1-U3, satisfaction for the source language, the CNF recursion, a finite-sum index proof, and a fixed standard-natural interpretation of f. Therefore the current universal HKN theorem is not yet instantiated with the source's f.

## Koyori lab design

The official profile describes Hakui Koyori as the holoX researcher, research-minded and curious, and uses #こより実験中. The project maps those motifs to technical components: the symbol inventory is the reagent catalogue; the prime-power code is a sample label; New is contamination control during substitution; and U(CNF(i)) satisfaction is a model assay. These are design metaphors, not mathematical evidence or official Hololive concepts.

Official profile: https://hololive.hololivepro.com/talents/hakui-koyori

This is an independent fan-inspired research project, not a Hololive or Cover Corp collaboration.
