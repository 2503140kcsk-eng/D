import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Omega

/-!
# Exact object-language syntax and substitution for the LNGN source

This module separates the source's object language from Lean's own syntax.
It keeps variable indices and function/relation-symbol indices as different
fields: substitution changes variable tokens only and never rewrites indices.

The constructors use a compact AST for the source's primitive logical
vocabulary: bottom, implication, negation, and existential quantification.
Conjunction, disjunction, universal quantification, and equality are not
primitive constructors here; the source treats them as abbreviations.
-/

namespace HakuiKoyori
namespace Godel

/-- The arity/index data attached to a function symbol in the quoted language. -/
inductive FunctionSymbol where
  | U
  | theta
  | indexed (arity index : Nat)
  deriving DecidableEq, Repr

/-- Arity of a function symbol. -/
def FunctionSymbol.arity : FunctionSymbol → Nat
  | .U => 1
  | .theta => 1
  | .indexed a _ => a

/-- The arity/index data attached to a relation symbol in the quoted language. -/
inductive RelationSymbol where
  | mem
  | indexed (arity index : Nat)
  deriving DecidableEq, Repr

/-- Arity of a relation symbol. -/
def RelationSymbol.arity : RelationSymbol → Nat
  | .mem => 2
  | .indexed a _ => a

/--
Terms of the quoted first-order language.

An application node is raw syntax. Its arity side-condition is recorded by
Term.WellFormed; keeping it as a predicate makes the recursive operations
simple while still allowing every admitted term to be checked explicitly.
-/
inductive Term where
  | var (index : Nat)
  | const (index : Nat)
  | app (symbol : FunctionSymbol) (args : List Term)
  deriving DecidableEq, Repr

/-- Raw formulas in the source's primitive logical vocabulary. -/
inductive Formula where
  | bot
  | imp (left right : Formula)
  | neg (body : Formula)
  | exists (variable : Nat) (body : Formula)
  | rel (symbol : RelationSymbol) (args : List Term)
  deriving DecidableEq, Repr

/-- The exact arity and recursive well-formedness condition for terms. -/
def Term.WellFormed : Term → Prop
  | .var _ => True
  | .const _ => True
  | .app f args => args.length = f.arity ∧ ∀ t ∈ args, t.WellFormed

/-- The exact arity and recursive well-formedness condition for formulas. -/
def Formula.WellFormed : Formula → Prop
  | .bot => True
  | .imp p q => p.WellFormed ∧ q.WellFormed
  | .neg p => p.WellFormed
  | .exists _ p => p.WellFormed
  | .rel r args => args.length = r.arity ∧ ∀ t ∈ args, t.WellFormed

/--
All variable-symbol indices occurring in a term, including repetitions.
Function-symbol and relation-symbol subscripts are intentionally excluded.
-/
def Term.varIndices : Term → List Nat
  | .var i => [i]
  | .const _ => []
  | .app _ args => args.flatMap Term.varIndices
termination_by t => sizeOf t
decreasing_by all_goals simp_wf

/--
All variable-symbol indices occurring in a formula, including bound and free
occurrences. This matches the source's New(S), which checks whether the
variable symbol occurs anywhere in the finite symbol strings.
-/
def Formula.varIndices : Formula → List Nat
  | .bot => []
  | .imp p q => p.varIndices ++ q.varIndices
  | .neg p => p.varIndices
  | .exists i p => i :: p.varIndices
  | .rel _ args => args.flatMap Term.varIndices
termination_by p => sizeOf p
decreasing_by all_goals simp_wf

/-- A recursive maximum for a finite list of natural numbers. -/
def listMax : List Nat → Nat
  | [] => 0
  | a :: as => max a (listMax as)

/-- Every member of a finite list is bounded by listMax. -/
theorem le_listMax {xs : List Nat} {n : Nat} (h : n ∈ xs) :
    n ≤ listMax xs := by
  induction xs with
  | nil =>
      simp at h
  | cons a as ih =>
      simp only [List.mem_cons] at h
      rcases h with h | h
      · subst n
        exact Nat.le_max_left _ _
      · exact le_trans (ih h) (Nat.le_max_right _ _)

/-- The successor of listMax is not in the list. -/
theorem listMax_succ_not_mem (xs : List Nat) :
    listMax xs + 1 ∉ xs := by
  intro h
  have hb := le_listMax h
  omega

/-- Existence proof used to define the source's least fresh variable index. -/
def freshVariableExists (P : Formula) (t : Term) (x : Nat) :
    ∃ i, i ∉ (P.varIndices ++ t.varIndices ++ [x]) := by
  let xs := P.varIndices ++ t.varIndices ++ [x]
  refine ⟨listMax xs + 1, ?_⟩
  exact listMax_succ_not_mem xs

/--
New({P,t,x}): the least variable index whose variable symbol occurs nowhere
in the formula, replacement term, or target variable. Nat.find makes the
leastness part of the definition, not merely a freshness heuristic.
-/
noncomputable def newVarIndex (P : Formula) (t : Term) (x : Nat) : Nat :=
  Nat.find (freshVariableExists P t x)

/-- The selected variable is absent from every source object in New. -/
theorem newVarIndex_fresh (P : Formula) (t : Term) (x : Nat) :
    newVarIndex P t x ∉ (P.varIndices ++ t.varIndices ++ [x]) :=
  Nat.find_spec (freshVariableExists P t x)

/-- The selected fresh index is the least index satisfying the freshness test. -/
theorem newVarIndex_minimal (P : Formula) (t : Term) (x j : Nat)
    (hj : j ∉ (P.varIndices ++ t.varIndices ++ [x])) :
    newVarIndex P t x ≤ j :=
  Nat.find_min' (freshVariableExists P t x) hj

/--
Rename occurrences of a variable in a term. Since terms have no binders,
every occurrence of old is free. Symbol indices and arities are unchanged.
-/
def Term.renameVar (old fresh : Nat) : Term → Term
  | .var i => .var (if i = old then fresh else i)
  | .const i => .const i
  | .app f args => .app f (args.map (fun a => a.renameVar old fresh))
termination_by t => sizeOf t
decreasing_by all_goals simp_wf

/--
Rename free occurrences in a formula. A quantifier binding old blocks
renaming below it. The source's New condition guarantees that fresh does
not occur anywhere in the complete formula being processed.
-/
def Formula.renameFree (old fresh : Nat) : Formula → Formula
  | .bot => .bot
  | .imp p q => .imp (p.renameFree old fresh) (q.renameFree old fresh)
  | .neg p => .neg (p.renameFree old fresh)
  | .exists y p =>
      if y = old then .exists y p
      else .exists y (p.renameFree old fresh)
  | .rel r args => .rel r (args.map (fun t => t.renameVar old fresh))
termination_by p => sizeOf p
decreasing_by all_goals simp_wf

/-- Capture-avoiding substitution on terms. -/
def Term.subst (x : Nat) (replacement : Term) : Term → Term
  | .var i => if i = x then replacement else .var i
  | .const i => .const i
  | .app f args => .app f (args.map (fun a => a.subst x replacement))
termination_by t => sizeOf t
decreasing_by all_goals simp_wf

/--
Fuelled implementation of the source's substitution operation.

At exists y P, if y occurs in the replacement term, the binder is first
renamed to New({whole formula, replacement, target}), then substitution
continues in the renamed body. This is precisely the source's stated
capture-avoidance convention. If the binder is the target and no renaming is
needed, substitution stops below that binder because those occurrences are
not free.
-/
def Formula.substFuel : Nat → Formula → Nat → Term → Formula
  | 0, P, _, _ => P
  | n + 1, .bot, _, _ => .bot
  | n + 1, .imp p q, x, t =>
      .imp (substFuel n p x t) (substFuel n q x t)
  | n + 1, .neg p, x, t =>
      .neg (substFuel n p x t)
  | n + 1, .rel r args, x, t =>
      .rel r (args.map (fun a => a.subst x t))
  | n + 1, P@(.exists y body), x, t =>
      if hy : y ∈ t.varIndices then
        let z := newVarIndex P t x
        .exists z (substFuel n (body.renameFree y z) x t)
      else if y = x then
        .exists y body
      else
        .exists y (substFuel n body x t)
termination_by fuel _ _ _ => fuel
decreasing_by all_goals simp_wf

/-- The source's capture-avoiding substitution operation. -/
def Formula.subst (P : Formula) (x : Nat) (replacement : Term) : Formula :=
  substFuel (sizeOf P + 1) P x replacement

/-- Replacing a variable by a term performs the expected operation. -/
theorem Term.subst_target (x : Nat) (t : Term) :
    (Term.var x).subst x t = t := by
  rfl

/-- A different variable is unchanged by term substitution. -/
theorem Term.subst_other {x y : Nat} (h : y ≠ x) (t : Term) :
    (Term.var y).subst x t = Term.var y := by
  simp [Term.subst, h]

/-- Constants are not altered by variable substitution. -/
theorem Term.subst_const (x i : Nat) (t : Term) :
    (Term.const i).subst x t = Term.const i := by
  rfl

/--
The source's Formula-minus: formulas in which the special unary function
symbol Theta does not occur. Constants and indexed function/relation symbols
remain permitted.
-/
def Term.thetaFree : Term → Prop
  | .var _ => True
  | .const _ => True
  | .app .theta _ => False
  | .app _ args => ∀ t ∈ args, t.thetaFree
termination_by t => sizeOf t
decreasing_by all_goals simp_wf

def Formula.thetaFree : Formula → Prop
  | .bot => True
  | .imp p q => p.thetaFree ∧ q.thetaFree
  | .neg p => p.thetaFree
  | .exists _ p => p.thetaFree
  | .rel _ args => ∀ t ∈ args, t.thetaFree
termination_by p => sizeOf p
decreasing_by all_goals simp_wf

/-- Valid object-language formulas, excluding malformed arity nodes. -/
abbrev WellFormedFormula := { P : Formula // P.WellFormed }

/-- Formula-minus: valid formulas in which the special symbol Theta is absent. -/
abbrev FormulaMinus := { P : Formula // P.WellFormed ∧ P.thetaFree }

end Godel
end HakuiKoyori
