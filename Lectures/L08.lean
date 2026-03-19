import Proofs.Lang
import Proofs.Autom
import Proofs.Kleene

-- Regular expressions
-- grep




-- * Regular Expression is just a tree representation of a language

/-
'·' -> concatenation
'+' -> choice -> this is '|' normally
  -- This is the **Union** operator in practice, as RE is defined as trees, each RE has 2 nodes associated with it,
    -- so the RE is just the **Union** of both of those languages

  -- this is also why we need to define it recursively, because we need to recursively check each node within an RE tree
    -- this means we can use the structure of the tree to define the language itself

'*' -> Kleene Star - just 0 or more repetitions, like normal
'ε' -> Empty string
-/


--open Kleene
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false
open Lang

variable (Sigma : Type)[Alphabet Sigma]

inductive RE : Type
| sym : Sigma → RE
| append : RE → RE → RE
| plus : RE → RE → RE
| epsilon : RE
| empty : RE
| star : RE → RE

open Lang.Examples
open SigmaABC
open RE
scoped[re] infixl:70 " ⋅ " => RE.append
scoped[re] infixl:65 " + " => RE.plus
scoped[re] postfix:max "*" => RE.star
scoped[re] notation "∅" => RE.empty
scoped[re] notation "ε" => RE.epsilon

open scoped re

instance {Sigma : Type} : CoeTC Sigma (RE Sigma) where
  coe := RE.sym


open scoped re

abbrev e1 : RE SigmaABC
:= a ⋅ b -- * Just means a followed by a b - normally written just without the '⋅'
--:= append (sym a) (sym b)
-- ab

abbrev e2 : RE SigmaABC
:= plus (sym a) (sym b)
-- a+b

abbrev e3 : RE SigmaABC
:= append (sym a) (plus (sym b) (sym c))
-- a(b+c)
-- ac ∈ L, c ∉ L

abbrev e4 : RE SigmaABC
:= plus (append (sym a) (sym b)) (sym c)
-- ab+c
-- ac ∉ L , c ∈ L

abbrev e5 : RE SigmaABC
:= star (append (sym a) (sym b))
-- (ab)*
-- ab , abab , ababab ...

abbrev e6 : RE SigmaABC :=
append (append (plus (sym b) epsilon) e5)
      (plus (sym a) epsilon)
-- ((b+ε)(ab)*)(a+ε)
-- bababa ab a b

abbrev any : RE SigmaABC
:= (a + b + c)*
--:= star (plus (sym a) (plus (sym b) (sym c)))

abbrev e7
:= any ⋅ a ⋅ b ⋅ any -- * Any word that has an 'ab' in the middle of it
--:= append (append any (append (sym a) (sym b))) -- ? shows the dot is left associative
--          any
-- (a+b+c)*ab(a+b+c)*

-- challenge : all words where ab does not appear
abbrev e8 : RE SigmaABC
:= ((b + c) ⋅ (ε + a ⋅ a* ⋅ c))* ⋅ a*


variable {Sigma : Type}[Alphabet Sigma]

-- * Need to define a language for every regular expression
-- this breaks down to needing to do recursion over trees
  -- basically translate every expression by its operation language

  -- ? Operational Language
    -- just translating the RE structure into a set of words

-- just defining what each word does/means -- * same as what i wrote at the top of the page
def L : RE Sigma → Lang Sigma
| empty => {}
| plus e1 e2 => (L e1) ∪ (L e2)
| epsilon => { [] }
| append e1 e2 => L e1 ⋅ L e2
| RE.star e => (L e) *
| sym x => { [x] }

open Nfa
open NFA

abbrev nfa_empty : NFA Sigma
:= { Q := Fin 0
     S := {}
     F := {}
     δ := λ q x => {}
}

def nfa_sym : Sigma → NFA Sigma
| x => {
      Q := Fin 2
      S := {0}
      F := {1}
      δ := λ | 0 , y => if x=y then {1} else {}
             | 1 , _ => {}
}

abbrev nfa_epsilon : NFA Sigma -- accepts only the empty string, anything else and this isnt defined
:= {
  Q := Fin 1
  S := {0}
  F := {0}
  δ := λ | _ , _ => {}
}


-- ? Define the **plus** operation as an NFA

abbrev nfa_plus :
NFA Sigma → NFA Sigma → NFA Sigma
| A1 A2 => -- extracting the 2 nodes from the RE tree using pattern matching
let Q := Sum A1.Q A2.Q -- just the combination of states for the 2 nodes at from this leaf
{
  Q := Q
  S := ({inl q | q ∈ A1.S} : Finset Q) ∪ ({inr q | q ∈ A2.S} : Finset Q) -- start states are the union of the start states for the nodes constructing the part of the tree
  /-
    uses 'inl' and 'inr' because the given RE is defined as the union of 2 other RE structures (ie RE₁ ∨ RE₂) and when we break ∨ we get a left and a right
      and this is why we use the 'inl' and 'inr' operators
  -/
  F := ({inl q | q ∈ A1.F} : Finset Q) ∪ ({inr q | q ∈ A2.F} : Finset Q) -- exact same logic as the start states
  /-
    just using the standard pattern matching in lean, because a given node is defined as the union of a left and a right re structure, we just split on the union (inl,inr)
      and then define the transitions as the transitions from those structures
  -/
  δ := λ | inl q x =>
          {inl p | p ∈ A1.δ q x}
         | inr q, x =>
          {inr p | p ∈ A2.δ q x}
}

-- * Translate NFAs over sigma into RE over sigma
  -- just a compiler for regular expressions
def re2nfa : RE Sigma → NFA Sigma
| empty => nfa_empty
| sym x => nfa_sym x
| plus e1 e2 => nfa_plus (re2nfa e1) (re2nfa e2) -- recursively break down each side of the tree structure
| epsilon => nfa_epsilon
| append e1 e2 => sorry
| RE.star e => sorry


theorem re2nfa_ok : ∀(e : RE Sigma),
  L e = Nfa.L (re2nfa e) := sorry
