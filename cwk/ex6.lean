/-
COMP2012 (LAC) 2026

Exercise 6

Don't change anything else in this file!
-/
import Proofs.TM
import Mathlib.Tactic.DeriveFintype
import Proofs.CFG

namespace ex6_1
open Sum Cfg CFG

/-
We are defining a grammar for regular expressions over

inductive Sigma : Type
| a | b | c

These are the expressions we have been using in ex4. E.g.
(a + b)* ⬝ c*
and so on.
-/

/- Here is the alphabet
epsilon = ε
empty = ∅
dot = ⬝
plus = +
star = *
lpar = (
rpar = )
-/
inductive Sigma_RE : Type
| a | b | c | epsilon | empty | dot | plus | star | lpar | rpar
deriving Fintype, DecidableEq
open Sigma_RE

-- We introduce the following grammar, st L(G₁) : Lang Sigma_RE
-- is the language of regular expressions.
namespace g₁

inductive NT₁ : Type
| E
deriving Fintype, DecidableEq
open NT₁

abbrev G₁ : CFG Sigma_RE :=
{ NT := NT₁
  S := E
  P := { (E, [inr a]),
         (E, [inr b]),
         (E, [inr c]),
         (E, [inr epsilon]),
         (E, [inr empty]),
         (E, [inl E, inr dot,inl E]),
         (E, [inl E, inr plus,inl E]),
         (E, [inl E, inr star]),
         (E, [inr lpar, inl E,inr rpar]) }
}

end g₁

namespace g₂
/-
Alas, G₁ is ambigious (why ?).
  G₁ is ambiguous because it has no precedence or associativity rules.
  For example, a + b ⬝ c could be parsed as (a + b) ⬝ c or a + (b ⬝ c)
  since there's nothing in the grammar to say which operator binds tighter.
  Similarly a ⬝ b ⬝ c could be (a ⬝ b) ⬝ c or a ⬝ (b ⬝ c) since there's no associativity.


Define a grammar G₂ which is not ambigious and whose parsetrees
reflect the conventions on how to read regular expressions.
-/

inductive NT₂ : Type
| E | T | F | A
deriving Fintype, DecidableEq
open NT₂

abbrev G₂ : CFG Sigma_RE :=
{ NT := NT₂
  S := E
  P := {
         (E, [inl E, inr plus, inl T]),
         (E, [inl T]),
         (T, [inl T, inr dot, inl F]),
         (T, [inl F]),
         (F, [inl F, inr star]),
         (F, [inl A]),
         (A, [inr a]),
         (A, [inr b]),
         (A, [inr c]),
         (A, [inr epsilon]),
         (A, [inr empty]),
         (A, [inr lpar, inl E, inr rpar])
       }
}
end g₂
namespace g₃

/- Is the grammar you have defined in the previous step LL(1)?
If not define another grammar G₃ for the same language,
which is LL(1). If G₂ is already LL(1) the just copy this.

LL(1) cannot have left recursion
  ie E → E + F
        ^^^
      E is on the left so the grammar is not LL(1)

-/

inductive NT₃ : Type
-- Define your nonterminals here
| E | E' | T | T' | F | F' | A
deriving Fintype, DecidableEq
open NT₃

/-

A → Aα | β (where β is the case we don't loop recursively)

  - re-write using a non-terminal to make LL(1)

A → βA'
A' → αA' | ε

-/

abbrev G₃ : CFG Sigma_RE :=
{ NT := NT₃
  S := E
  P := {
        (E, [inl T, inl E']),
        (E', [inr plus, inl T, inl E']),
        (E', [inr epsilon]),
        (T, [inl F, inl T']),
        (T', [inr dot, inl F, inl T']),
        (T', [inr epsilon]),
        (F, [inl A, inl F']),
        (F', [inr star, inl F']),
        (F', [inr epsilon]),
        (A, [inr a]),
        (A, [inr b]),
        (A, [inr c]),
        (A, [inr epsilon]),
        (A, [inr empty]),
        (A, [inr lpar, inl E, inr rpar])
      }
}

end g₃

end ex6_1

namespace ex6_2
open Sum Lang Tm TM

inductive SigmaABX : Type
| a | b | X
deriving Fintype, DecidableEq, Repr
open SigmaABX
/-
Define a Turing Machine M deciding the language
-/
abbrev Lww : Lang SigmaABX
:= { wXw | ∃ w , X ∉ w ∧ wXw = w ++ [ X ] ++ w }
/-
ie the language of repeated words over a , b separated by X in the middle.
e.g.
[ a , b, X , a , b] ∈ Lww
-/

inductive Qww : Type
-- Define your TM states here
| next | seekA | seekB | matchA | matchB | ret | retL | accept | reject | cleanup

deriving Fintype, DecidableEq, Repr
open Qww

inductive Γww : Type
-- Define your stack alphabet here
| a | b | X | B

deriving Fintype, DecidableEq, Repr
open Γww

/-

-/

abbrev Mww : TM SigmaABX
:= {
  Q := Qww
  Γ := Γww
  s := next
  B := B
  F := {accept}
  -- (state, symbol) => (next_state, write_symbol, direction)
  δ := λ  | next, inr .a => some (seekA, inl .B, .R)
          | next, inr .b => some (seekB, inl .B, .R)
          | next, inr .X => some (cleanup, inr .X, .R)

          | seekA, inr .a => some (seekA, inr .a, .R)
          | seekA, inr .b => some (seekA, inr .b, .R)
          | seekA, inr .X => some (matchA, inr .X, .R)

          | seekB, inr .a => some (seekB, inr .a, .R)
          | seekB, inr .b => some (seekB, inr .b, .R)
          | seekB, inr .X => some (matchB, inr .X, .R)

          | matchA, inl .B => some (matchA, inl .B, .R)
          | matchA, inr .a => some (ret, inl .B, .L)
          | matchA, inr .b => some (reject, inr .b, .R)

          | matchB, inl .B => some (matchB, inl .B, .R)
          | matchB, inr .b => some (ret, inl .B, .L)
          | matchB, inr .a => some (reject, inr .a, .R)

          | ret, inl .B  => some (ret, inl .B, .L)
          | ret, inr .a  => some (ret, inr .a, .L)
          | ret, inr .b  => some (ret, inr .b, .L)
          | ret, inr .X  => some (retL, inr .X, .L)

          | retL, inr .a  => some (retL, inr .a, .L)
          | retL, inr .b  => some (retL, inr .b, .L)
          | retL, inl .B  => some (next, inl .B, .R)

          | cleanup, inr .a => some (reject, inr .a, .R)
          | cleanup, inr .b => some (reject, inr .b, .R)
          | cleanup, inr .X => some (reject, inr .X, .R)
          | cleanup, inl .B => some (accept, inl .B, .R)

          | _, _ => none
}



#eval (L_n  Mww 1000 [X])
#eval (L_n  Mww 1000 [a,X,a])
#eval (L_n  Mww 1000 [b,X,b])
#eval (L_n  Mww 1000 [a,a,X,a,a])
#eval (L_n  Mww 1000 [a,b,X,a,b])

#eval (stepn_f Mww 9 (init Mww [a,b,X,a,b]))


end ex6_2
