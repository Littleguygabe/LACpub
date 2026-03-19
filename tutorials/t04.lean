import Proofs.Lang
import Proofs.Autom
import Proofs.Kleene

-- Regular expressions
-- grep

open Kleene
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

abbrev e1 : RE SigmaABC
:= append (sym a) (sym b)
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
:= star (plus (sym a) (plus (sym b) (sym c)))

abbrev e7
:= append (append any (append (sym a) (sym b)))
          any
-- (a+b+c)*ab(a+b+c)*
