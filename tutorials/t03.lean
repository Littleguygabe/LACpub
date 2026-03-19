import Proofs.Lang
import Proofs.Autom

open Lang Dfa DFA Nfa NFA Lang.Examples SigmaABC
variable {Sigma : Type}[Alphabet Sigma]
variable (A : DFA Sigma)

/-
Recap: Languages

A language is a set of words.
A word is a sequence of symbols from an alphabet.
An alphabet is a finite type with decidable equality.

Given languages L₁,L₂ we have the following operations:
L₁ ∪ L₂ : { w | w ∈ L₁ ∨ w ∈ L₂ }
L₁ ∩ L₂ : { w | w ∈ L₁ ∧ w ∈ L₂ }
L₁ ⋅ L₂ : { v ++ w | v ∈ L₁ ∧ w ∈ L₂ }
L₁* : { w₁ ++ w₂ ++ ... ++ wₙ | n ∈ ℕ, w₁,w₂,...,wₙ ∈ L₁ }

This week: automata.
Deterministic automaton over alphabet Sigma consists of:
 - States Q
 - Initial state s
 - Final states F
 - Transition function δ : Q → Sigma → Q
We extend δ to δ_star:
-/
def δ_star : A.Q → Word Sigma → A.Q
| q , [] => q
| q , (x :: w) => δ_star (A.δ q x) w
/-
The language of an automaton A is then
{ w | δ_star A A.s w ∈ A.F }
-/

namespace Exercise
/-
abbrev DFA_no010or01 : DFA SigmaBin :=
 {   Q := Fin 3
      s := -- define macro states ie 'zero_one' which represents {0,1}
      the build the DFA using those macro states

 }
-/
