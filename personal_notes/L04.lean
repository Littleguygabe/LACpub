import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Nat.ModEq
import Proofs.Lang

namespace Dfa
open Lang

variable (Sigma : Type)[Alphabet Sigma]

-- when we write sigma we're talking about an alphabet

-- just the type definition for a DFA
structure DFA : Type 1 where
  -- first thing in the DFA is states
  Q : Type
  [alphQ : Alphabet Q] -- saying Q is an alphabet
  s : Q -- start state
  F : Finset Q -- set of finish states
  δ : Q → Sigma → Q -- transition functions

end Dfa

namespace DFAex

open Lang
open Lang.Examples
open Dfa
open SigmaABC

abbrev A₁ : DFA SigmaABC
:= {
  Q := Fin 2
  s := 0
  F := { 1 }
  δ := λ | 0 , a => 1
         | 0 , _ => 0
         | 1 , _ => 1
}

variable {Sigma : Type}[Alphabet Sigma]
variable (A : DFA Sigma)


-- how we recursively prove that a word is in the language
-- the transition function to go from a given state and a given input to a new state
def δ_star : A.Q → Word Sigma → A.Q
| q, [] => q -- base case
| q, (x :: w) => δ_star (A.δ q x) w

-- now we define the language
abbrev L : Lang Sigma
:= {w | δ_star A A.s w ∈ A.F}

example : [a,b,a] ∈ L A₁ := by aesop
example : [b,b] ∉ L A₁ := by sorry

end DFAex
