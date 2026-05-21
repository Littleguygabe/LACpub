/-
Languages and Computation (COMP2012) 25-26
L05 : NFAs

-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Finset.Powerset
import Proofs.Lang

namespace Dfa
open Lang

variable (Sigma : Type)[Alphabet Sigma]

structure DFA : Type 1 where
  Q : Type -- states of the automata
  [alphQ : Alphabet Q]
  s : Q
  F : Finset Q
  δ : Q → Sigma → Q


variable (A : DFA Sigma)
attribute [instance] DFA.alphQ


def δ_star : A.Q → Word Sigma → A.Q
  | q, [] => q
  | q, (x :: w) => δ_star (A.δ q x) w -- recursive call to move through character by character

end Dfa

namespace DfaEx
open Lang Lang.Examples SigmaABC Dfa

abbrev A₁ : DFA SigmaABC
:= {
  Q := Fin 2
  s := 0
  F := {1}
  δ := λ  | 0, a => 1
          | 0, _ => 0
          | 1, _ => 1
}
-- Simulate at: https://www.automataverse.com/simulator



end DfaEx

-- moving onto NFA

namespace Nfa
open Lang
variable (Sigma : Type)[Alphabet Sigma]

structure NFA : Type 1 where
  Q : Type
  [alphQ : Alphabet Q]
  s : Finset Q
  F : Finset Q
  δ : Q → Sigma → Finset Q


macro "⟪" q:ident " | " P:term "⟫" : term =>
  `( (Finset.univ).filter (fun $q => $P) )
macro "⟪" q:ident " ∈ " xs:term " | " P:term "⟫" : term =>
  `( ($xs).filter (fun $q => $P) )

attribute [instance] NFA.alphQ

variable {Sigma : Type}[Alphabet Sigma]
variable (A : NFA Sigma)



namespace NfaEx
open Nfa Lang Lang.Examples SigmaABC

abbrev A₂ : NFA SigmaABC
:= {
  Q := Fin 2
  s := {0}
  F := {1}
  δ := λ  | 0, a => {0,1}
          | 0, _ => {0}
          | 1, _ => {}
}

def δ_step (A : NFA Sigma) (S : Finset A.Q) (a : Sigma) : Finset A.Q :=
  ⟪ q | ∃ p ∈ S, q ∈ A.δ p a ⟫

def δ_star : Finset A.Q → Word Sigma → Finset A.Q
  | s, [] => s
  | s , (x :: w) => δ_star (δ_step A s x) w

end NfaEx
