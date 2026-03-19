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

/-
Example: simple request-response system, after every request
there will be a response before the next request arrives.
-/
inductive SigmaRss : Type
| req | res | wait
open SigmaRss

abbrev A₁ : DFA SigmaRss
:= {
  Q := Fin 3
  s := 0
  F := { 0 }
  δ := λ | 0, req => 1
         | 0, wait => 0
         | 0, res => 2
         | 1, req => 2
         | 1, wait => 1
         | 1, res => 0
         | 2, _ => 2
}
/-
Define the following DFAs:
L₁ : hailing a cab. All words over SigmaABC containing "cab"
L₂ : powers of 4, words over SigmaBin that are a power of 4
L₁ ⋅ L₂ : the concatenation of L₁ and L₂
-/

/-
An NFA is similar to a DFA, except that at any state,
multiple arrows are allowed over the same character

An NFA consists of:
  - Q → a set of States
  - S → a **Set** of initial states
  - F → a set of final states
  - δ → Transition Function
    δ : Q → Sigma → Pow Q
      Delta can take a single state and character and return multiple possible states
-/
