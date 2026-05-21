import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Nat.ModEq
import Proofs.Lang
import Proofs.Autom

open Lang Nfa NFA Lang.Examples SigmaABC

/-!
# Practice: NFAs

In this file, you should define the NFAs for the described languages.
NFAs are often easier to define than DFAs for "contains" or "ends with" languages
because you can "guess" when the pattern starts.

Use `decide` or `simp [L, δ_star, δ_step]` to check your answers.
-/

namespace PracticeNFA

/-
Exercise 1: Contains "cab".
Define an NFA over SigmaABC that accepts words containing the substring "cab".
Hint: Use state 0 to loop on everything, and "guess" when to start matching 'c'.
-/

def NFA_contains_cab : NFA SigmaABC
:= {
  Q := Fin 4
  S := {0}
  F := {3}
  δ := λ  | 0, c => {0, 1}
          | 0, _ => {0}
          | 1, a => {2}
          | 2, b => {3}
          | 3, _ => {3}
          | _, _ => {} -- need to remember this for the base case

}

example : ([c, a, b] : Word SigmaABC) ∈ L NFA_contains_cab := by decide
example : ([a, c, a, b, c] : Word SigmaABC) ∈ L NFA_contains_cab := by decide
example : ([a, b, c] : Word SigmaABC) ∉ L NFA_contains_cab := by decide


/-
Exercise 2: Ends with "aba".
Define an NFA over SigmaABC that accepts words ending with "aba".
-/

def NFA_ends_aba : NFA SigmaABC
:= {
  Q := Fin 4
  S := {0}
  F := {3}
  δ := λ  | 0, a => {0, 1}
          | 0, _ => {0}
          | 1, b => {2}
          | 2, a => {3}
          | _, _ => {}
}

example : ([a, b, a] : Word SigmaABC) ∈ L NFA_ends_aba := by decide
example : ([c, a, b, a] : Word SigmaABC) ∈ L NFA_ends_aba := by decide
example : ([a, b, a, b] : Word SigmaABC) ∉ L NFA_ends_aba := by decide


/-
Exercise 3: Second to last symbol is 'a'.
Define an NFA over SigmaABC that accepts words where the second to last symbol is 'a'.
-/

def NFA_second_last_a : NFA SigmaABC
:= {
  Q := Fin 3
  S := {0}
  F := {2}
  δ := λ  | 0, a => {0,1}
          | 0, _ => {0}
          | 1, _ => {2}
          | 2, _ => {}
          | _, _ => {}
}

example : ([a, b] : Word SigmaABC) ∈ L NFA_second_last_a := by decide
example : ([c, a, c] : Word SigmaABC) ∈ L NFA_second_last_a := by decide
example : ([a, a, a] : Word SigmaABC) ∈ L NFA_second_last_a := by decide
example : ([a] : Word SigmaABC) ∉ L NFA_second_last_a := by decide
example : ([b, c] : Word SigmaABC) ∉ L NFA_second_last_a := by decide


/-
Exercise 4: Contains "aa" OR "bb".
Define an NFA over SigmaABC that accepts words containing either "aa" or "bb".
Hint: You can have multiple initial states in an NFA!
-/

def NFA_aa_or_bb : NFA SigmaABC
:= {
  Q := Fin 5
  S := {0, 2}
  F := {4}
  δ := λ  | 0, a => {0,1}
          | 0, _ => {0}
          | 1, a => {4}
          | 2, b => {2, 3}
          | 2, _ => {2}
          | 3, b => {4}
          | 4, _ => {4}
          | _, _ => {}
}

example : ([a, a] : Word SigmaABC) ∈ L NFA_aa_or_bb := by decide
example : ([c, b, b, a] : Word SigmaABC) ∈ L NFA_aa_or_bb := by decide
example : ([a, b, a, b] : Word SigmaABC) ∉ L NFA_aa_or_bb := by decide


/-
Exercise 5: Binary strings containing "101".
Define an NFA over SigmaBin that accepts binary strings containing "101".
-/

def NFA_contains_101 : NFA SigmaBin
:= {
  Q := Fin 4
  S := {0}
  F := {3}
  δ := λ  | 0, 1 => {0, 1}
          | 0, 0 => {0}
          | 1, 0 => {2}
          | 2, 1 => {3}
          | 3, _ => {3}
          | _, _ => {}
}

example : ([1, 0, 1] : Word SigmaBin) ∈ L NFA_contains_101 := by decide
example : ([0, 1, 0, 1, 0] : Word SigmaBin) ∈ L NFA_contains_101 := by decide
example : ([1, 1, 0, 0] : Word SigmaBin) ∉ L NFA_contains_101 := by decide

end PracticeNFA
