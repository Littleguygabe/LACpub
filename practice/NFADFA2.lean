import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Nat.ModEq
import Proofs.Lang
import Proofs.Autom

open Lang Nfa NFA Dfa DFA Lang.Examples SigmaABC

/-!
# Practice: NFAs

In this file, you should define the NFAs for the described languages.
NFAs are often easier to define than DFAs for "contains" or "ends with" languages
because you can "guess" when the pattern starts.

Use `decide` or `simp [L, δ_star, δ_step]` to check your answers.
-/

namespace PracticeDFA

def DFA_ends_101: DFA SigmaBin
:= {
  Q := Fin 4
  s := 0
  F := {3}
  δ := λ  | 0, 0 => 0
          | 0, 1 => 1
          | 1, 0 => 2
          | 1, 1 => 1
          | 2, 0 => 0
          | 2, 1 => 3
          | 3, 0 => 2
          | 3, 1 => 1
}

def DFA_e0_o1: DFA SigmaBin
:= {
  Q := Fin 4
  s := 0
  F := {2}
  δ := λ  | 0, 0 => 1
          | 0, 1 => 2
          | 1, 0 => 0
          | 1, 1 => 3
          | 2, 0 => 3
          | 2, 1 => 0
          | 3, 0 => 2
          | 3, 1 => 1
}

end PracticeDFA

namespace PracticeNFA

def NFA_tte_1 : NFA SigmaBin
:= {
  Q := Fin 4
  S := {0}
  F := {3}
  δ := λ  | 0, 0 => {0}
          | 0, 1 => {0, 1}
          | 1, _ => {2}
          | 2, _ => {3}
          | _, _ => {}
}

end PracticeNFA
