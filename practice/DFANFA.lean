import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Nat.ModEq
import Proofs.Lang
import Proofs.Autom

open Lang Dfa DFA Lang.Examples SigmaABC

/-!
# Practice: DFAs

In this file, you should define the DFAs for the described languages.
Follow the style of `Lectures/L04.lean`.
Use `decide` or `aesop` to check your answers against the examples.
-/

namespace PracticeDFA

/-
Exercise 1: Even number of 'a's.
Define a DFA over SigmaABC that accepts words with an even number of 'a's.
(Zero is an even number).
-/

abbrev A_even_a : DFA SigmaABC
:= {
  Q := Fin 2 -- The machine has 2 states (0 = even, 1 = odd)
  s := 0
  F := { 0 }
  δ := λ  | 0, a => 1 -- move from even to odd
          | 1, a => 0 -- move from odd to even
          | q, _ => q -- b or c doesnt change anything
}

example : ([] : Word SigmaABC) ∈ L A_even_a := by decide
example : ([a, b, a] : Word SigmaABC) ∈ L A_even_a := by decide
example : ([a, b, c] : Word SigmaABC) ∉ L A_even_a := by decide
example : ([a, a, a] : Word SigmaABC) ∉ L A_even_a := by decide


/-
Exercise 2: Ends with "ab".
Define a DFA over SigmaABC that accepts words ending with the substring "ab".
-/

abbrev A_ends_ab : DFA SigmaABC
:= {
  Q := Fin 3
  s := 0
  F := { 2 }
  δ := λ  | 0, a => 1
          | 0, _ => 0
          | 1, a => 1
          | 1, b => 2
          | 1, c => 0
          | 2, a => 1
          | 2, _ => 0
}

example : ([a, b] : Word SigmaABC) ∈ L A_ends_ab := by decide
example : ([c, a, b] : Word SigmaABC) ∈ L A_ends_ab := by decide
example : ([a, a, b] : Word SigmaABC) ∈ L A_ends_ab := by decide
example : ([a, b, c] : Word SigmaABC) ∉ L A_ends_ab := by decide
example : ([a] : Word SigmaABC) ∉ L A_ends_ab := by decide


/-
Exercise 3: Binary Even.
Define a DFA over SigmaBin (0 and 1) that accepts binary strings representing even numbers.
Assume the empty string is not even (or is 0, depending on your preference,
but here let's say it must end in '0').
-/
-- basically doesnt end in 1
abbrev A_bin_even : DFA SigmaBin
:= {
  Q := Fin 2
  s := 0
  F := {1}
  δ := λ  | 0, 0 => 1
          | 0, 1 => 0
          | 1, 0 => 1
          | 1, 1 => 0
}

example : ([1, 0] : Word SigmaBin) ∈ L A_bin_even := by decide    -- 2
example : ([1, 1, 0] : Word SigmaBin) ∈ L A_bin_even := by decide -- 6
example : ([1] : Word SigmaBin) ∉ L A_bin_even := by decide          -- 1
example : ([1, 0, 1] : Word SigmaBin) ∉ L A_bin_even := by decide -- 5


/-
Exercise 4: Contains "abc".
Define a DFA over SigmaABC that accepts any word containing the substring "abc".
-/

abbrev A_contains_abc : DFA SigmaABC
:= {
  Q := Fin 4
  s := 0
  F := {3}
  δ := λ  | 0, a => 1
          | 0, _ => 0
          | 1, a => 1
          | 1, b => 2
          | 1, c => 0
          | 2, a => 1
          | 2, b => 0
          | 2, c => 3
          | 3, _ => 3
}

example : ([a, b, c] : Word SigmaABC) ∈ L A_contains_abc := by decide
example : ([a, a, b, c, b] : Word SigmaABC) ∈ L A_contains_abc := by decide
example : ([a, b, b, c] : Word SigmaABC) ∉ L A_contains_abc := by decide


/-
Exercise 5: Every 'a' followed by 'b'.
Define a DFA over SigmaABC that accepts words where every occurrence of 'a'
is immediately followed by at least one 'b'.
-/

abbrev A_a_then_b : DFA SigmaABC
:= {
  Q := Fin 3
  s := 0
  F := { 0 }
  δ := λ  | 0, a => 1
          | 0, _ => 0
          | 1, b => 0
          | 1, _ => 2
          | 2, _ => 2

}

example : ([] : Word SigmaABC) ∈ L A_a_then_b := by decide
example : ([a, b, c, a, b] : Word SigmaABC) ∈ L A_a_then_b := by decide
example : ([b, c, b] : Word SigmaABC) ∈ L A_a_then_b := by decide
example : ([a, a, b] : Word SigmaABC) ∉ L A_a_then_b := by decide
example : ([a, c] : Word SigmaABC) ∉ L A_a_then_b := by decide
example : ([a] : Word SigmaABC) ∉ L A_a_then_b := by decide


/-
Exercise 6: Length exactly 3.
Define a DFA over SigmaABC that accepts words of length exactly 3.
-/

abbrev A_len_3 : DFA SigmaABC
:= {
  Q := Fin 5
  s := 0
  F := {3}
  δ := λ  | 0, _ => 1
          | 1, _ => 2
          | 2, _ => 3
          | 3, _ => 4
          | 4, _ => 4
}

example : ([a, b, c] : Word SigmaABC) ∈ L A_len_3 := by decide
example : ([b, b, b] : Word SigmaABC) ∈ L A_len_3 := by decide
example : ([a, b] : Word SigmaABC) ∉ L A_len_3 := by decide
example : ([a, b, c, a] : Word SigmaABC) ∉ L A_len_3 := by decide

end PracticeDFA
