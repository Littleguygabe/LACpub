/-
COMP2012 (LAC) 2026

Exercise 5

Construct a CFG and PDA for the language of bracket-matched
words.

Don't change anything else in this file!
-/
import Proofs.CFG
import Mathlib.Tactic.DeriveFintype
import Proofs.PDA

namespace ex5

open Lang Sum Cfg CFG Pda PDA

/-
Let SigmaPar be the alphabet of left and right brackets
-/

inductive SigmaPar : Type
| lpar -- "⟨"
| rpar -- "⟩"
deriving Fintype, DecidableEq
open SigmaPar

/-
We consider the language L : Lang Σ of bracket-matched words, words
words in which every ⟨ is “closed” by a ⟩ occurring later in the word. For instance:
• [] ∈ L -- ϵ ∈ L
• [lpar,rpar] ∈ L -- ⟨⟩ ∈ L
• [lpar,lpar,rpar,lpar,rpar,rpar] ∈ L -- ⟨⟩⟨⟩ ∈ L
• [lpar,lpar,rpar] ∉ L   -- ⟨⟨⟩ ∉ L because it has more ⟨’s than ⟩’s,
• [lpar,rpar,rpar] ∉ L   -- ⟨⟩⟩ ∉ L because it has more ⟩’s than ⟨’s,
• [lpar,rpar,rpar,lpar] ∉ L -- ⟨⟩⟩⟨ ∉ L because the second ⟩ occurs before the corresponding ⟨.
-/

-- Just matching parenthesis leetcode question

/- 1. Define a CFG for the language, you will also need to define an inductive type for the Non-terminals -/
inductive NTPar : Type
| Start
deriving Fintype, DecidableEq
open NTPar

abbrev GPar : CFG SigmaPar
:= { NT := NTPar
     S := Start
     P := {
          (Start, []),
          (Start, [inr lpar, inl Start, inr rpar]),
          (Start, [inl Start, inl Start])
     }
}

/- 2. Define a PDA for the language -/
-- You need to define inductive types for the states and the stack alphabet
inductive QPar : Type
| q0 | q1
deriving Fintype, DecidableEq
open QPar

-- Define the stack alphabet
inductive ΓPar : Type
| Z | X
deriving Fintype, DecidableEq
open ΓPar

abbrev PPar : PDA SigmaPar
:= { Q := QPar
     Γ := ΓPar
     s := q0
     Z₀ := Z
     F := { q1 }
     δ q x z := match q, x, z with
       | q0, some lpar, Z => {(q0, [X, Z])}
       | q0, some lpar, X => {(q0, [X, X])}
       | q0, some rpar, X => {(q0, [])}
       | q0, none, Z => {(q1, [Z])}
       | _, _, _ => {}
}

-- 3. Show that ⟨⟨⟩⟨⟩⟩ ∈ L PPar
-- you can either do this by spelling out the sequence of IDs in a comment or by proving
theorem e3 : [SigmaPar.lpar,SigmaPar.lpar, SigmaPar.rpar,SigmaPar.lpar,SigmaPar.rpar, SigmaPar.rpar] ∈ L PPar := by
     simp
     exists [ΓPar.Z]
     apply Star.step
     apply Step.read
     constructor

     apply Star.step
     apply Step.read
     constructor

     apply Star.step
     apply Step.read
     constructor

     apply Star.step
     apply Step.read
     constructor

     apply Star.step
     apply Step.read
     constructor

     apply Star.step
     apply Step.read
     constructor

     apply Star.step
     apply Step.silent
     constructor

     apply Star.refl


/-
Trace of ⟨⟨⟩⟨⟩⟩ ∈ L PPar for your notes:
(q0, [lpar, lpar, rpar, lpar, rpar, rpar], [Z]) -> read lpar
(q0, [lpar, rpar, lpar, rpar, rpar], [X, Z])    -> read lpar
(q0, [rpar, lpar, rpar, rpar], [X, X, Z])       -> read rpar
(q0, [lpar, rpar, rpar], [X, Z])                -> read lpar
(q0, [rpar, rpar], [X, X, Z])                   -> read rpar
(q0, [rpar], [X, Z])                            -> read rpar
(q0, [], [Z])                                   -> silent (epsilon)
(q1, [], [Z])                                   -> Accept!
-/
end ex5
