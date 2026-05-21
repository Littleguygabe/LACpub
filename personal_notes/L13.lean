import Proofs.Lang
import Mathlib.Tactic.DeriveFintype

namespace pda
open Lang Lang.Examples SigmaABC
variable (Sigma : Type)[Alphabet Sigma]

/-

We are technically looking at Non-Deterministic PDAs


What is a push down automata?
  - Type of context free grammar
  - An NFA that has a stack aswell

This means the state transitions are defined with all
  1. Current State
  2. Input Symbol
  3. Top of Stack   ← This is new

Then the transition function outputs:
  1. New State
  2. Value to replace the top of the stack    ← Again this is new
-/


structure PDA : Type 1 where
  Q : Type -- states
  [alphQ : Alphabet Q]
  Γ : Type -- stack alphabet
  [alphΓ : Alphabet Γ]
  s : Q -- initial state
    -- although we only have 1 initial state
      -- we can technically have mutliple using epsilon transition functions

  z₀ : Γ -- initial stack state
  F : Finset Q -- set of final states
  δ : Q → Option Sigma → Γ → Finset (Q × List Γ)
    -- takes:
      -- 1. current state
      -- 2. optional input symbol
      -- 3. top of stack (Γ)

    -- returns:
      -- A set of states and strings to push to the stack

open PDA
variable {Sigma : Type}[Alphabet Sigma]
variable (P : PDA Sigma)

---------------------------------
---------- PDA EXAMPLE ----------

inductive Γ₀ : Type
| hash | one -- a
deriving Fintype, DecidableEq
open Γ₀

abbrev P₁ : PDA SigmaABC
:= {
  Q := Fin 3
  Γ := Γ₀
  s := 0
  z₀ := hash
  F := {2}
  δ q x γ :=
    match q, x, γ with
      -- define as:
        -- current_state, input_symbol, top_of_stack => {(new_state,[vals_to_push_to_stack])}
    | 0, some a, z => {(0, [one,z])}
    | 0, some b, one => {(1, [])}
    | 0, none, Γ₀.hash => {(2, [])}
    | 1, some b, one => {(1, [])}
    | 1, none, Γ₀.hash => {(2, [])}
    | _,_,_ => {} -- kills out computation like in an NFA
}


/-
At any specific point when reading a word in a PDA,
we need to know:
  1. The state the PDA is in
  2. The rest of the word we're reading
  3. The stack contents

  To be able to un-ambiguously define how the PDA behaves

These recoards are called **Instantanious Descriptions**
  Essentially a stack trace for the PDA

ie if we had the transition function
  δ (q₀,a,Z₀) = (q₁,AZ₀)

and word:
  ab

then we would get:
  (q₀,ab,Z₀) ⊢ (q₁,b,AZ₀)

  we get q₀ and AZ₀ from δ
  then ab → b because we consume the word left to right
    so essentially a is on top of the stack

  the '⊢' just represents the transition from one ID to another
-/

abbrev ID : Type := P.Q × Word Sigma × List P.Γ

-- tells us if we can move from one ID to another in a single step in our PDA
inductive Step : (ID P × ID P) → Prop
| read : ∀ q q' α x w z y,
  /-
    q q' :: all states in our PDA
    α :: stack chars
    (x:w) :: the word we're operating on
    (z:y) :: the stack we're using
  -/
  (q', α) ∈ P.δ q (some x) z
  → Step ((q, x::w, z::y), (q', w, α ++ y))
| silent : ∀ q q' α w z y, -- case with epsilon
  (q', α) ∈ P.δ q none z
  → Step ((q, w, z::y),(q', w, α ++ y))

-- Generalisation of previous δ_Star function over PDAs
  -- officially transitive reflective closure?
inductive Star {A:Type}(R: A × A → Prop) : A × A → Prop
| refl : ∀ a, Star R (a, a)
| step : ∀ a b c, R (a, b) → Star R (b, c) → Star R (a, c)


-- the definition of the language of a PDA
abbrev L : Lang Sigma
:= { w | ∃ q' γ ,
    Star (Step P) ((P.s,w,[P.z₀]),(q',[],γ)) ∧ q' ∈ P.F }

-- saying if we read a word until its empty
-- then if the stack is also empty
-- then the word is accepted
abbrev L_empty : Lang Sigma
 := { w | ∃ q' ,
      Star (Step P) ((P.s,w,[P.z₀]),(q',[],[])) }

end pda
