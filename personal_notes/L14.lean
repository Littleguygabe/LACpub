import Proofs.Lang
import Proofs.CFG
import Mathlib.Tactic.DeriveFintype


namespace pda
open Lang Lang.Examples SigmaABC Sum
variable (Sigma : Type)[Alphabet Sigma]

/-

can use the IDs to determine if something is accepted:

  A word w is accepted iff there exists a valid
  sequence of ID such that the final ID
  is in a final state of the PDA

-/

/-
we've been looking at Non-Deterministic PDAs
however we can produce a proposition to see if a given
PDA is deterministic:
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


abbrev isDet : Prop
:= ∀ q x z,
  Fintype.card (P.δ q (some x) z) + Fintype.card (P.δ q none z) ≤ 1

-- bascially saying every combination only has a single transition function


---------- translating from CFG to PDA ----------

/-

Universal Algo to Translate

So how does it translate?

For Non-Terminals:

  1. So the PDA doesn't actually read any input
    Uses epsilon functions

  2. It then look at the value on top of the stack S

  3. It then uses the CFG replacement strings to
    find all possible new values from S

  4. It then pushes all the new values
      from the CFG's replacement functions
      onto individual stacks
      so each one is traced individually

      ie it encodes the CFG replacement functions
          onto its own stack

For Terminals:

  Just consume the terminal character from
  both the stack and the tape
  then carry on

  ie (q ,aba, aSa) ⊢ (q, ba Sa)
    just consumes the a and moves on
-/





end pda
