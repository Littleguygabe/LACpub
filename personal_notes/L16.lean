import Proofs.Lang
import Proofs.PDA

open Lang
open Pda
open Examples
open SigmaABC
open Sum


/-
Turing Machines

  Looking at level 0 & 1 in the chomsky hierarchy
-/

/-

We can see context free grammars are closed under intersection

for instance:
-/

abbrev anbncn : Lang SigmaABC
:= {a^n ++ b^n ++ c^n | n : ℕ}

/-
is not a CFG as we cannot construct a PDA to represent it
  →   we can use a stack to count the number of a's and bs'
      but then how do we know how many c's we want to count?
-/

-- so if we define:
abbrev anbncm : Lang SigmaABC
:= {a^n ++ b^n ++ c^m | (n : ℕ) (m : ℕ)}

-- and

abbrev anbmcn : Lang SigmaABC
:= {a^n ++ b^m ++ c^n | (n : ℕ) (m : ℕ)}

/-

then when we do:

  anbncm ∩ anbmcn

then we end up with the same language as:

  anbncn
-/

/-
But how can we actually recognise a grammar like anbncn?

As its a chomsky level 1 language then it is recognised by a turing machine
-/

/-
**What is a Turing Machine**

Formal Definition :
-/

variable (Sigma : Type)[Alphabet Sigma]

inductive Dir : Type where
| L | R
deriving Fintype, DecidableEq
open Dir

structure TM : Type 1 where
  Q : Type -- states
  [alphQ : Alphabet Q]
  Γ : Type -- tape alphabet
  [alphΓ : Alphabet Γ]
  s : Q -- start state
  B : Γ -- blank symbol
  F : Finset Q
  δ : Q → Γ ⊕ Sigma → Option (Q × (Γ ⊕ Sigma) × Dir)


-- defining an example turing machine

inductive Γb : Type where
| blank | X | Y | Z
deriving Fintype, DecidableEq

open Γb

abbrev Manbncn : TM SigmaABC :=
{
   Q := Fin 7
   Γ := Γb
   s := 0
   B := blank
   F := { 6 }
   δ q z := match q , z with
            | 0 , inr a => some (1, inl X, R)
            | 1 , inr a => some (1, inr a, R)
            | 1 , inl Y => some (1,inl Y, R )
            | 1 , inr b => some (2,inl Y, R )
            | 2 , inr b => some (2,inr b, R )
            | 2 , inl Z => some (2,inl Z, R )
            | 2 , inr c => some (3,inl Z, R )
            | 3 , inr c => some (4,inr c, Dir.L)
            | 4 , inr a => some (4,inr a, Dir.L)
            | 4 , inr b => some (4,inr b, Dir.L)
            | 4 , inl Y => some (4,inl Y, Dir.L)
            | 4 , inl Z => some (4,inl Z, Dir.L)
            | 4 , inl X => some (0,inl X, Dir.R)
            | 3 , inl blank => some (5,inl blank, Dir.L)
            | 5 , inl Y => some (5,inl Y, Dir.L)
            | 5 , inl Z => some (5,inl Z, Dir.L)
            | 5 , inl X => some (6,inl X, R)
            | _ , _  => none
      }

variable {Sigma : Type}[Alphabet Sigma]

variable (M : TM Sigma)

abbrev Sym : Type := M.Γ ⊕ Sigma
/-

saying that the turing machine can hold both:

  Γ → internal tape symbols
  Sigma → input symbols

-/

abbrev ID : Type -- instantanious description
:= List (Sym M) × M.Q × List (Sym M)
/-
Instantaneous Description

Represents the given position/state of the machine at any given moment
  like an execution trace

-/

-- the step of a touring machine is the relation between IDs - same as PDAs/CFGs

inductive Step : ID M × ID M → Prop where
-- To be completed

def word2tape : List Sigma → List (Sym M)
| w => List.map inr w
/-
just converts a word to a tape
as input is [Sigma] and the tape is [Sym]
  so we just map each Sigma to Sym as Sym ∈ Sigma
-/

abbrev init : Word Sigma → ID M
| w => ([] , M.s, word2tape M w )
/-
Describing the initial state of the system
-/

abbrev accept : ID M → Prop
| (_,q,_) => q ∈ M.F

abbrev L : Lang Sigma
:= { w | ∃ st , Pda.Star (Step M) (init M w,st) ∧ accept M st}
/-

just saying a word is in the language if there exists 0 or more steps
that transitions the machine from the init ID to any state snapshot
where the state is accepted

-/
