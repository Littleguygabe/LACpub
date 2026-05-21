import Proofs.Lang
import Proofs.PDA
import Proofs.Autom

open Lang Examples SigmaABC Sum
open Dfa hiding L
open Pda hiding L

/-
Where are we now?

Chomsky hierarchy:

  Level 3 →
    DFA/NFA

  Level 2 →
    PDA = NFA + Stack

  Level 1/0 →
    Turing Machine = DFA + tape
-/

abbrev anbncn : Lang SigmaABC
:= {a^n ++ b^n ++ c^n | n : ℕ}

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

-- Example TM

inductive Γb : Type where
| X | Y | Z | blank
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

/-

Formalisation of how turing machines accept words

-/

variable {Sigma : Type}[Alphabet Sigma]
variable (M : TM Sigma)
variable (D : DFA Sigma)



---------- DFAs ----------

abbrev ID_DFA (A : DFA Sigma) : Type
:= A.Q × Word Sigma
-- defining the type for the instantaneous description
  -- this is just (State, Word)

abbrev init_dfa (A : DFA Sigma) : Word Sigma → ID_DFA A
| w => (A.s, w)
-- This is defining the start ID
  -- just the starting state 's' and the whole unread word 'w'

abbrev Step_dfa (A : DFA Sigma) : (ID_DFA A × ID_DFA A) → Prop
| read => ∀ q q' x w, q' = A.δ q x → Step_dfa A ((q, x::w),(q',w))
/-
This is acting as a volidator rather than applying the transition
  it's taking:
    q : Current State
    q': Our next State

  and then checking that there is actually a transition
  from q → q'
  and if there isn't then the transition is invalid

  formula explained:
    q    : current state
    q'   : next state
    x::w : our input word

    so if the next state q' is the same as what we get
    when we apply the transition function to our current state
    and the current character we're looking at
    then it implies this is a valid transition

-/

inductive Star' {A : Type}(R : A × A → Prop) : A × A → Prop
| refl : ∀ a, Star' R (a, a)
| step : ∀ a b c, R (a, b) → Star' R (b, c) → Star' R (a,c)
/-

refl →
  This is the base case,
    basically saying it's valid that we can start at a
    and end at a, without having to do any steps

ste →
  This is the recursive case,
    Saying for all a, b & c,
    if we have a transition from a → b
    and a transition from b → c
    then we can say we have a transition from a → c
      - Basically formally defining the rule of transitivity

-/

abbrev accept_dfa (A : DFA Sigma) : ID_DFA A → Prop
| (q, []) => q ∈ A.F
| _ => False
/-
Just saying:
  if the state q is in the final states of A
  and the word is empty
  then we accept the word

  otherwise we don't accept the word
-/

abbrev lang_dfa : Lang Sigma
:= {w | ∃ st, Star' (Step_dfa D) (init_dfa D w, st) ∧ accept_dfa D st}

---------- PDAs ----------
abbrev ID_PDA (P : PDA Sigma) : Type
:= P.Q × Word Sigma × List P.Γ

abbrev init_pda (P : PDA Sigma) : Word Sigma → ID_PDA P
| w => (P.s, w, [P.Z₀])

inductive Step_pda (P : PDA Sigma) : (ID P × ID P ) → Prop
| read : ∀ q q' α x w z γ ,
    (q' , α ) ∈ P.δ q (some x) z →
       Step_pda P ((q , x :: w, z :: γ) , (q' , w , α ++ γ ) )
| silent : ∀ q q' α w z γ ,
    (q' , α ) ∈ P.δ q none z →
       Step_pda P ((q , w , z :: γ) , (q' , w , α ++ γ ))

abbrev accept_pda (P : PDA Sigma) : ID_PDA P → Prop
| (q', [], _) => q' ∈ P.F
| _ => False
/-
if q is a final state and the word is empty then regardless of the stack content
the word is accepted in the PDA's language
-/

abbrev lang_pda (P : PDA Sigma) : Lang Sigma
:= {w | ∃ fst, Star' (Step_pda P) (init_pda P w, fst) ∧ accept_pda P fst}

---------- TMs ----------

abbrev Sym : Type := M.Γ ⊕ Sigma

abbrev ID_TM : Type
:= List (Sym M) × M.Q × List (Sym M)

def word2tape : List Sigma → List (Sym M)
| w => List.map inr w

abbrev init_tm (M : TM Sigma) : Word Sigma → ID_TM M
| w => ([], M.s, word2tape M w)

abbrev accept_tm : ID_TM M → Prop
| (_,q,_) => q ∈ M.F

inductive Step : ID_TM M × ID_TM M → Prop
-- Easy when we're in the middle of the tape
/-
  q   → current state
  x   → first character of the list to the left (currently under the head of our TM)
  q'  → state we're moving to
  y   → first character of the list to the right
  γL  → everything else to the left
  γR  → everything else to the right
-/
| right : ∀ q x q' y γL γR, M.δ q x = some (q',y,R)
        → Step ((γL,q,x::γR) , (y::γL,q',γR))
        /-       ^^^^^^^^^^     ^^^^^^^^^^^
                 Init State      New State
        In this branch when we do the validation
          M.δ q x = some (q', y, R)
        the discriminator is the R value
          we need q' & y for later, but right now we just want to know
          did the state transition make us move to the right or to the left
        -/

| left : ∀ q x q' y z γL γR, M.δ q x = some (q',y,L)
        → Step ((z::γL,q,x::γR) , (γL,q',z::y::γR))
        /-
        Similar to the right case but we need to keep an extra value z to move the tape
        example:
          say we have the tape:

            ... | γL | z | [x] | γR | ...

          then to move to the left
          we take the 2 remaining lists γL & γR
          take the value we want to write to the tape y
          then do z :: y :: γR to move the head to the left:

            ... | γL | [z] | y | γR | ...

          then repeat
        -/

-- Special cases when we're at the right end of the tape
| right_rightEnd : ∀ q q' y γL, M.δ q (inl M.B) = some (q',y,R)
        → Step ((γL,q,[]) , (y::γL,q',[]))

| left_rightEnd : ∀ q q' y z γL, M.δ q (inl M.B) = some (q',y,L)
        → Step ((z::γL,q,[]) , (γL,q',[z,y]))

-- Special cases when we're at the left end of the tape
| left_empty : ∀ q q' y γL, M.δ q (inl M.B) = some (q',y,L)
        → Step (([],q,[]) , (γL,q',[inl M.B,y]))

| leftEnd : ∀ q q' x y γR, M.δ q x = some (q',y,L)
         → Step (([],q,x::γR) , ([],q',(inl M.B)::y::γR))

abbrev lang_tm : Lang Sigma
:= {w | ∃ fst , Star' (Step M) (init_tm M w, fst) ∧ accept_tm M fst}
