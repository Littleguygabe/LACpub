import Proofs.Lang
import Proofs.Autom
import Proofs.Kleene

open Kleene
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

open Lang

variable (Sigma : Type)[Alphabet Sigma]

open Lang.Examples
open SigmaABC

---------------------------------
--------- RE Definitions --------

-- regular expressions are actually tree structures

-- exact same as how we define a new type in haskell
inductive RE : Type
| sym : Sigma → RE -- function from a letter in the alphabet to a word ie e₁ example
| append : RE → RE → RE -- function that joins 2 REs into 1 (and) ie e₂ example
| plus : RE → RE → RE -- function that joins 2 REs into 1 (or) ie e₃ example
| epsilon : RE -- empty word
| empty : RE -- empty set
| star : RE → RE

open RE


-- defining the semantics of regular expressions
  -- ie how we define the language from a reg ex
def L : RE Sigma → Lang Sigma
| sym x => { [x] }
| append re₁ re₂ => (L re₁) ⋅ (L re₂)
| plus re₁ re₂ => (L re₁) ∪ (L re₂)
| epsilon => { [] }
| empty => {}
| RE.star e => (L e) *

---------------------------------
---------- RE Examples ----------

abbrev e₁ : RE SigmaABC -- example of how sym is a function from something witin the language ('a') to a word
:= sym a
-- any word containing a
  -- a

abbrev e₂ : RE SigmaABC
:= append (sym a) (sym b)
-- anyword containing ab
  -- ab

abbrev e₃ : RE SigmaABC
:= plus (sym a) (sym b)
-- any word containing a or b
  -- a + b

-- then can just combine operators like haskell:
  -- a(b+c)
abbrev e₄ : RE SigmaABC
:= append (sym a) (plus (sym b) (sym c))
-- an 'a' followed by a 'b' or a 'c'

abbrev a₅ : RE SigmaABC
:= append (star (append (plus (sym b) epsilon) (append (sym a) (sym b)))) (plus (sym a) epsilon)
-- ((b+ε)(ab)*)(a+ε)
-- accepts any sequence so long as 'a' and 'b' are alternating



abbrev any : RE SigmaABC
:= star (plus (sym a) (plus (sym b) (sym c)))

-- how to say ab needs to appear somewhere within the word
abbrev e₆ : RE SigmaABC
:= append (append any (append (sym a) (sym b))) (any)
-- (a+b+c)ab*(a+b+c)

---------------------------------
---------- RE Challenge ----------

-- any word where ab DOES NOT appear
-- to convert RE to negate itself
  -- Convert RE → NFA
  -- Convert NFA → DFA
  -- Swap sets of accepting and non-accepting states
  -- Convert back to NFA (using Kleene's algo)

abbrev e₇ : RE SigmaABC :=
  append (star (append (plus (sym b) (sym c))
    (append (plus epsilon (sym a)) (append (star (sym a)) (sym c))))) (star (sym a))

---------------------------------
------------ RE → NFA -----------

-- this is essentially just a compiler
  -- takes an expression and converts it to automata
  -- then we use nfa to dfa to ultimately convert from re to dfa

open Nfa
open NFA
open Sum

-- have to define how each case is converted

-- how the empty case is converted to an NFA

variable {Sigma : Type}[Alphabet Sigma]

def nfaEmpty : NFA Sigma -- how we define the 'empty' RE to NFA
:= {
  Q := Fin 0
  S := {}
  F := {}
  δ := λ _ _ => {}
}

def nfaSym : Sigma → NFA Sigma
| x => {
  Q := Fin 2
  S := {0}
  F := {1}
  δ := λ  | 0, y => if x=y then {1} else {}
          | 1, _ => {}
}

def nfaEp : NFA Sigma -- defining the NFA for epsilon (empty word)
:= {
  Q := Fin 1
  S := {0}
  F := {0}
  δ := λ  | _, _ => {}
} -- have a single state that is also a terminal state
  -- as soon as we have anything passed in we move out of that state so no longer accept

def nfaPlus : NFA Sigma → NFA Sigma → NFA Sigma
| A₁, A₂ =>
  let Q := Sum A₁.Q A₂.Q -- sum maintains memory of which initial set the value came from when ∪ doesnt
    -- so {1, 2} ∪ {2, 3} → {1, 2, 3}
    -- but Sum {1, 2} {2, 3} → {inl 1, inl 2, inr 2, inr 3}
      -- used to operate on types rather than just on values/elements
  {
    Q := Q
    S := ({inl q | q ∈ A₁.S} : Finset Q)
        ∪ ({inr q | q ∈ A₂.S} : Finset Q)
    F := ({inl q | q ∈ A₁.F} : Finset Q)
        ∪ ({inr q | q ∈ A₂.F} : Finset Q)
    δ := λ q x ↦ match q with
          | inl s₁ => ({inl p | p ∈ A₁.δ s₁ x} : Finset Q)
          | inr s₂ => ({inr p | p ∈ A₂.δ s₂ x} : Finset Q)
  }

abbrev nullable : Set (NFA Sigma) :=
  { A | ∃ q , q ∈ A.S ∩ A.F }

def nfaAppend (A₁ A₂ : NFA Sigma) : NFA Sigma -- matches the pattern of A₂ immediately followed by A₂
:= let Q := Sum A₁.Q A₂.Q;
  -- this ensures that even if the NFAs use same internal state numbers they dont over write one another
  {
    Q := Q
    S := ({ x | (∃ q ∈ A₁.S, x = inl q) ∨
            (∃ q ∈ A₂.S, x = inr q ∧ A₁ ∈ nullable)})

    -- Saying the start states are:
      -- All the start states in A₁
      -- Then if A₁ accepts the empty word {}
        -- then it would instantly transition to A₂'s initial states
        -- hence A₂'s states become start states if A₁ accepts {}

    F := { inr q | q ∈ A₂.F} -- just the normal final states of A₂


    -- transitions are the transitions in A₁ and A₂
    -- then also all final states in A₁ that are init states in A₂
    δ := λ q x ↦ match q with
      | inl q => ({inl q' | q' ∈ A₁.δ q x} : Finset Q) -- just following A₁'s normal transitions
        ∪ ({y | ∃ q ∈ A₁.δ q x, q ∈ A₁.F ∧ ∃ q' ∈ A₂.S, y = inr q'}:Finset Q)
        -- this is saying then, if we land in one of the final states of A₁ (A₁.F)
        -- then at the same time add the initial start states of A₂ to the output from the transition
          -- this allows the Automata to shift from A₁ to A₂ whilst keeping going in A₁ at the same time

      | inr q => {inr s | s ∈ A₂.δ q x}
        -- otherwise if we're in A₂ just use normal A₂ transitions
  }

def nfaStar (A : NFA Sigma) : NFA Sigma
:= let Q := Sum A.Q (Fin 1) ;
   { Q := Q
     S := ({ inr 0 } : Finset Q)  ∪
          ({ inl q | q ∈ A.S } : Finset Q)
     F := { inr 0 } ∪ ({ inl q | q ∈ A.F } : Finset Q)
     δ := λ q x ↦ match q with
          | inl q => ({ inl q' | q' ∈ A.δ q x} : Finset Q)
           ∪ ({ y | ∃ q', y = inl q' ∧ q' ∈ A.S
                   ∧ ∃ q'' , q'' ∈ A.δ q x ∧ q'' ∈ A.F } : Finset Q)
           | inr _ => {}}


-- similarly to NFA to DFA, this is basically a compiler from RE to NFA

def re2nfa : RE Sigma → NFA Sigma
| sym x => nfaSym x
| append re₁ re₂ => nfaAppend (re2nfa re₁) (re2nfa re₂)
| plus re₁ re₂ => nfaPlus (re2nfa re₁) (re2nfa re₂)
| epsilon => nfaEp
| empty => nfaEmpty
| RE.star e => nfaStar (re2nfa e)

---------------------------------
--------- Pumping Lemma ---------

/-
So far we've seen regular languages
A language is regular if:
  - can be represented by a regular expression
  - or by an NFA
  - or by a DFA
-/

/-
Imagine a word constructed of characters:
w₁ w₂ w₃ ... wᵢ ... wⱼ ... wₙ

If n is large enough (specifically n ≥ p, where p is the number of states in the DFA),
then because DFAs only have finite memory,
at least one state must be revisited while reading the word.

This is where the **pumping lemma** comes in.
We can find indices i and j such that the DFA is in the same state at position i and position j,
meaning wᵢ ... wⱼ forms a loop. For example:

pos: 1 2 3 4 5 6
chr: c a b a b d

Here the DFA revisits the same state at positions 2 and 5,
so the loop is w₂ ... w₅ = "abab" (specifically the repeating part "ab").

We can then pump this loop any number of times (including zero) and the word is still accepted:

0 pumps (remove the loop entirely):
  1 6
  c d

1 pump (original):
  1 2 3 4 5 6
  c a b a b d

2 pumps (add another cycle):
  1 2 3 4 5 6 7 8
  c a b a b a b d

The pumping lemma guarantees:
  - The loop wᵢ ... wⱼ is non-empty (you are always repeating something real)
  - The loop appears within the first p characters of the word
  - All pumped versions of the word are still accepted by the DFA

This is useful for proving a language is NOT regular:
  if no valid pumping decomposition exists for some long enough word,
  the language cannot be regular.
-/

/-
**How do we show certain languages are not regular?**

We know:
  - the loop must occur within the first n characters
      where n is the number of states in the automata


**Concrete Example**

Consider the language { a^n b^n | n ∈ ℕ }
Suppose this is regular, for a contradiction
Then there exists a pumping length p

Consider the word a^p · b^p
  - this forces the word to have length 2p so pumping lemma can be used

By the pumping lemma, we can write a^p · b^p as xyz such that
|xy| ≤ p
  - since xy is ≤ p
      then it means xy must be all a's - as we have p a's
      therefore y is made completely of a's
      this is used later again

|y| ≥ 1
xy^mz is accepted for every m ∈ ℕ

Since |xy| ≤ p, we know that xy = a^q for some q ≤ p -- this is later
Hence, y = a^r for some 1 ≤ r ≤ q
  - because we know y ≥ 1
      and the first p letters must be 'a'
      so y is just a repeating string of ≤p repeating a's

But then, xz = a^{p-r} b^p
  saying we found a loop 'y' that consisted entirely of A's
  and because for a language to be regular it must pump for all number of pumps
  when we reduce the pump to 0 (ie 0 cycles)
  then the number of a's and b's is no longer equal
  so the language cannot be regular


xz is not accepted, hence the pumping lemma does not hold
and therefore, the language { a^n b^n | n ∈ ℕ } is not regular

-/

---------------------------------
------ Formal Pumping Lemma -----

instance : HPow (Word Sigma) ℕ (Word Sigma)
where hPow := λ x n ↦ List.flatten (x^n)

open Dfa

def REG : Set (Lang Sigma)
:= {lang | ∃ A : DFA Sigma, Dfa.L A = lang}

theorem pumping_lemma : ∀ L₁ : Lang Sigma,
  L₁ ∈ REG →
    (∃ n : ℕ,
    ∀ w : Word Sigma,
    w.length ≥ n →
      ∃ x y z : Word Sigma,
      w = x ++ y ++ z ∧
      (x ++ y).length ≤ n ∧
      y.length ≥ 1 ∧
      ∀ m : ℕ, x ++ y^m ++ z ∈ L₁
    ) := by sorry
