import Proofs.Lang
import Proofs.Autom

open Lang Dfa DFA Nfa NFA Lang.Examples SigmaABC nfaDfa
variable {Sigma : Type}[Alphabet Sigma]
variable (A : DFA Sigma)

structure DFA : Type 1 where -- definition of a DFA
  Q : Type
  [alphQ : Alphabet Q]
  s : Q
  F : Finset Q
  δ : Q → Sigma → Q

structure NFA : Type 1 where -- definition of an NFA
  Q : Type
  [alphQ : Alphabet Q]
  S : Finset Q
  F : Finset Q
  δ : Q → Sigma → Finset Q

-------- DFA EXAMPLES --------
--DFA to accept words were if the num A's mod 2 = num B's mod 2

abbrev D₁ : DFA SigmaABC
:= {
  Q := Fin 4
  s := 0
  F := {0,3}
  δ := λ  | 0, a => 1
          | 0, b => 2
          | 0, c => 0
          | 1, a => 0
          | 1, b => 3
          | 1, c => 1
          | 2, a => 3
          | 2, b => 0
          | 2, c => 2
          | 3, a => 2
          | 3, b => 1
          | 3, c => 3
}

-- instead of using numbered states we can define our own states:
inductive StateEqParity : Type
| EE | EO | OE | OO
deriving Fintype, DecidableEq
open StateEqParity

abbrev D₂ : DFA SigmaABC
:= {
  Q := StateEqParity
  s := EE
  F := {EE,OO}
  δ := λ  | EE, a => OE
          | EE, b => EO
          | EE, c => EE
          | OE, a => EE
          | OE, b => OO
          | OE, c => OE
          | EO, a => OO
          | EO, b => EE
          | EO, c => EO
          | OO, a => EO
          | OO, b => OE
          | OO, c => OO
}
------------------------------
-------- NFA EXAMPLES --------

abbrev N₁ : NFA SigmaBin
:= {
  Q := Fin 3
  S := {0,1}
  F := {1}
  δ := λ  | 0, 1 => {0,1}
          | 1, 0 => {1,2}
          | 1, 1 => {0}
          | 2, 1 => {0, 2}
          | _, _ => {}
}

------------------------------
--------- DFA → NFA ----------

def dfa2nfa' (A : DFA Sigma) : NFA Sigma
:= {
  Q := A.Q
  S := {A.s}
  F := A.F
  δ := λ s w ↦ {A.δ s w}
    -- maps the input state s and word w to the singleton set of the transition function of the DFA
      -- trivial as each state becomes a singleton state
}

------------------------------
--------- NFA → DFA ----------

def nfa2dfa' (A : NFA Sigma) : DFA Sigma
:= {
  Q := Finset A.Q
  s := A.S
  F := ⟪ S ∈ nfaDfa.Pow A.Q |
    ∃ (q : A.Q), q ∈ S ∧ q ∈ A.F

    -- each set S in the power set of A's states
    -- where there exists a state q in S that is also in the final set of states of A

    -- because for each of the sets within the power set if the set contains atleast 1 terminal state then
    -- that set has atleast 1 way it can terminate so is a final state set
    -- then combine all the sets containing final states to produce a single final set

  ⟫
  δ := δ_step A
    -- uses the δ_step as it matches the correct type sig but operates over NFAs not DFAss
}
