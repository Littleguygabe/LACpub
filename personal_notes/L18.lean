
/-
Chomsky Hiearchy Refresh

Level 3 - the Narrowest
  DFA

Level 2 - Encapsulates Level 3
  PDAs (NFA with Memory)

Level 1 - Encapsulates Level 2
  Context Sensitive Languages
  Turing Machines with a finite tape

Level 0 - Encapsulates Level 1
  Turing Machines (DFA with a tape)
-/

import Proofs.TM

namespace halt

open Tm Lang Lang.Examples Classical

inductive Star' {A : Type}(R : A × A → Prop)
    : A × A → Prop
| refl : ∀ a , Star' R (a , a)
| step : ∀ a b c , R (a , b)
      → Star' R (b , c) → Star' R (a , c)
-- transitive, reflexive closure


variable {Sigma : Type}
[Fintype Sigma][DecidableEq Sigma]

variable (M : TM Sigma)

-- A word w is accepted by a TM if it reaches an accepting ID

abbrev accepts: ID M → Bool
| (_, q, _) => q ∈ M.F

abbrev L : Lang Sigma
:= {w | ∃ st, accepts M st ∧ Star' (Step M) (init M w, st)}

abbrev stuck : ID M → Prop
| st => ¬ ∃ st' , Step M (st, st')

abbrev L_no : Lang Sigma
:= {w | ∃ st, stuck M st ∧ Star' (Step M) (init M w, st)}

abbrev L_halts : Lang Sigma
:= {w | w ∈ L M ∨ w ∈ L_no M}

abbrev decides : Prop
:= ∀ w, w ∈ L_halts M

/-

Halting problem
  It tells us whether a given TM and input halts

This gives us a yes-no answer - so it's a language
  ie accept reject

If we encode a TM with its input as a word,
then we may be able to create a machine
that tells us whether or not the TM will halt on the input

how we do it:
-/

abbrev SigmaBin : Type
:= Fin 2
-- 0 or 1

def expand : Word SigmaBin → Word SigmaBin
| [] => []
| (x :: w) => 0 :: x :: (expand w)
-- so we get 0 :: character :: 0 :: character and so on

def pair : Word SigmaBin × Word SigmaBin → Word SigmaBin
| (w,v) => expand w ++ [1] ++ expand v
-- so when we see a 1 we know we've hit the end of the word w

axiom pair_injective : Function.Injective pair

abbrev encodeTM : TM SigmaBin → Word SigmaBin
:= sorry
axiom encodeTM_injective : Function.Injective encodeTM

abbrev encode : TM SigmaBin × Word SigmaBin → Word SigmaBin
| (M, x) => pair (encodeTM M, x)

abbrev halting_encodings : Lang SigmaBin
:= {w | ∃ M v, w = encode (M, v) ∧ v ∈ L_halts M}

-- as it turns out turing machines can simulate turing machines

abbrev U : TM SigmaBin -- Universal Turing Machine
:= sorry

abbrev U_ok : ∀ M w, encode (M, w) ∈ L U ↔ w ∈ L M := sorry

abbrev H : TM SigmaBin := sorry
abbrev H_ok : L H = halting_encodings := sorry

variable (DH : TM SigmaBin)
axiom L_DH : L DH = halting_encodings
axiom d_DH : decides DH

abbrev W : TM SigmaBin
:= sorry

lemma w_ok : ∀ w, w ∈ L_halts W ↔ pair (w,w) ∉ L DH := sorry

lemma w1 : encodeTM W ∈ L_halts W ↔ pair (encodeTM W, encodeTM W) ∉ L DH
:= by apply w_ok

lemma w2 (DH : TM SigmaBin) : encodeTM W ∈ L_halts W ↔
            pair (encodeTM W, encodeTM W) ∉ halting_encodings := by
            rw [←L_DH DH]
            apply w1

lemma W3 (DH : TM SigmaBin) : encodeTM W ∈ L_halts W ↔ encodeTM W ∉ L_halts W := by
  constructor
  · intro inhalts
    apply (w2 DH).1 at inhalts
    intro inhalts2
    apply inhalts
    exists W
    exists encodeTM W
  · intro ninhalts
    apply (w2 DH).2
    intro pair
    apply ninhalts
    cases pair with
    | intro TM form =>
      cases form with
      | intro pword form =>
        cases form with | intro encword winlang
        rw [encode] at encword
        have eq : (encodeTM W, encodeTM W) = (encodeTM TM, pword) := by
          apply pair_injective
          assumption
        have tmeqw : W = TM := by
          apply encodeTM_injective
          injection eq
        have pwordeqencw : encodeTM W = pword := by
          injection eq
        rw [pwordeqencw]
        rw [tmeqw]
        exact winlang

-- And from that contradiction we derive falsehood, we have proven False = True and pigs can fly!
lemma boom (DH : TM SigmaBin) : ⊥ := by
  have boom : encodeTM W ∈ L_halts W ↔ encodeTM W ∉ L_halts W := by apply W3; apply DH
  cases boom with
  | intro lr rl =>
    apply lr
    apply rl
    intro inhalts
    apply lr
    exact inhalts
    exact inhalts
    apply rl
    intro inhalts
    apply lr
    exact inhalts
    exact inhalts

end halt
