import Proofs.Lang
open Lang

variable (Sigma : Type)[Alphabet Sigma]


open Sum

structure CFG : Type 1 where
  NT : Type
  [alphNT : Alphabet NT]
  S : NT
  P : Finset (NT × Word (Sum NT Sigma))
    -- has a left hand side that is Non-Terminal (NT), a right hand side that has a sequence
      -- Sum adds 2 things together, but remembers what they are



variable {Sigma : Type}[Alphabet Sigma]

variable (G : CFG Sigma)

abbrev Sent : Type
:= Word (Sum G.NT Sigma)

abbrev Deriv : Set (Sent G × Sent G)
:= {(α, β) |
    ∃ w w' : Sent G, ∃ A : G.NT, ∃ γ : Sent G,
    α = w ++ [inl A] ++ w'
    ∧ β = w ++ γ ++ w'
    ∧ (A, γ) ∈ G.P
}

-- A for artithmetic - defined inductively
inductive SigmaA : Type
| a | plus | times | lpar | rpar
deriving Fintype, DecidableEq
-- a, +, *, (, )


-- defining the terminal symbols
inductive NTA : Type
| E | T | F
deriving Fintype, DecidableEq

open SigmaA
open NTA
open CFG

abbrev GA : CFG SigmaA
:= {
  NT := NTA,
  S := E,
  P := {(E , [inl T]), -- need inl as we defined p using sum
        (E , [inl E , inr plus, inl T]),
        (T , [inl F]),
        (T , [inl T, inr times, inl F]),
        (F , [inr a]),
        (F , [inr lpar, inl E, inr rpar])
        }
}
