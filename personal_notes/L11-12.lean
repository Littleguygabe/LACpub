import Proofs.Lang
open Lang

variable (Sigma : Type)[Alphabet Sigma]

open Sum

structure CFG : Type 1 where
  NT : Type -- non-terminal symbols
  [alphNT : Alphabet NT]
  S : NT -- start symbol

  -- production has a left hand side of non-terminal
  -- and a right hand side which is a sequence of elements of sigma and terminal & non-terminal symbols
  P : Finset (NT × Word (Sum NT Sigma))



variable {Sigma : Type}[Alphabet Sigma]

variable (G : CFG Sigma)

------------------------------------
---------- Deriving a CFG ----------

-- basically how does a CFG construct a string

abbrev Sent : Type -- sentential form
:= Word (Sum G.NT Sigma)
-- this is needed so that terminal and non-terminal chars can exist in the same list


abbrev Deriv : Set (Sent G × Sent G)
:= {(α, β) |
    ∃ w w' : Sent G, ∃ A : G.NT, ∃ γ : Sent G,
    α = w ++ [inl A] ++ w'
    ∧ β = w ++ γ ++ w'
    ∧ (A, γ) ∈ G.P
}
/-
in english

this is essentially a step

how do we allow a step?
we say somewhere in the middle of the left-hand side, there is an NT symbol
  ie there is a word on the left and right of the NT symbol

  so α = word + non-terminal symbol + word

and β is the same, but
  we are replacing the non-terminal with a right hand side of a production in the grammar
    ie a terminal symbol
-/

/-
Recursively building a CFG string until there is only terminal chars
-/
inductive DerivStar : Set (Sent G × Sent G)
| refl : ∀ α , DerivStar (α,α) -- base the case
| step : ∀ α β γ, -- recursive case
  Deriv G (α, β) → DerivStar (β, γ) → DerivStar (α, γ)

-- converts a list of pure terminals and converts to sentential form
abbrev emb : Word Sigma → Sent G
:= List.map inr

abbrev L : Lang Sigma
:= {w | DerivStar G ([inl G.S], emb G w)}



------------------------------------
---------- Defining a CFG ----------


-- A for Arithmetic

inductive SigmaA : Type-- the language of terminal symbols - left side
| a | plus | times | lpar | rpar
deriving Fintype, DecidableEq
-- a, +, *, (, )

inductive NTA : Type -- our non-terminal symbol - right side
| E | T | F
deriving Fintype, DecidableEq
-- this can be replaced with Fin 3
  -- but just less readable as we use 0 1 2 instead of E T F

open SigmaA
open NTA
open CFG

abbrev GA : CFG SigmaA
:={ NT := NTA,
    S := E,
    P := {(E, [inl T]),
          (E, [inl T, inr plus, inl T]),
          (T, [inl F]),
          (T, [inl T, inr times, inl F]),
          (F, [inr a]),
          (F, [inr lpar, inl E, inr rpar])
        }

}

open SigmaA

abbrev GAA : CFG SigmaA
:= {
    NT := Fin 1
    S := 0
    P := { (0 , [inl 0,inr plus,inl 0 ]),
           (0 , [inl 0,inr times,inl 0]),
           (0 , [inr a]),
           (0 , [inr lpar,inl 0,inr rpar])
    }
}

theorem today : L GA = L GAA := by sorry
  -- how would we prove this?

/-
the first CFG (GA) is preffered because it specifies the different
binding strength of plus and times

in the second one (GAA) when we produce a tree of the order of operations
we lose the fact that times binds stronger than times so get the wrong output

hence we prefer the more specific CFG (GA)
-/

/-
What is a parse tree?



What does it mean that a grammar is ambiguous?
  There is more than one parse tree for atleast 1 word

How do we show this in lean:
-/

mutual

  inductive PT : G.NT → Type

    | node : ∀ {A}, ∀ {α}, (A, α ) ∈ G.P → PTSent α → PT A

  inductive PTSent : Sent G → Type

    | nil  : PTSent []
    | NT : ∀ {A}, ∀ {α} , PT A → PTSent α → PTSent ((inl A)::α)
    | T : ∀ α , ∀ a, PTSent α → PTSent (a :: α)

end

open PT
open PTSent

mutual
-- now defining the word at the bottom of the parse tree
  -- the 'yield'

  def yield {A : G.NT }: PT G A → Word Sigma
    | node _ t => yieldSent t

  def yieldSent {α : Sent G} : PTSent G α → Word Sigma
    | nil => []
    | NT t ts => yield t ++ yieldSent ts
    | T a ts => a :: yieldSent ts

end


-- formal def for ambigous
abbrev Amb : Prop
:= ∃ w : Word Sigma ,
   ∃ A : G.NT , ∃ t t' : PT G A , yield G t = w ∧ yield G t' = w
   ∧ t ≠ t'
