import Proofs.CFG
import Proofs.Autom
open Lang Lang.Examples Dfa SigmaABC

variable (Sigma : Type)[Alphabet Sigma]

namespace Pda
-- PDA = NFA + stack
structure PDA' : Type 1 where
  Q : Type -- states
  [alphQ : Alphabet Q]
  Γ : Type -- Stack alphabet
  [alphΓ : Alphabet Γ]
  s : Q    -- initial state
  Z₀ : Γ    -- initial stack
  F : Finset Q -- set of final states
  δ : Q → Option Sigma → Γ → Finset (Q × List Γ)
variable (P : PDA' Sigma)

-- Example: a^{n}b^{3n}
-- Why might this not be regular, why would we need memory?

abbrev ID : Type := P.Q × Word Sigma × List P.Γ
-- instantaneous description
-- Initial example: use epsilon arrow to switch between b's and a's
-- Show paths in the pda, ask "is this automaton deterministic?"
-- Emphasize how determinism directly relates to the number of paths
-- Show deterministic version of PDA

/-
Exercises: Create a PDA for the following languages:
{a^nb^m | m > n}
{a^n ++ w ++ rev(w) ++ b^n | w is any word, rev(w) is its reverse}
-/

namespace Cfg

structure CFG' : Type 1 where
  NT : Type -- Nonterminal symbols
  [ alphNT : Alphabet NT]
  S : NT -- Initial symbol
  P : Finset (NT × Word (Sum NT Sigma )) -- Productions, derivations

-- Example: anbn
-- Convert to PDA

/-
Exercises: Convert the following CFGs into PDAs:
1.
E := E + E | E * E | ( E ) | a

2.
E := T | E + T
T := F | T * F
F := a | ( E )

3.
E := T E'
E' := + T E' | ε
T := F T'
T' := * F T' | ε
F := a | ( E )

-/

end Cfg
end Pda
