/-
COMP2012 (LAC) 2026

Exercise 4

We are asking you to provide informal proofs
(i.e. in English) that the languages L₁, L₂ are
not regular. We are using Lean to specify the setup,
but you should give your answer in a comment.

If you are very Lean savvy you can try to do at
least the outline in Lean and rely on some lemmas
which are evident but which you don't want to
prove.
-/
import Mathlib.Tactic.DeriveFintype
import Proofs.Lang
import Proofs.Autom
open Lang Dfa DFA Lang.Examples SigmaABC

-- Here are the two languages:
abbrev L₁ : Lang SigmaABC
:= { a^n ++ b^m ++ c^(m+n)| (m : ℕ)(n : ℕ)}

abbrev L₂ : Lang SigmaABC
:= { w | w.count a = 2*(w.count b)
       ∧ w.count b = 2*(w.count c) }

-- this is the pumping lemma in Lean
-- we add it as an axiom here but it is
-- provable from our definition of DFA.
variable (Sigma : Type)[Alphabet Sigma]
instance : HPow (Word Sigma) ℕ (Word Sigma)
where hPow := λ x n ↦ List.flatten (x^n)
variable {Sigma : Type}[Alphabet Sigma]

def REG : Set (Lang Sigma)
:= {lang | ∃ A : DFA Sigma, Dfa.L A = lang}

axiom pumping_lemma : ∀ L₁ : Lang Sigma,
  L₁ ∈ REG →
    (∃ n : ℕ,
    ∀ w : Word Sigma,
    w.length ≥ n ∧ w ∈ L₁ →
      ∃ x y z : Word Sigma,
      w = x ++ y ++ z ∧
      (x ++ y).length ≤ n ∧
      y.length ≥ 1 ∧
      ∀ m : ℕ, x ++ y^m ++ z ∈ L₁
    )

-- Exercises

theorem ex1 : ¬ ∃ A : DFA SigmaABC, L A = L₁
:= sorry
/-
suppose l₁ is regular. let p be the pumping length given by the pumping lemma
consider the word w = a^p b^p c^(2p) clearly w ∈ l₁ and |w| = 4p ≥ p
by the pumping lemma, w can be split into xyz such that:
1. |xy| ≤ p
2. |y| ≥ 1
3. for all i ≥ 0, xy^iz ∈ l₁

since |xy| ≤ p and w starts with p 'a's, y must consist entirely of 'a's
let y = a^k for some k ≥ 1
if we pump i = 2, the word xy^2z = a^(p+k) b^p c^(2p)
for this word to be in l₁, the number of 'c's must equal the sum of 'a's and 'b's
however, (p+k) + p = 2p + k since k ≥ 1, 2p + k ≠ 2p
thus xy^2z ∉ l₁, which contradicts the pumping lemma
therefore, l₁ is not regular
-/

theorem ex2 : ¬ ∃ A : DFA SigmaABC, L A = L₂
:= sorry
/-
suppose l₂ is regular let p be the pumping length given by the pumping lemma
consider the word w = a^(4p) b^(2p) c^p
since 4p = 2*(2p) and 2p = 2*p, w ∈ l₂ also |w| = 7p ≥ p
by the pumping lemma, w can be split into xyz such that:
1. |xy| ≤ p
2. |y| ≥ 1
3. for all i ≥ 0, xy^iz ∈ l₂

since |xy| ≤ p and w starts with 4p 'a's, y must consist entirely of 'a's
let y = a^k for some k ≥ 1
if we pump down (i = 0), the word xz = a^(4p-k) b^(2p) c^p
for xz to be in l₂, it must satisfy count(a, xz) = 2*count(b, xz)
this would mean 4p - k = 2*(2p) = 4p, which implies k = 0
this contradicts k ≥ 1
therefore, l₂ is not regular
-/
