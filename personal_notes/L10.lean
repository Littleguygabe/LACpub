import Proofs.Lang
import Proofs.Autom

namespace pumping
open Lang Dfa
variable (Sigma : Type)[Alphabet Sigma]
instance : HPow (Word Sigma) ℕ (Word Sigma)
where hPow := λ x n ↦ List.flatten (x^n)
variable {Sigma : Type}[Alphabet Sigma]

def REG : Set (Lang Sigma)
:= {lang | ∃ A : DFA Sigma, Dfa.L A = lang}

/-

Talking about the halting problem - says something about regular languages

**What is a regular language?**
  A language that can be represented by a DFA, NFA or RE
    (as a RE or NFA can be converted to a DFA)

Given a regular language, we may not know the DFA,
  but we do know that is has some number n of finite states

So if we have accepted a word of length > n,
  then it must do a loop at some point within the DFA
But that must mean that the word traversing this loop multiple
  times is also in the language

We know:
  The first loop must occur in the first n steps,
  hence the repeated substring is also in the first n characters

So for all words longer than n,
There exists a non-empty subword within the first n characters
such that the word obtained by repeating or omitting this subword
is also accepted

TLDR:
  If we have more chars than states in an accepting word
    then we know there must be a loop somewhere within the word

  So we also know that the loop must occur within the first n characters
    else we wouldn't be able to accept the word

  And also we can either
    1. Remove the substring that creates the loop
    2. Add another instance of the substring that creates the loop
  and the new word would still be accepted
-/

-- So when we formailse all of this then we get the pumping lemma:

theorem pumping_lemma : ∀ L₁ : Lang Sigma,
  L₁ ∈ REG →
    (∃ n : ℕ,
    ∀ w : Word Sigma,
    w.length ≥ n ∧ w ∈ L₁ →
      ∃ x y z : Word Sigma,
      w = x ++ y ++z ∧
      (x ++ y).length ≤ n ∧
      y.length ≥ 1 ∧
      ∀ m : ℕ, x ++ y^m ++ z ∈ L₁
    ) := by sorry

/-

FOLLOW THIS STRUCTURE
  typically very rigid in this format

Used to show a language (L) is not regular:
  1. Assume L is regular
  2. Assume we have a pumping length n
  3. Choose w such that w.length ≥ n and w ∈ L
  4. Then show that for any split xyz = w with |xy| ≤ n and |y| ≥ 1,
      There exists some repetition of y's
      such that xy^mz is not in the language

Example: L = {a^n | n is prime}
1. Assume L is regular
2. That means we have a pumping length n
3. Let w = a^m where m is the first prime greater than n
    (Could pick any prime greater than n)
4. let x y z be such that xy = a^p for p ≤ n and y = a^q for 1 ≤ q ≤ p
Now consider x ++ y^s ++ z, What is this word?
  xy^sz = x ++ y^s ++ z
  x = a^{p-q}
  z = a^{m-p}
  y^s = a^{s*q}
  =
  xy^sz = a^{m+(s-1)q}

Now we need to pick an s such that
  m+(s-1)q is NOT a prime (proving the word isn't in the language)

pick s = m + 1
then:
  x ++ y^s ++ z = a^{m+(m+1-1)*q}
  =
  a^{m+m*q}
  =
  a^{m(1+q)}

Then as we can take out a factor of m or q
  that must be mean x ++ y^s ++z is not in L
  which contradicts the pumping lemma
  which must mean that L is not regular
-/

end pumping

--------------------------
---------- CFGs ----------

/-
What is the type of a regular expression?

data RE =
      terminal →  | ε - empty word
      terminal →  | {} - empty language
      terminal →  | {[x]} - language containing a single character
  non-terminal →  | RE + RE - re plus a re
  non-terminal →  | RE · RE - re concatenated with a re
  non-terminal →  | RE* - just a repeated re
  non-terminal →  | (RE) - putting a RE in brackets

(not only non-terminal because contain RE, the symbol itself is terminal)

this is an exaple of a context free grammar (CFG)
  used to define a context free language


A CFG consists of:
  - Non-Terminal characters (left hand side characters)
  - Terminal characters (right hand side characters)
  - Start character
  - Derivation Rules (transitions)

so for regular expressions the CFG is:
  - RE (non-terminal)
  - ε, {}, {[x]}, +, ·, *, ()
  - RE
  - defined by taking an RE and defining it into the other forms of RE
-/

/-
Example 2: Simple arithmetic formulas such as
  a + (a*a)

The CFG for example 2:
  - Non-Terminals : E (expressions), T (terms), F (factors)
  - Starting symbol : E (expression)
  - Terminals are : a, +, (, ), *
  - Derivation Rules:
      E => T
      E => E + T
      T => F
      T => T * F
      F => a
      F => (E)


The language of a CFG is all those
words over the terminal characters
such that there exists a chain
of derivation from the starting non-terminal
to that word

Note this is an um-ambiguous language
  because there is only 1 way to get to each character

  if we have mutliple ways of getting to a single character
  then it means the language is ambiguous
  as we can't determine the exact route taken to get to a character
-/
