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

-- The halting problem
  -- says something about reuglar languages
/-
What is a regular language?
  > A language that can be represented by a DFA (or NFA or RE)

Give a regular language we may not know the DFA,
but we know it has some number `n` of states

so if we have any word of length > `n` it must visit atleast one state more than once
  > ie it must traverse some non-empty loop in the DFA

So that must mean that the word doing this loop multiple times is also in the language

So when does this loop occur?
  > The first loop must occur in the first `n` steps
  > So the repeated substring is also in the first `n` characters

So for all words longer than `n`
there is some non-empty sub word in the first `n` characters
such that the word obtained by repeating or omitting this subword is also accepted
ie
  > if a-ab-a is accepted with `ab` as our subword
  > the word a-a obtained from omitting `ab` is also accepted (as we just don't loop)
  > the word a-ab-ab-a obtained from repeating the `ab` subword is also accepted (as we just loop more times)

    > all we're doing is changing the number of loops we
-/
-- ! So by formalising this we get the **Pumping Lemma**

theorem pumping_lemma : ∀ L₁ : Lang Sigma,
  L₁ ∈ REG → -- if the language is regular
    (∃ n : ℕ, -- there exists some number n (number of states in DFA)
    ∀ w : Word Sigma, -- such that for all words
    w.length ≥ n ∧ w ∈ L₁ → -- where the word length is greater than the number of states
                            -- and the word is in the the language
      ∃ x y z : Word Sigma, -- there exists words x y z
      w = x ++ y ++ z ∧ -- such that the word w is the concatenation of x y z
      (x ++ y).length ≤ n ∧ -- and the length of the concatenation of x y
                            -- ≤ the number of states in our DFA
      y.length ≥ 1 ∧ -- and the length of y (the subword we loop) ≥ 1
      ∀ m : ℕ, x ++ y^m ++ z ∈ L₁ -- and for all natural numbers m, if we repeat y m times
                                  -- the word created is still in our language
    ) := by sorry

-- ! This is then used to show a language is not regular
-- 1. Assume the language is regular
-- 2. Then prove that the pumping lemma does not hold
/- ? Then how do we prive the pumping lemma does not hold?
by proving the negation of `pumping_lemma`

1. Assume we have a pumping length `n`
2. We choose a w such that:
  w.length ≥ n
  w ∈ L

3. Then we show that for any split xyz = w with
  (x++y).length ≤ n
  y.length ≥ 1
There exists some repeitions of y's such that xy^mz is not in the language
-/

/- ! Example L = {a^n | n is prime}
1. Assume L is regular

2. That means we have a pumping length n

3. Let w = a^m
  where m is the first prime greater than n

4. Let x y z be such that
  xy = a^p for p ≤ n
  y = a^q for 1 ≤ q ≤ p

Now consider x ++ y^s ++ z. What is this word?
  xy^sz = x ++ y^s ++ z
    x = a^{p - q}
    z = a^{m - p}
    y^s = a^{s × q}
  so
  xy^sz = a^{p - q} ++ a^{s × q} ++ a^{m - p}
        = a^{p - q} × a^{s × q} × a^{m - p}
        = a^{p - q + s × q + m - p}
        = a^{- q + s × q + m}
        = a^{(s - 1) × q + m}

If we pick s = m+1
then x ++ y^s ++ z = a^{(m + 1 - 1) × q + m}
                   = a^{m (1 + q)}

hence not prime as we can take a factor of m or 1 + q out

That must mean that x ++ y^s ++ z is not in L
That contradicts the pumping lemma
That must mean that L is not regular
-/

-- ! Moving onto Context Free Grammars (CFG)

/- ? First what is the definition of a regular expression

Components, either:
  empty word - ε
  or empty language - ∅
  or language that contains a single character - {[x]}
  or regular expression + regular expression - ∨
  or regular expression ++ regular expression - ∧
  or regular expression * - repeating RE
  or (regular expression) - putting a RE in brackets
-/

/- ? So how is it created?
Start with a character regular expression, ie `S`
  Called a non-terminal in CFG's

Which is then replaced by any of the components of a regular expression
-/

/- ? What are the components of a context free grammar (CFG)
- Non-Terminal Characters
    Only 1 in regular expr (RE)
- Terminal Characters
    Every component of a regular expression (shown above)
- A Starting Character
    Only non-terminal we have (RE)
- Derivation Rules
    How we translate RE (Non-terminal starting character) into a structure defined by the language
-/

/- ! Example of creating a CFG for a language
Language of creating simple arithmetic formulas like
  a + (a*a)

Non-terminals are
  1. E - one for expressions
  2. T - one for terms
  3. F - one for factors

Starting symbol: S = E (expressions)
Terminals here are: a, +, (, ), *

Derivation rules:
  E => T
    An Expression can become a Term

  E => E + T
    An Expression can be an Expression plus a Term

  T => F
    A Term can be a Factor

  T => T * F
    A Term can be a Term multiplied by a Factor

  F => a
    A Factor can be a Number

  F => (E)
    A Factor can be an Expression within brackets
-/

/- ? How would this generate a formula?
Eg a + (a*a)

a + (a*a) = E
=> E + T - E is E + T
=> T + F - E is T, T is F
=> F + (E) - T is F, F is (E)
=> a + (T) - F is a, E is T
=> a + (T * F) - T is T * F
=> a + (F * a) - T is F, F is a
=> a + (a * a) - F is a

which then gives us our final expression

So its like defining an algebraic data type for a DSL in haskell

so the language of a CFG is
all those words oer the terminal characters,
such that there exists a chain of derivations
from the starting non-terminal to that word

-/
