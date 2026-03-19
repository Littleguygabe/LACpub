/- COMP2065 (IFR) - Tutorial 2 -/

variable (P Q R : Prop)

/- Constructive (Intuitionistic) Logic
-- ↔ Prove by evidence
-/

/- Double Negation Introduction -/
theorem dni : P → ¬ ¬ P := by
  intro p
  intro np
  contradiction -- can also call cases (np p)


/- (Constructive direction of) Contraposition -/
theorem cp_to : (P → Q) → ¬ Q → ¬ P := by
  intro pq
  intro nq
  intro p
  have q : Q := pq p
  cases (nq q) -- same as calling contradiction
  -- this is why contradiction is intuitionistic because its just built on top of cases


/- Classical Logic
-- ↔ Can be proved by adding Law of Excluded Middle (em) : P ∨ ¬ P
-- ↔ Can be checked by building truth table
-/

open Classical

/- Double Negation Elimination -/
theorem dne : ¬ ¬ P → P := by
  cases (em P) with
  |inl p =>
    intro _
    exact p

  |inr np =>
    intro nnp
    have f : False := by
      apply nnp
      exact np
    cases f



/- P      ¬ P     ¬ ¬ P   ¬ ¬ P → P
-- True   False   True    True
-- False  True    False   True
-/

/- Pierce's Law -/
theorem pierce : ((P → Q) → P) → P := by
  cases (em P) with
  |inl p =>
    intro pqp
    exact p
  |inr np =>
    intro pqp
    apply pqp
    intro p

    cases (np p) -- same as calling contradiction

/- (Classical direction of) Contraposition -/
theorem cp_from : (¬ Q → ¬ P) → P → Q := by
  intro nqnp
  intro p
  cases (em Q) with
    |inl h =>
      exact h
    |inr n_h =>
      have np : ¬P := nqnp n_h
      cases np p --calling contradiction


/- All Classical Tautuologies are equivalent:
-- Law of Excluded Middle ↔
-- Double Negation Elimination ↔
-- Pierce's Law ↔
-- Classical direction of Contraposition ↔
-- Classical direction of De Morgan's Law ↔
-- ...
-/

/- Try to prove em using other classical laws -/

theorem em_pierce : P ∨ ¬ P := by
  cases (em P) with
    |inl h =>
      left
      exact h

    |inr nh =>
      right
      exact nh

theorem em_dne : P ∨ ¬ P := by
  sorry

/- No Provable
-- ↔ Can find counterexample by building truth table
-/

example : P ∧ ¬ P := by sorry

/- P     ¬ P    P ∧ ¬ P
-/

example : ¬ P → P := by sorry

/- P     ¬ P   ¬ P → P
-/

example : ¬ (P ∨ ¬ P) := by
  sorry
