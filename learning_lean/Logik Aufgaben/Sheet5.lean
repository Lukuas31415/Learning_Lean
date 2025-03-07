/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 5 : "iff" (`↔`)

We learn about how to manipulate `P ↔ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following two new tactics:

* `refl`
* `rw`

-/


variable (P Q R S : Prop)

example : P ↔ P := by
  rfl


example : (P ↔ Q) → (Q ↔ P) := by
  intro h1
  rw[h1]

example : (P ↔ Q) ↔ (Q ↔ P) := by
  constructor
  intro h1
  rw[h1]
  intro h1
  rw[h1]

example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  intro h1
  intro h2
  rw[h1]
  exact h2



example : P ∧ Q ↔ Q ∧ P := by
  constructor
  intro h1
  constructor
  cases' h1 with hp hq
  exact hq
  cases' h1 with hp hq
  exact hp
  intro h1
  constructor
  cases' h1 with hp hq
  exact hq
  cases' h1 with hp hq
  exact hp


example : (P ∧ Q) ∧ R ↔ P ∧ Q ∧ R := by
  constructor
  intro h1
  cases' h1 with h2 hr
  cases' h2 with hp hq
  constructor
  exact hp
  constructor
  exact hq
  exact hr
  intro h1
  cases' h1 with hp h2
  cases' h2 with hq hr
  constructor
  constructor
  exact hp
  exact hq
  exact hr


example : P ↔ P ∧ True := by
  constructor
  intro h1
  constructor
  exact h1
  trivial
  intro h1
  cases' h1 with h1 h2
  exact h1

example : False ↔ P ∧ False := by
  sorry
  done

example : (P ↔ Q) → (R ↔ S) → (P ∧ R ↔ Q ∧ S) := by
  sorry
  done

example : ¬(P ↔ ¬P) := by
  intro h1
  cases' h1 with h1 h2
  by_cases hp:P
  apply h1
  exact hp
  exact hp
  apply h2 at hp
  apply h1
  exact hp
  exact hp
