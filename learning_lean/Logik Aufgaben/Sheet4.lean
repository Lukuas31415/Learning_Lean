/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics


/-!

# Logic in Lean, example sheet 4 : "and" (`∧`)

We learn about how to manipulate `P ∧ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following tactics:

* `cases'`
* `constructor`

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.
variable (P Q R : Prop)

example : P ∧ Q → P := by
  intro h1
  cases' h1 with hP hQ
  exact hP

example : P ∧ Q → Q := by
  sorry
  done

example : (P → Q → R) → P ∧ Q → R := by
  intro h1
  intro h2
  cases' h2 with hp hq
  apply h1 at hp
  apply hp at hq
  exact hq

example : P → Q → P ∧ Q := by
  intro h1
  intro h2
  constructor
  exact h1
  exact h2

/-- `∧` is symmetric -/
example : P ∧ Q → Q ∧ P := by
  intro h1
  constructor
  cases' h1 with hp hq
  exact hq
  cases' h1 with hp hq
  exact hp

example : P → P ∧ True := by
  intro h1
  constructor
  exact h1
  trivial

example : False → P ∧ False := by
  intro h1
  exfalso
  exact h1

/-- `∧` is transitive -/
example : P ∧ Q → Q ∧ R → P ∧ R := by
  intro h1
  intro h2
  cases' h1 with hp hq
  cases' h2 with hq hr
  constructor
  exact hp
  exact hr


example : (P ∧ Q → R) → P → Q → R := by
  intro h1
  intro h2
  intro h3
  apply h1
  constructor
  exact h2
  exact h3
