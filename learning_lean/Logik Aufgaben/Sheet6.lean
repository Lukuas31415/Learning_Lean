/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics


/-!

# Logic in Lean, example sheet 6 : "or" (∨`)

We learn about how to manipulate `P ∨ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following tactics

* `left` and `right`
* `cases'` (new functionality)

-/


-- Throughout this sheet, `P`, `Q`, `R` and `S` will denote propositions.
variable (P Q R S : Prop)

example : P → P ∨ Q := by
  intro h1
  left
  exact h1

example : Q → P ∨ Q := by
  sorry
  done

example : P ∨ Q → (P → R) → (Q → R) → R := by
  intro h1
  intro h2
  intro h3
  cases' h1 with hp hq
  apply h2 at hp
  exact hp
  apply h3 at hq
  exact hq

-- symmetry of `or`
example : P ∨ Q → Q ∨ P := by
  intro h1
  cases' h1 with hp hq
  right
  exact hp
  left
  exact hq

-- associativity of `or`
example : (P ∨ Q) ∨ R ↔ P ∨ Q ∨ R := by
  constructor
  intro h1
  cases' h1 with h1 hr
  cases' h1 with hp hq
  left
  exact hp
  right
  left
  exact hq
  right
  right
  exact hr
  intro h1
  cases' h1 with hp h1
  left
  left
  exact hp
  cases' h1 with hq hr
  left
  right
  exact hq
  right
  exact hr

example : (P → R) → (Q → S) → P ∨ Q → R ∨ S := by
  sorry
  done

example : (P → Q) → P ∨ R → Q ∨ R := by
  sorry
  done

example : (P ↔ R) → (Q ↔ S) → (P ∨ Q ↔ R ∨ S) := by
  intro h1
  intro h2
  rw[h1]
  rw[h2]

-- de Morgan's laws
example : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q := by
  constructor
  intro h1
  constructor
  intro h2
  apply h1
  left
  exact h2
  intro h2
  apply h1
  right
  exact h2
  intro h1
  intro h2
  cases' h1 with hnp hnq
  cases' h2 with hp hq
  apply hnp
  exact hp
  apply hnq
  exact hq

example : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q := by
  sorry
  done
