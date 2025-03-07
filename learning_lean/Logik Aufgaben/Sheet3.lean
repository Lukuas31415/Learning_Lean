/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- import all the tactics

/-!

# Logic in Lean, example sheet 3 : "not" (`¬`)

We learn about how to manipulate `¬ P` in Lean.

# The definition of `¬ P`

In Lean, `¬ P` is *defined* to mean `P → false`. So `¬ P` and `P → false`
are *definitionally equal*. Check out the explanation of definitional
equality in the "equality" section of Part B of the course notes:
https://www.ma.imperial.ac.uk/~buzzard/xena/formalising-mathematics-2023/Part_B/equality.html

## Tactics

You'll need to know about the tactics from the previous sheets,
and the following tactics may also be useful:

* `change`
* `by_contra`
* `by_cases`

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.
variable (P Q R : Prop)

example : ¬True → False := by
  by_contra h
  apply h
  trivial

example : False → ¬True := by
  intro h1
  change True -> False
  intro h2
  exact h1



example : ¬False → True := by
  intro h1
  trivial


example : True → ¬False := by
  intro h1
  change False -> False
  intro h2
  exact h2


example : False → ¬P := by
  intro h1
  change P->False
  intro h2
  exact h1


example : P → ¬P → False := by
  intro h1
  intro h2
  apply h2 at h1
  exact h1

example : P → ¬¬P := by
  intro h1
  intro h2
  apply h2 at h1
  exact h1

example : (P → Q) → ¬Q → ¬P := by
  intro h1
  intro h2
  intro h3
  apply h1 at h3
  apply h2 at h3
  exact h3

example : ¬¬False → False := by
  intro h1
  apply h1
  intro h2
  exact h2

example : ¬¬P → P := by
  sorry
  done

example : (¬Q → ¬P) → P → Q := by
  sorry
  done
