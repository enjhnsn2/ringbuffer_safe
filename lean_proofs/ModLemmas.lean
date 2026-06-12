import Mathlib
open Classical
set_option linter.unusedVariables false

-- Central repository of modular arithmetic lemmas used across ring buffer proofs.

-- a % b is non-negative whenever b is positive.
theorem mod_non_neg (a b : Int) : 0 < b → 0 ≤ a % b :=
  fun h => Int.emod_nonneg a (by omega)

-- a % b is strictly less than b whenever b is positive.
theorem mod_lt (a b : Int) : 0 < b → a % b < b :=
  fun h => Int.emod_lt_of_pos a h

-- When 0 ≤ a < b, a % b = a (a is already its own representative).
theorem mod_eq_of_lt (a b : Int) (hlo : 0 ≤ a) (hhi : a < b) : a % b = a :=
  Int.emod_eq_of_lt hlo hhi
