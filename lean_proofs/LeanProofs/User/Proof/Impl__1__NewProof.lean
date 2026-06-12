import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.Impl__1__New
import Mathlib
import Lemmas
import Tactics
open Classical
set_option linter.unusedVariables false


namespace F

theorem mod_non_neg (a b : Int) : 0 < b -> 0 <= (a % b) := by
  intro h
  exact Int.emod_nonneg a (by omega)

theorem mod_lt (a b : Int) : 0 < b -> (a % b) < b := by
  intro h
  exact Int.emod_lt_of_pos a h

theorem mod_silly (a b : Int) : 0 <= a -> 0 <= b -> a < b ->  (a % b) = a := by
  intro ha hb hab
  exact Int.emod_eq_of_lt ha hab

def Impl__1__New_proof : Impl__1__New := by
  unfold Impl__1__New
  repeat (any_goals (first | (intro) | apply And.intro | grind))
  rename_i ring₀ slice idx _
  obtain ⟨_, inits⟩ := slice
  simp_all
  have h1 : (0 : Int) - 0 + ring₀.len = ring₀.len := by omega
  have h2 : ring₀.len % ring₀.len = (0 : Int) := Int.emod_self
  have h3 : (0 : Int) ≤ (idx + ring₀.len - 0) % ring₀.len := Int.emod_nonneg _ (by omega)
  grind
end F
