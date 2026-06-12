import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.Impl__1__New
import Mathlib
import Lemmas
import ModLemmas
import Tactics
open Classical
set_option linter.unusedVariables false


namespace F

def Impl__1__New_proof : Impl__1__New := by
  unfold Impl__1__New
  repeat (any_goals (first | (intro) | apply And.intro | grind))
  rename_i ring₀ slice idx _
  obtain ⟨_, inits⟩ := slice
  simp_all
  have h1 : ring₀.len % ring₀.len = (0 : Int) := Int.emod_self
  have h2 : (0 : Int) ≤ (idx + ring₀.len - 0) % ring₀.len := Int.emod_nonneg _ (by omega)
  grind
end F
