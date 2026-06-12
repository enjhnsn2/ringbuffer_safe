import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.FluxSlice
import LeanProofs.User.Fun.RbValidIffInit
open Classical
set_option linter.unusedVariables false


namespace F



def Impl__1__New := 
 ∀ (ring₀ : FluxSlice),
  (((FluxSlice.len ring₀) > 0) ∧ ((FluxSlice.inits ring₀) = (SmtMap_default (t0 := Int) (t1 := Prop) False))) ->
   ((rb_valid_iff_init ring₀ 0 0)) ∧
   ((0 < (FluxSlice.len ring₀))) ∧
   ((0 < (FluxSlice.len ring₀)))
   
end F
