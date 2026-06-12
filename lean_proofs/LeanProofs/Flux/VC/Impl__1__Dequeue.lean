import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.RingBuffer
import LeanProofs.Flux.Struct.FluxSlice
import LeanProofs.User.Fun.RbValidIffInit
open Classical
set_option linter.unusedVariables false


namespace F

namespace Impl1DequeueKVarSolutions

-- cyclic (cut) kvars
def k0 (a'₇ : Int) (a'₈ : Int) (a'₉ : (SmtMap Int Prop)) (a'₁₀ : Int) (a'₁₁ : Int) : Prop :=
  True
-- acyclic (non-cut) kvars
def k1 (s₀ : RingBuffer) (val₀ : Int) (a'₁₂ : Int) (a'₁₃ : Int) (a'₁₄ : (SmtMap Int Prop)) (a'₁₅ : Int) (a'₁₆ : Int) (a'₁₇ : Int) : Prop :=
  ((((((((((rb_valid_iff_init) : ((FluxSlice -> (Int -> (Int -> Prop))))) (RingBuffer.ring s₀))) : ((Int -> (Int -> Prop)))) (RingBuffer.hd s₀))) : ((Int -> Prop))) (RingBuffer.tl s₀)) ∧ (a'₁₃ = (FluxSlice.len (RingBuffer.ring s₀))) ∧ (a'₁₄ = (FluxSlice.inits (RingBuffer.ring s₀))) ∧ (a'₁₅ = (RingBuffer.hd s₀)) ∧ (a'₁₆ = (RingBuffer.tl s₀)) ∧ (a'₁₇ = val₀) ∧ ((RingBuffer.hd s₀) ≠ (RingBuffer.tl s₀)) ∧ ((FluxSlice.len (RingBuffer.ring s₀)) > 0) ∧ ((RingBuffer.hd s₀) ≥ 0) ∧ ((RingBuffer.tl s₀) ≥ 0) ∧ ((RingBuffer.hd s₀) < (FluxSlice.len (RingBuffer.ring s₀))) ∧ ((RingBuffer.tl s₀) < (FluxSlice.len (RingBuffer.ring s₀))))
def k2 (s₀ : RingBuffer) (val₀ : Int) (a'₁₈ : Int) (a'₁₉ : Int) (a'₂₀ : (SmtMap Int Prop)) (a'₂₁ : Int) (a'₂₂ : Int) (a'₂₃ : Int) : Prop :=
  (((((((((((rb_valid_iff_init) : ((FluxSlice -> (Int -> (Int -> Prop))))) (RingBuffer.ring s₀))) : ((Int -> (Int -> Prop)))) (RingBuffer.hd s₀))) : ((Int -> Prop))) (RingBuffer.tl s₀)) ∧ (a'₁₉ = (FluxSlice.len (RingBuffer.ring s₀))) ∧ (a'₂₀ = (FluxSlice.inits (RingBuffer.ring s₀))) ∧ (a'₂₁ = (RingBuffer.hd s₀)) ∧ (a'₂₂ = (RingBuffer.tl s₀)) ∧ (a'₂₃ = val₀) ∧ ((RingBuffer.hd s₀) ≠ (RingBuffer.tl s₀)) ∧ ((FluxSlice.len (RingBuffer.ring s₀)) ≠ 0) ∧ ((FluxSlice.len (RingBuffer.ring s₀)) > 0) ∧ ((RingBuffer.hd s₀) ≥ 0) ∧ ((RingBuffer.tl s₀) ≥ 0) ∧ ((FluxSlice.len (RingBuffer.ring s₀)) ≥ 0) ∧ ((RingBuffer.hd s₀) < (FluxSlice.len (RingBuffer.ring s₀))) ∧ ((RingBuffer.tl s₀) < (FluxSlice.len (RingBuffer.ring s₀)))) ∨ ((((((((((rb_valid_iff_init) : ((FluxSlice -> (Int -> (Int -> Prop))))) (RingBuffer.ring s₀))) : ((Int -> (Int -> Prop)))) (RingBuffer.hd s₀))) : ((Int -> Prop))) (RingBuffer.tl s₀)) ∧ (a'₁₉ = (FluxSlice.len (RingBuffer.ring s₀))) ∧ (a'₂₀ = (FluxSlice.inits (RingBuffer.ring s₀))) ∧ (a'₂₁ = (RingBuffer.hd s₀)) ∧ (a'₂₂ = (RingBuffer.tl s₀)) ∧ (a'₂₃ = val₀) ∧ ((RingBuffer.hd s₀) ≠ (RingBuffer.tl s₀)) ∧ ((FluxSlice.len (RingBuffer.ring s₀)) ≠ 0) ∧ ((FluxSlice.len (RingBuffer.ring s₀)) > 0) ∧ ((RingBuffer.hd s₀) ≥ 0) ∧ ((RingBuffer.tl s₀) ≥ 0) ∧ ((FluxSlice.len (RingBuffer.ring s₀)) ≥ 0) ∧ ((RingBuffer.hd s₀) < (FluxSlice.len (RingBuffer.ring s₀))) ∧ ((RingBuffer.tl s₀) < (FluxSlice.len (RingBuffer.ring s₀)))))

end Impl1DequeueKVarSolutions


open Impl1DequeueKVarSolutions




def Impl__1__Dequeue := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : (SmtMap Int Prop)) -> (a3 : Int) -> (a4 : Int) -> Prop, ∃ k1 : (a0 : RingBuffer) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : (SmtMap Int Prop)) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> Prop, ∃ k2 : (a0 : RingBuffer) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : (SmtMap Int Prop)) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> Prop, 
 ∀ (s₀ : RingBuffer),
  (rb_valid_iff_init (RingBuffer.ring s₀) (RingBuffer.hd s₀) (RingBuffer.tl s₀)) ->
   ((RingBuffer.hd s₀) ≠ (RingBuffer.tl s₀)) ->
    ((FluxSlice.len (RingBuffer.ring s₀)) > 0) ->
     ((RingBuffer.hd s₀) < (FluxSlice.len (RingBuffer.ring s₀))) ->
      ((RingBuffer.hd s₀) ≥ 0) ->
       ((RingBuffer.tl s₀) < (FluxSlice.len (RingBuffer.ring s₀))) ->
        ((RingBuffer.tl s₀) ≥ 0) ->
         ((SmtMap_select (t0 := Int) (t1 := Prop) (FluxSlice.inits (RingBuffer.ring s₀)) (RingBuffer.hd s₀))) ∧
         (∀ (a'₀ : Int),
          ((k0 a'₀ (FluxSlice.len (RingBuffer.ring s₀)) (FluxSlice.inits (RingBuffer.ring s₀)) (RingBuffer.hd s₀) (RingBuffer.tl s₀)))) ∧
         (∀ (val₀ : Int),
          ((k0 val₀ (FluxSlice.len (RingBuffer.ring s₀)) (FluxSlice.inits (RingBuffer.ring s₀)) (RingBuffer.hd s₀) (RingBuffer.tl s₀))) ->
           (∀ (a'₂ : Int),
            ((k0 a'₂ (FluxSlice.len (RingBuffer.ring s₀)) (FluxSlice.inits (RingBuffer.ring s₀)) (RingBuffer.hd s₀) (RingBuffer.tl s₀))) ->
             ((k1 s₀ val₀ a'₂ (FluxSlice.len (RingBuffer.ring s₀)) (FluxSlice.inits (RingBuffer.ring s₀)) (RingBuffer.hd s₀) (RingBuffer.tl s₀) val₀))) ∧
           (∀ (a'₃ : Int),
            ((k1 s₀ val₀ a'₃ (FluxSlice.len (RingBuffer.ring s₀)) (FluxSlice.inits (RingBuffer.ring s₀)) (RingBuffer.hd s₀) (RingBuffer.tl s₀) val₀)) ->
             ((k0 a'₃ (FluxSlice.len (RingBuffer.ring s₀)) (FluxSlice.inits (RingBuffer.ring s₀)) (RingBuffer.hd s₀) (RingBuffer.tl s₀)))) ∧
           (((FluxSlice.len (RingBuffer.ring s₀)) ≥ 0) ->
            (((FluxSlice.len (RingBuffer.ring s₀)) ≠ 0)) ∧
            (((FluxSlice.len (RingBuffer.ring s₀)) ≠ 0) ->
             (∀ (a'₄ : Int),
              ((k0 a'₄ (FluxSlice.len (RingBuffer.ring s₀)) (FluxSlice.inits (RingBuffer.ring s₀)) (RingBuffer.hd s₀) (RingBuffer.tl s₀))) ->
               ((k2 s₀ val₀ a'₄ (FluxSlice.len (RingBuffer.ring s₀)) (FluxSlice.inits (RingBuffer.ring s₀)) (RingBuffer.hd s₀) (RingBuffer.tl s₀) val₀))) ∧
             (∀ (a'₅ : Int),
              ((k2 s₀ val₀ a'₅ (FluxSlice.len (RingBuffer.ring s₀)) (FluxSlice.inits (RingBuffer.ring s₀)) (RingBuffer.hd s₀) (RingBuffer.tl s₀) val₀)) ->
               ((k0 a'₅ (FluxSlice.len (RingBuffer.ring s₀)) (FluxSlice.inits (RingBuffer.ring s₀)) (RingBuffer.hd s₀) (RingBuffer.tl s₀)))) ∧
             (((((RingBuffer.hd s₀) + 1) % (FluxSlice.len (RingBuffer.ring s₀))) < (FluxSlice.len (RingBuffer.ring s₀)))) ∧
             ((rb_valid_iff_init (FluxSlice.mkFluxSlice₀ (FluxSlice.len (RingBuffer.ring s₀)) (SmtMap_store (t0 := Int) (t1 := Prop) (FluxSlice.inits (RingBuffer.ring s₀)) (RingBuffer.hd s₀) False)) (((RingBuffer.hd s₀) + 1) % (FluxSlice.len (RingBuffer.ring s₀))) (RingBuffer.tl s₀))) ∧
             (∀ (a'₆ : Int),
              ((k2 s₀ val₀ a'₆ (FluxSlice.len (RingBuffer.ring s₀)) (FluxSlice.inits (RingBuffer.ring s₀)) (RingBuffer.hd s₀) (RingBuffer.tl s₀) val₀)))
             )
            )
           )
         
end F
