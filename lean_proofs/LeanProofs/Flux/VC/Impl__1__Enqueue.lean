import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.RingBuffer
import LeanProofs.Flux.Struct.FluxSlice
import LeanProofs.User.Fun.RbValidIffInit
open Classical
set_option linter.unusedVariables false


namespace F



def Impl__1__Enqueue := 
 ∀ (s₀ : RingBuffer),
  ∀ (val₀ : Int),
   (rb_valid_iff_init (RingBuffer.ring s₀) (RingBuffer.hd s₀) (RingBuffer.tl s₀)) ->
    ((RingBuffer.hd s₀) ≠ (((RingBuffer.tl s₀) + 1) % (FluxSlice.len (RingBuffer.ring s₀)))) ->
     ((FluxSlice.len (RingBuffer.ring s₀)) > 0) ->
      ((RingBuffer.hd s₀) < (FluxSlice.len (RingBuffer.ring s₀))) ->
       ((RingBuffer.hd s₀) ≥ 0) ->
        ((RingBuffer.tl s₀) < (FluxSlice.len (RingBuffer.ring s₀))) ->
         ((RingBuffer.tl s₀) ≥ 0) ->
          ((¬(SmtMap_select (t0 := Int) (t1 := Prop) (FluxSlice.inits (RingBuffer.ring s₀)) (RingBuffer.tl s₀)))) ∧
          (((FluxSlice.len (RingBuffer.ring s₀)) ≥ 0) ->
           (((FluxSlice.len (RingBuffer.ring s₀)) ≠ 0)) ∧
           (((FluxSlice.len (RingBuffer.ring s₀)) ≠ 0) ->
            (((((RingBuffer.tl s₀) + 1) % (FluxSlice.len (RingBuffer.ring s₀))) < (FluxSlice.len (RingBuffer.ring s₀)))) ∧
            ((rb_valid_iff_init (FluxSlice.mkFluxSlice₀ (FluxSlice.len (RingBuffer.ring s₀)) (SmtMap_store (t0 := Int) (t1 := Prop) (FluxSlice.inits (RingBuffer.ring s₀)) (RingBuffer.tl s₀) True)) (RingBuffer.hd s₀) (((RingBuffer.tl s₀) + 1) % (FluxSlice.len (RingBuffer.ring s₀)))))
            )
           )
          
end F
