import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.FluxSlice
open Classical
set_option linter.unusedVariables false


namespace F

@[ext]
structure RingBuffer  where
  mkRingBuffer₀ ::
    ring : FluxSlice 
    hd : Int 
    tl : Int 


end F
