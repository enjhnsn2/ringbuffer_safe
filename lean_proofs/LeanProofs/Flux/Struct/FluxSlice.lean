import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F

@[ext]
structure FluxSlice  where
  mkFluxSlice₀ ::
    len : Int 
    inits : (SmtMap Int Prop) 


end F
