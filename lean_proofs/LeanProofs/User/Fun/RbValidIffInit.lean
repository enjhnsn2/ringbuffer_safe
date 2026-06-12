import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.FluxSlice
open Classical
set_option linter.unusedVariables false


namespace F

@[grind]
def rb_idx_valid (len hd tl idx : Int) : Prop :=
  0 ≤ idx ∧
  idx < len ∧
  ((idx + len - hd) % len) < ((tl - hd + len) % len)

@[grind]
noncomputable def rb_valid_iff_init : FluxSlice -> Int -> Int -> Prop :=
  fun s hd tl =>
    ∀ idx : Int,
      idx < s.len →
      (SmtMap_select s.inits idx ↔ rb_idx_valid s.len hd tl idx)


end F
