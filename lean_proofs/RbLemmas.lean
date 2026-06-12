import Mathlib
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.FluxSlice
import LeanProofs.User.Fun.RbValidIffInit
import ModLemmas
open Classical
set_option linter.unusedVariables false

namespace F

-- The tail slot is always empty: tl is never a valid index.
-- (Both sides of rb_idx_valid collapse to the same expression, so it's x < x.)
theorem rb_tl_not_valid (len hd tl : Int) :
    ¬ rb_idx_valid len hd tl tl := by
  grind


-- When the buffer is non-empty (hd ≠ tl), the head index is valid.
theorem rb_hd_valid (len hd tl : Int)
    (hlen : 0 < len)
    (hhd_lo : 0 ≤ hd) (hhd_hi : hd < len)
    (htl_lo : 0 ≤ tl) (htl_hi : tl < len)
    (hne : hd ≠ tl) :
    rb_idx_valid len hd tl hd := by
  simp only [rb_idx_valid]
  have hlhs : (hd + len - hd) % len = 0 := by
    conv_lhs => rw [show hd + len - hd = len by omega]
    exact Int.emod_self
  rw [hlhs]
  by_cases hlt : tl < hd
  · have : (tl - hd + len) % len = tl - hd + len := Int.emod_eq_of_lt (by omega) (by omega)
    omega
  · have : (tl - hd + len) % len = tl - hd := by
      have h1 : (tl - hd + len) % len = (tl - hd) % len := Int.emod_eq_add_self_emod.symm
      rw [h1]; exact Int.emod_eq_of_lt (by omega) (by omega)
    omega
end F


-- Two distinct indices in [0, len) have distinct shifted positions (· + len - hd) % len.
-- Used to show that advancing tl or hd cannot collide with an unrelated slot.
theorem rb_distinct_pos (len hd idx tl : Int)
    (hlen : 0 < len)
    (hidx_lo : 0 ≤ idx) (hidx_hi : idx < len)
    (htl_lo : 0 ≤ tl) (htl_hi : tl < len)
    (hne : idx ≠ tl) :
    (idx + len - hd) % len ≠ (tl + len - hd) % len := by
  intro h

  have midx : idx % len = idx := mod_eq_of_lt idx len hidx_lo hidx_hi
  have mtl  : tl  % len = tl  := mod_eq_of_lt tl len  htl_lo  htl_hi

  have hshift :
      Int.ModEq len (idx + (len - hd)) (tl + (len - hd)) := by
    simpa [Int.ModEq, sub_eq_add_neg, add_assoc] using h

  have hcong : Int.ModEq len idx tl :=
    Int.ModEq.add_right_cancel' (len - hd) hshift

  have heq : idx = tl := by
    calc
      idx = idx % len := midx.symm
      _ = tl % len := Int.ModEq.eq hcong
      _ = tl := mtl

  contradiction

-- Advancing hd by 1 decrements the distance (x - hd) % len by exactly 1, when x ≠ hd.
lemma rb_shift_origin
    (len hd x : Int)
    (hlen : 0 < len)
    (hhd_lo : 0 ≤ hd) (hhd_hi : hd < len)
    (hx_lo : 0 ≤ x) (hx_hi : x < len)
    (hx_ne : x ≠ hd) :
    (x - hd) % len = (x - (hd + 1)) % len + 1 := by
  rcases lt_or_gt_of_ne hx_ne with hx_lt | hx_gt

  · -- Case: x < hd.  Both representatives are obtained by adding len.
    have hleft_lo : 0 ≤ x + len - hd := by omega
    have hleft_hi : x + len - hd < len := by omega
    have hright_lo : 0 ≤ x + len - (hd + 1) := by omega
    have hright_hi : x + len - (hd + 1) < len := by omega

    have hleft :
        (x - hd) % len = x + len - hd := by
      calc
        (x - hd) % len
            = ((x - hd) + len) % len := by
                exact (Int.add_emod_right (x - hd) len).symm
        _   = (x + len - hd) % len := by ring_nf
        _   = x + len - hd := by
                exact Int.emod_eq_of_lt hleft_lo hleft_hi

    have hright :
        (x - (hd + 1)) % len = x + len - (hd + 1) := by
      calc
        (x - (hd + 1)) % len
            = ((x - (hd + 1)) + len) % len := by
                exact (Int.add_emod_right (x - (hd + 1)) len).symm
        _   = (x + len - (hd + 1)) % len := by ring_nf
        _   = x + len - (hd + 1) := by
                exact Int.emod_eq_of_lt hright_lo hright_hi

    rw [hleft, hright]
    omega

  · -- Case: hd < x.  Both representatives are already in range.
    have hleft_lo : 0 ≤ x - hd := by omega
    have hleft_hi : x - hd < len := by omega
    have hright_lo : 0 ≤ x - (hd + 1) := by omega
    have hright_hi : x - (hd + 1) < len := by omega

    rw [
      Int.emod_eq_of_lt hleft_lo hleft_hi,
      Int.emod_eq_of_lt hright_lo hright_hi
    ]
    omega

-- Same as rb_shift_origin but for the (x + len - hd) % len form used in rb_idx_valid.
lemma rb_shift_origin_add_len
    (len hd x : Int)
    (hlen : 0 < len)
    (hhd_lo : 0 ≤ hd) (hhd_hi : hd < len)
    (hx_lo : 0 ≤ x) (hx_hi : x < len)
    (hx_ne : x ≠ hd) :
    (x + len - hd) % len =
      (x + len - (hd + 1)) % len + 1 := by
  have hbase :=
    rb_shift_origin len hd x hlen hhd_lo hhd_hi hx_lo hx_hi hx_ne

  have hleft :
      (x + len - hd) % len = (x - hd) % len := by
    calc
      (x + len - hd) % len
          = ((x - hd) + len) % len := by ring_nf
      _   = (x - hd) % len := by
              exact Int.add_emod_right (x - hd) len

  have hright :
      (x + len - (hd + 1)) % len = (x - (hd + 1)) % len := by
    calc
      (x + len - (hd + 1)) % len
          = ((x - (hd + 1)) + len) % len := by ring_nf
      _   = (x - (hd + 1)) % len := by
              exact Int.add_emod_right (x - (hd + 1)) len

  rw [hleft, hbase, ← hright]
