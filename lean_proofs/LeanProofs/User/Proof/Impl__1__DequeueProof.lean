import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.Impl__1__Dequeue
import Tactics
import Mathlib
import Lemmas
import ModLemmas
import RbLemmas
open Classical
set_option linter.unusedVariables false


namespace F

open Impl1DequeueKVarSolutions


lemma rb_neg_one_mod (len : Int) (hlen : 0 < len) :
    (-1 : Int) % len = len - 1 := by
  have hcanon : (len - 1) % len = len - 1 := by
    apply Int.emod_eq_of_lt
    · omega
    · omega

  calc
    (-1 : Int) % len
        = (len - 1 + (-1) * len) % len := by
            congr 1
            ring
    _   = (len - 1) % len := by
            rw [Int.add_mul_emod_self_right]
    _   = len - 1 := hcanon

-- If the buffer invariant holds and hd ≠ tl, then hd is initialized.
theorem rb_hd_is_init (ring : FluxSlice) (hd tl : Int)
    (hlen : 0 < ring.len)
    (hhd_lo : 0 ≤ hd) (hhd_hi : hd < ring.len)
    (htl_lo : 0 ≤ tl) (htl_hi : tl < ring.len)
    (hne : hd ≠ tl)
    (hvalid : rb_valid_iff_init ring hd tl) :
    SmtMap_select ring.inits hd :=
  (hvalid hd hhd_hi).mpr (rb_hd_valid ring.len hd tl hlen hhd_lo hhd_hi htl_lo htl_hi hne)

-- After advancing the head, the old hd slot is no longer in the valid window.
-- Key: (old_hd + len - new_hd) % len = len - 1, which can never be < anything < len.
theorem rb_dequeue_old_hd_invalid (len hd tl : Int)
    (hlen : 0 < len) (hhd_lo : 0 ≤ hd) (hhd_hi : hd < len) :
    ¬ rb_idx_valid len ((hd + 1) % len) tl hd := by
    simp_all [rb_idx_valid, Int.reduceNeg, rb_neg_one_mod, mod_lt]

theorem rb_dequeue_preserves_valid_bounded (len hd tl idx : Int)
    (hlen : 0 < len)
    (hhd_lo : 0 ≤ hd) (hhd_hi : hd < len)
    (htl_lo : 0 ≤ tl) (htl_hi : tl < len)
    (hne_tl : hd ≠ tl)
    (hne_idx : idx ≠ hd) :
    rb_idx_valid len ((hd + 1) % len) tl idx ↔
      rb_idx_valid len hd tl idx := by
  unfold rb_idx_valid
  constructor

  · intro h
    rcases h with ⟨hidx_lo, hidx_hi, hineq⟩

    have hidx_shift :
        (idx + len - hd) % len =
          (idx + len - (hd + 1)) % len + 1 := by
      exact rb_shift_origin_add_len
        len hd idx hlen hhd_lo hhd_hi hidx_lo hidx_hi hne_idx

    have htl_ne : tl ≠ hd := by
      intro h
      exact hne_tl h.symm

    have htl_shift :
        (tl - hd + len) % len =
          (tl - (hd + 1) + len) % len + 1 := by
      -- Same content as rb_shift_origin, but with `+ len` on both sides.
      have hbase :=
        rb_shift_origin_add_len
          len hd tl hlen hhd_lo hhd_hi htl_lo htl_hi htl_ne
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hbase

    refine ⟨hidx_lo, hidx_hi, ?_⟩

    calc
      (idx + len - hd) % len
          = (idx + len - (hd + 1)) % len + 1 := hidx_shift
      _   < (tl - (hd + 1) + len) % len + 1 := by
              simpa [add_comm] using add_lt_add_right hineq (1 : Int)
      _   = (tl - hd + len) % len := htl_shift.symm

  · intro h
    rcases h with ⟨hidx_lo, hidx_hi, hineq⟩

    have hidx_shift :
        (idx + len - hd) % len =
          (idx + len - (hd + 1)) % len + 1 := by
      exact rb_shift_origin_add_len
        len hd idx hlen hhd_lo hhd_hi hidx_lo hidx_hi hne_idx

    have htl_ne : tl ≠ hd := by
      intro h
      exact hne_tl h.symm

    have htl_shift :
        (tl - hd + len) % len =
          (tl - (hd + 1) + len) % len + 1 := by
      have hbase :=
        rb_shift_origin_add_len
          len hd tl hlen hhd_lo hhd_hi htl_lo htl_hi htl_ne
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hbase

    refine ⟨hidx_lo, hidx_hi, ?_⟩

    have hineq' :
        (idx + len - (hd + 1)) % len + 1
          <
        (tl - (hd + 1) + len) % len + 1 := by
      simpa [hidx_shift, htl_shift] using hineq
    aesop

theorem rb_dequeue_preserves_valid_iff_init
    (ring : FluxSlice) (hd tl : Int)
    (hvalid : rb_valid_iff_init ring hd tl)
    (hlen : 0 < ring.len)
    (hhd_lo : 0 ≤ hd) (hhd_hi : hd < ring.len)
    (htl_lo : 0 ≤ tl) (htl_hi : tl < ring.len)
    (hne_tl : hd ≠ tl) :
    rb_valid_iff_init
      { len := ring.len, inits := SmtMap_store ring.inits hd False }
      ((hd + 1) % ring.len)
      tl := by
  intro idx hidx_hi

  have hidx_hi_ring : idx < ring.len := by
    simpa using hidx_hi

  by_cases hidx_hd : idx = hd

  · -- idx is exactly the old head slot.
    subst idx

    have h_old_hd_invalid :
        ¬ rb_idx_valid
            ring.len
            ((hd + 1) % ring.len)
            tl
            hd := by
      exact rb_dequeue_old_hd_invalid
        ring.len hd tl
        hlen hhd_lo hhd_hi

    constructor

    · intro hsel
      have hfalse : False := by
        simpa using hsel
      exact False.elim hfalse

    · intro hnew_valid
      exact False.elim (h_old_hd_invalid hnew_valid)

  · -- idx is not hd, so the store does not affect this key.
    have hstore :
    SmtMap_select (SmtMap_store ring.inits hd False) idx =
      SmtMap_select ring.inits idx := by simp [hidx_hd]

    rw [hstore]

    have h_old_iff :
        SmtMap_select ring.inits idx ↔
          rb_idx_valid ring.len hd tl idx := by
      exact hvalid idx hidx_hi_ring

    constructor

    · intro hsel

      have h_old_valid :
          rb_idx_valid ring.len hd tl idx :=
        h_old_iff.mp hsel

      have hidx_lo : 0 ≤ idx := by
        exact h_old_valid.1

      have hidx_hi' : idx < ring.len := by
        exact h_old_valid.2.1

      have h_pres :
    rb_idx_valid ring.len ((hd + 1) % ring.len) tl idx ↔
      rb_idx_valid ring.len hd tl idx := by exact rb_dequeue_preserves_valid_bounded ring.len hd tl idx hlen hhd_lo hhd_hi htl_lo htl_hi hne_tl hidx_hd
      exact h_pres.mpr h_old_valid

    · intro h_new_valid

      have h_new_valid' :
          rb_idx_valid ring.len ((hd + 1) % ring.len) tl idx := by
        simpa using h_new_valid

      have hidx_lo : 0 ≤ idx := by
        exact h_new_valid'.1

      have hidx_hi' : idx < ring.len := by
        exact h_new_valid'.2.1

      have h_pres :
        rb_idx_valid ring.len ((hd + 1) % ring.len) tl idx ↔
          rb_idx_valid ring.len hd tl idx := by
        exact rb_dequeue_preserves_valid_bounded ring.len hd tl idx hlen hhd_lo hhd_hi htl_lo htl_hi hne_tl hidx_hd

      have h_old_valid :
          rb_idx_valid ring.len hd tl idx :=
        h_pres.mp h_new_valid'

      exact h_old_iff.mpr h_old_valid

def Impl__1__Dequeue_proof : Impl__1__Dequeue := by
  unfold Impl__1__Dequeue
  exists k0; exists k2; exists k2;
  repeat (any_goals (first | (intro) | apply And.intro | grind))
  simp_all
  . apply rb_hd_is_init <;> assumption
  . unfold k0; grind
  . unfold k2; grind
  . unfold k0; grind
  . unfold k2; grind
  . unfold k0; grind
  . exact mod_lt _ _ (by assumption)
  . rename_i s hvalid hne hlen hhd_hi hhd_lo htl_hi htl_lo val hk hlen_nonneg hlen_ne idx hidx_hi
    have hnew :
        rb_valid_iff_init
          { len := s.ring.len, inits := SmtMap_store s.ring.inits s.hd False }
          ((s.hd + 1) % s.ring.len)
          s.tl := by
      exact rb_dequeue_preserves_valid_iff_init
        s.ring
        s.hd
        s.tl
        hvalid
        hlen
        hhd_lo
        hhd_hi
        htl_lo
        htl_hi
        hne
    exact hnew idx hidx_hi
  . unfold k2; grind

end F
