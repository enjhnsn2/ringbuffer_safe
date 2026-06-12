import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.Impl__1__Dequeue
import Tactics
import Mathlib
import Lemmas
open Classical
set_option linter.unusedVariables false


namespace F

open Impl1DequeueKVarSolutions

-- The tail slot is always empty: tl is never a valid index.
-- (Both sides of rb_idx_valid collapse to the same expression, so it's x < x.)
theorem rb_tl_not_valid (len hd tl : Int) :
    ¬ rb_idx_valid len hd tl tl := by
  grind

theorem mod_lt (a b : Int) : 0 < b -> (a % b) < b := by
  intro h
  exact Int.emod_lt_of_pos a h

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
    simp only [rb_idx_valid]
      -- Step 1: show LHS = len - 1 (maximum possible mod value)
    have hkey : hd + len - (hd + 1) % len = len - 1 + len * ((hd + 1) / len) := by
      linarith [Int.emod_add_mul_ediv (hd + 1) len]
    have hlhs : (hd + len - (hd + 1) % len) % len = len - 1 := by
      rw [hkey]
      -- goal: (len - 1 + len * ((hd + 1) / len)) % len = len - 1
      -- matches (?a + ?b * ?c) % ?b with ?b = len ✓
      rw [Int.add_mul_emod_self_left]
      exact Int.emod_eq_of_lt (by omega) (by omega)
    rw [hlhs]
    -- Step 2: RHS < len, so len - 1 < RHS is impossible
    have hrhs : (tl - (hd + 1) % len + len) % len < len := Int.emod_lt_of_pos _ hlen
    omega

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
