import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.Impl__1__Enqueue
import Lemmas
import Tactics
import Mathlib
open Classical
set_option linter.unusedVariables false


namespace F

theorem mod_non_neg (a b : Int) : 0 < b -> 0 <= (a % b) := by
  intro h
  exact Int.emod_nonneg a (by omega)

theorem mod_lt (a b : Int) : 0 < b -> (a % b) < b := by
  intro h
  exact Int.emod_lt_of_pos a h


theorem rb_mod_self (len idx : Int) (hlo : 0 ≤ idx) (hhi : idx < len) :
    idx % len = idx :=
  Int.emod_eq_of_lt hlo hhi

theorem rb_distinct_pos (len hd idx tl : Int)
    (hlen : 0 < len)
    (hidx_lo : 0 ≤ idx) (hidx_hi : idx < len)
    (htl_lo : 0 ≤ tl) (htl_hi : tl < len)
    (hne : idx ≠ tl) :
    (idx + len - hd) % len ≠ (tl + len - hd) % len := by
  intro h

  have midx : idx % len = idx := rb_mod_self len idx hidx_lo hidx_hi
  have mtl  : tl  % len = tl  := rb_mod_self len tl  htl_lo  htl_hi

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



-- After enqueue, the occupied count increases by exactly one.
-- Requires the buffer is not full (hd ≠ (tl+1)%len).
theorem rb_enqueue_count (len hd tl : Int)
    (hlen : 0 < len) (hhd_lo : 0 ≤ hd) (hhd_hi : hd < len) -- 0 <= hd < len
    (htl_lo : 0 ≤ tl) (htl_hi : tl < len) -- 0 <= tl < len
    (hnot_full : hd ≠ (tl + 1) % len) : -- hd != rb_next(tail)
    (tl - hd + 1) % len = (tl - hd + len) % len + 1 := by --
    -- step 1: reduce (tl-hd + len) % len into (tl-hd) % len.
    have h1: (tl - hd + len) % len = (tl - hd) % len := by aesop
    simp [h1]
    by_cases hle: hd <= tl
    . sorry
    . have hlt : tl < hd := by omega
      have htl1_mod : (tl + 1) % len = tl + 1 := by exact Int.emod_eq_of_lt (by omega) (by omega)
      have hy0 : 0 ≤ tl - hd + len := by omega
      have hylt : tl - hd + len < len := by omega
      have hmod : (tl - hd) % len = tl - hd + len := by calc
        (tl - hd) % len
            = (tl - hd + len) % len := h1.symm
        _ = tl - hd + len := Int.emod_eq_of_lt hy0 hylt
      have hz0 : 0 ≤ tl - hd + 1 + len := by omega
      have hzlt : tl - hd + 1 + len < len := by omega
      have hleft : (tl - hd + 1) % len = tl - hd + 1 + len := by calc
        (tl - hd + 1) % len
            = (tl - hd + 1 + len) % len := by
                exact Int.emod_eq_add_self_emod
        _ = tl - hd + 1 + len := Int.emod_eq_of_lt hz0 hzlt
      rw [hleft, hmod]
      omega


-- Not-full means advancing tl does not wrap onto hd,
-- so the valid interval length grows by exactly one.
lemma rb_enqueue_bound_grows
    (len hd tl : Int)
    (hlen : 0 < len)
    (hhd_lo : 0 ≤ hd) (hhd_hi : hd < len)
    (htl_lo : 0 ≤ tl) (htl_hi : tl < len)
    (hnot_full : hd ≠ (tl + 1) % len) :
    ((tl + 1) - hd) % len =
      (tl - hd + len) % len + 1 := by
  have hec :
      (tl - hd + 1) % len =
        (tl - hd + len) % len + 1 := by
    exact rb_enqueue_count len hd tl
      hlen hhd_lo hhd_hi htl_lo htl_hi hnot_full

  calc
    ((tl + 1) - hd) % len
        = (tl - hd + 1) % len := by ring_nf
    _   = (tl - hd + len) % len + 1 := hec


def Impl__1__Enqueue_proof : Impl__1__Enqueue := by
  unfold Impl__1__Enqueue
  repeat (any_goals (first | (intro) | apply And.intro | grind))
  · apply Int.emod_lt_of_pos
    omega
  · constructor <;> simp_all
    · intro h
      rename_i s₀ _ hvalid idx hnot_full hlen hhd_hi hge_hd htl_hi hge_tl _ _ hidx_lt
      have hec := rb_enqueue_count s₀.ring.len s₀.hd s₀.tl hlen hge_hd hhd_hi hge_tl htl_hi hnot_full
      -- hec : (tl - hd + 1) % len = (tl - hd + len) % len + 1
      simp_all
      unfold rb_idx_valid
      zap
      simp_all [Int.add_emod_right, Int.emod_sub_emod]
      sorry

    . sorry
    --
      -- have h1:(idx✝ + s₀✝.ring.len - s₀✝.hd) by sorry
    -- · intro hval_new hidx_ne
    --   apply (hvalid idx hidx_lt).mpr    -- goal becomes: < old_count
    --   have hec := rb_enqueue_count s₀.ring.len s₀.hd s₀.tl hlen hge_hd hhd_hi hge_tl htl_hi hnot_full
    --   have hdp := rb_distinct_pos s₀.ring.len s₀.hd idx s₀.tl hlen hidx_lo hidx_lt hge_tl htl_hi hidx_ne
    --   -- hval_new + hec : (idx + len - hd) % len < old_count + 1
    --   -- hdp            : (idx + len - hd) % len ≠ old_count
    --   omega                              -- ≤ old_count and ≠ old_count → < old_count


end F
