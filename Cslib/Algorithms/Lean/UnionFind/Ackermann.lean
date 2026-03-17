/-
Copyright (c) 2026 CSLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CSLib Contributors
-/

module

public import Cslib.Init
public import Mathlib.Computability.Ackermann

/-!
# Inverse Ackermann Function

Defines the inverse Ackermann function and a two-argument variant
used in the Tarjan potential function for union-find amortized
analysis.

The forward Ackermann function `ack` and its properties are imported
from `Mathlib.Computability.Ackermann`.

## Main Definitions

- `invAck n`: The inverse Ackermann function, `min i` such that
  `ack i 1 ≥ n`.
- `invAck₂ r n`: Two-argument variant, `min k` such that
  `ack k r ≥ n`. Used in the Tarjan potential.

## References

- [Tarjan, 1975] *Efficiency of a Good But Not Linear Set Union
  Algorithm*
- [Charguéraud & Pottier, 2015] *Verifying the Correctness and
  Amortized Complexity of a Union-Find Implementation in Separation
  Logic with Time Credits*
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.UnionFind

/-- The two-argument inverse Ackermann function.
`invAck₂ r n` is the smallest `k` such that `ack k r ≥ n`.
When `ack 0 r = r + 1 ≥ n`, this returns 0. -/
def invAck₂ (r n : ℕ) : ℕ :=
  go r n 0
where
  /-- Search for smallest `k ≥ i` with `ack k r ≥ n`. -/
  go (r n i : ℕ) : ℕ :=
    if ack i r ≥ n then i
    else go r n (i + 1)
  termination_by n - ack i r
  decreasing_by
    simp only [not_le] at *
    have : ack i r < ack (i + 1) r :=
      ack_strictMono_left r (by omega)
    omega

/-- The inverse Ackermann function.
`invAck n` is the smallest `i` such that `ack i 1 ≥ n`. -/
def invAck (n : ℕ) : ℕ := invAck₂ 1 n

private theorem invAck₂.go_unfold (r n i : ℕ) :
    invAck₂.go r n i =
      if ack i r ≥ n then i
      else invAck₂.go r n (i + 1) := by
  rw [invAck₂.go]

/-- `invAck₂.go` satisfies its specification: result has
`ack result r ≥ n`. -/
private theorem invAck₂.go_spec (r n i : ℕ) :
    ack (invAck₂.go r n i) r ≥ n := by
  rw [invAck₂.go]
  split
  · assumption
  · have : ack i r < ack (i + 1) r :=
      ack_strictMono_left r (by omega)
    have : ack i r < n := by omega
    exact invAck₂.go_spec r n (i + 1)
termination_by n - ack i r
decreasing_by
  simp only [not_le] at *
  have : ack i r < ack (i + 1) r :=
    ack_strictMono_left r (by omega)
  omega

/-- The defining property: `ack (invAck₂ r n) r ≥ n`. -/
theorem ack_invAck₂_ge (r n : ℕ) :
    ack (invAck₂ r n) r ≥ n := by
  exact invAck₂.go_spec r n 0

/-- `invAck₂.go` returns a value ≤ `k` when `ack k r ≥ n` and
`i ≤ k`. -/
private theorem invAck₂.go_le {k r n i : ℕ}
    (hk : ack k r ≥ n) (hi : i ≤ k) :
    invAck₂.go r n i ≤ k := by
  rw [invAck₂.go]
  split
  · exact hi
  · have hlt : ack i r < n := by omega
    have : i < k := by
      by_contra h
      push_neg at h
      have : k ≤ i := h
      have := ack_le_ack this (le_refl r)
      omega
    exact invAck₂.go_le hk (by omega)
termination_by n - ack i r
decreasing_by
  simp only [not_le] at *
  have : ack i r < ack (i + 1) r :=
    ack_strictMono_left r (by omega)
  omega

/-- `invAck₂` returns the *minimum* such `k`. -/
theorem invAck₂_le_of_ack_ge {k r n : ℕ}
    (h : ack k r ≥ n) : invAck₂ r n ≤ k :=
  invAck₂.go_le h (Nat.zero_le _)

@[scoped grind =]
theorem invAck₂_of_le {r n : ℕ} (h : ack 0 r ≥ n) :
    invAck₂ r n = 0 := by
  have h1 := invAck₂_le_of_ack_ge h
  omega

/-- `invAck₂` is monotone in `n`: larger `n` gives larger
(or equal) result. -/
theorem invAck₂_mono_right {r n₁ n₂ : ℕ}
    (h : n₁ ≤ n₂) : invAck₂ r n₁ ≤ invAck₂ r n₂ := by
  apply invAck₂_le_of_ack_ge
  exact Nat.le_trans h (ack_invAck₂_ge r n₂)

/-- `invAck₂` is anti-monotone in the first argument: larger `r`
gives smaller (or equal) result. -/
theorem invAck₂_anti_left {r₁ r₂ n : ℕ}
    (h : r₁ ≤ r₂) : invAck₂ r₂ n ≤ invAck₂ r₁ n := by
  apply invAck₂_le_of_ack_ge
  exact Nat.le_trans (ack_invAck₂_ge r₁ n)
    (ack_le_ack (le_refl _) h)

/-- `invAck₂ r n ≤ invAck n` when `r ≥ 1`. -/
theorem invAck₂_le_invAck {r n : ℕ} (hr : 1 ≤ r) :
    invAck₂ r n ≤ invAck n :=
  invAck₂_anti_left hr

/-- The defining property of `invAck`: `ack (invAck n) 1 ≥ n`. -/
theorem ack_invAck_ge (n : ℕ) : ack (invAck n) 1 ≥ n :=
  ack_invAck₂_ge 1 n

/-- `invAck` is monotone. -/
theorem invAck_mono {n₁ n₂ : ℕ} (h : n₁ ≤ n₂) :
    invAck n₁ ≤ invAck n₂ :=
  invAck₂_mono_right h

/-! ### Iterated Ackermann -/

/-- `ackIter k i r` is `ack(k, -)` applied `i` times to `r`.
`ackIter k 0 r = r` and `ackIter k (i+1) r = ack k (ackIter k i r)`. -/
def ackIter (k i r : ℕ) : ℕ :=
  match i with
  | 0 => r
  | i + 1 => ack k (ackIter k i r)

@[simp] theorem ackIter_zero (k r : ℕ) :
    ackIter k 0 r = r := rfl

@[simp] theorem ackIter_succ (k i r : ℕ) :
    ackIter k (i + 1) r = ack k (ackIter k i r) := rfl

/-- `ackIter` is monotone in `i`. -/
theorem ackIter_mono_right {k i₁ i₂ r : ℕ}
    (h : i₁ ≤ i₂) :
    ackIter k i₁ r ≤ ackIter k i₂ r := by
  induction h with
  | refl => exact Nat.le_refl _
  | step h ih =>
    simp only [ackIter_succ]
    exact Nat.le_trans ih (Nat.le_of_lt
      (lt_ack_right _ _))

/-- `ackIter k 1 r = ack k r`. -/
@[simp] theorem ackIter_one (k r : ℕ) :
    ackIter k 1 r = ack k r := rfl

/-- `ackIter` is strictly monotone in `i` when `i ≥ 1`. -/
theorem ackIter_strictMono_right {k r : ℕ}
    {i₁ i₂ : ℕ} (h : i₁ < i₂) :
    ackIter k i₁ r < ackIter k i₂ r := by
  induction i₂ with
  | zero => omega
  | succ i₂ ih =>
    simp only [ackIter_succ]
    if h1 : i₁ < i₂ then
      exact Nat.lt_trans (ih h1)
        (lt_ack_right _ _)
    else
      have : i₁ = i₂ := by omega
      subst this
      exact lt_ack_right _ _

/-- The max iterations at level k before exceeding n.
`iterCount k r n` = max i such that `ackIter k i r ≤ n`.
Equivalently, the count of times we can apply `ack k`
starting from r before exceeding n. -/
def iterCount (k r n : ℕ) : ℕ :=
  if ack k r > n then 0
  else 1 + iterCount k (ack k r) n
termination_by n - r
decreasing_by
  simp only [not_lt] at *
  have : r < ack k r := lt_ack_right k r
  omega

/-- Shifting the base: ackIter with base ack(k,r) equals
ackIter with one more iteration from base r. -/
theorem ackIter_shift (k i r : ℕ) :
    ackIter k i (ack k r) = ackIter k (i + 1) r := by
  induction i with
  | zero => simp [ackIter]
  | succ i ih => simp [ackIter, ih]

/-- ackIter(k, iterCount(k,r,n), r) ≤ n when r ≤ n. -/
theorem ackIter_iterCount_le (k r n : ℕ)
    (hr : r ≤ n) :
    ackIter k (iterCount k r n) r ≤ n := by
  rw [iterCount]
  split
  · simp; exact hr
  · rename_i h; push_neg at h
    show ackIter k (1 + iterCount k (ack k r) n) r ≤ n
    rw [show 1 + iterCount k (ack k r) n =
      iterCount k (ack k r) n + 1 from by omega,
      ← ackIter_shift]
    exact ackIter_iterCount_le k (ack k r) n h
termination_by n - r
decreasing_by
  simp_all only [not_lt]
  have := lt_ack_right k r; omega

/-- ackIter(k, iterCount(k,r,n)+1, r) > n. -/
theorem ackIter_iterCount_gt (k r n : ℕ) :
    ackIter k (iterCount k r n + 1) r > n := by
  rw [iterCount]
  split
  · simp [ackIter]; omega
  · rename_i h; push_neg at h
    show ackIter k (1 + iterCount k (ack k r) n + 1)
      r > n
    rw [show 1 + iterCount k (ack k r) n + 1 =
      (iterCount k (ack k r) n + 1) + 1 from by omega,
      ← ackIter_shift]
    exact ackIter_iterCount_gt k (ack k r) n
termination_by n - r
decreasing_by
  simp_all only [not_lt]
  have := lt_ack_right k r; omega

/-- `ack(invAck₂(r, n) - 1, r) ≤ n - 1` when invAck₂ > 0.
Equivalently, the level below invAck₂ does NOT reach n. -/
theorem ack_pred_invAck₂_lt {r n : ℕ}
    (h : invAck₂ r n > 0) :
    ack (invAck₂ r n - 1) r < n := by
  by_contra hge
  push_neg at hge
  have := invAck₂_le_of_ack_ge (by omega : ack (invAck₂ r n - 1) r ≥ n)
  omega

/-- `iterCount k r n ≤ n - r`. -/
theorem iterCount_le_sub (k r n : ℕ) :
    iterCount k r n ≤ n - r := by
  rw [iterCount]
  split
  · omega
  · rename_i h; push_neg at h
    have h1 : r < ack k r := lt_ack_right k r
    have ih := iterCount_le_sub k (ack k r) n
    omega
termination_by n - r
decreasing_by
  simp only [not_lt] at *
  have := lt_ack_right k r; omega

/-- `iterCount` is monotone in the bound: larger `n`
allows more iterations. -/
theorem iterCount_mono_right (k r : ℕ)
    {n₁ n₂ : ℕ} (h : n₁ ≤ n₂) :
    iterCount k r n₁ ≤ iterCount k r n₂ := by
  unfold iterCount
  split
  · exact Nat.zero_le _
  · rename_i h1; push_neg at h1
    have h2 : ¬(ack k r > n₂) := by omega
    simp only [if_neg h2]
    exact Nat.add_le_add_left
      (iterCount_mono_right k (ack k r) h) 1
termination_by n₁ - r
decreasing_by
  simp only [not_lt] at *
  have := lt_ack_right k r; omega

/-- `iterCount k r n ≤ n`. -/
theorem iterCount_le (k r n : ℕ) :
    iterCount k r n ≤ n :=
  Nat.le_trans (iterCount_le_sub k r n)
    (Nat.sub_le n r)

end Cslib.Algorithms.Lean.UnionFind

end -- section
