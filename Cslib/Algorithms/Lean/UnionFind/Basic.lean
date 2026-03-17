/-
Copyright (c) 2026 CSLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CSLib Contributors
-/

module

public import Cslib.Init
public import Batteries.Data.UnionFind
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Finset.Card

/-!
# Union-Find Bridge: Path Length and Rank Bounds

Defines `pathLength` for `Batteries.UnionFind` and proves the per-call
`O(log n)` worst-case bound for find operations.

## Main Definitions

- `pathLength self x`: Number of edges from node `x` to its root.
- `descendants self x`: Set of nodes whose root is `x`.
- `findState self x`: Union-find after path compression on `x`.
- `RankBound self`: Predicate asserting the classical 2^r rank-size
  bound holds for all roots. This is an invariant maintained by the
  standard union-find operations (`empty`, `push`, `union`) but
  cannot be derived from the `UnionFind` structure alone, since one
  can hand-craft arrays satisfying `parentD_lt` and `rankD_lt` that
  violate the bound (e.g. a chain 0->1->2 with ranks 0,1,2 has
  only 3 descendants at the rank-2 root, but 2^2=4).

## Main Results

- `pathLength_le_rank_root`: Path length ≤ rank of root.
- `two_pow_rank_le_descendants_card`: Root of rank `r` has ≥ `2^r`
  descendants (assuming `RankBound`).
- `rank_le_log_size`: `self.rank x ≤ Nat.log 2 self.size`
  (assuming `RankBound`).
- `pathLength_le_log_size`: Per-call `O(log n)` worst-case bound
  (assuming `RankBound`).

## References

- [Tarjan, 1975] *Efficiency of a Good But Not Linear Set Union
  Algorithm*
- [Cormen et al.] *Introduction to Algorithms*, Chapter 21
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.UnionFind

open Batteries in
/-- Number of edges from node `x` to its root.
Returns 0 if `x` is out of bounds or is a root. -/
def pathLength (self : UnionFind) (x : ℕ) : ℕ :=
  if h : self.parent x = x then 0
  else
    have := Nat.sub_lt_sub_left
      (self.lt_rankMax x) (self.rank_lt h)
    1 + pathLength self (self.parent x)
termination_by self.rankMax - self.rank x

open Batteries in
/-- The set of nodes whose root is `x`. -/
def descendants (self : UnionFind) (x : ℕ) : Finset ℕ :=
  (Finset.range self.size).filter fun j =>
    self.rootD j = x

open Batteries in
/-- Union-find state after path compression for a find on `x`. -/
def findState (self : UnionFind) (x : ℕ) : UnionFind :=
  (self.findD x).1

open Batteries in
/-- Path length + rank of node ≤ rank of root. -/
private theorem pathLength_add_rank_le
    (self : UnionFind) (x : ℕ) :
    pathLength self x + self.rank x ≤
      self.rank (self.rootD x) := by
  if h : self.parent x = x then
    have : pathLength self x = 0 := by
      rw [pathLength, dif_pos h]
    rw [this, Nat.zero_add]
    exact UnionFind.le_rank_root
  else
    have hdec := Nat.sub_lt_sub_left
      (self.lt_rankMax x) (self.rank_lt h)
    have hpl : pathLength self x =
        1 + pathLength self (self.parent x) := by
      rw [pathLength, dif_neg h]
    have ih := pathLength_add_rank_le self
      (self.parent x)
    rw [UnionFind.rootD_parent] at ih
    have hlt := self.rank_lt h
    rw [hpl]
    -- Need: 1 + pathLength(p) + rank(x) ≤ rank(root)
    -- From: ih: pathLength(p) + rank(p) ≤ rank(root)
    --       hlt: rank(x) < rank(p)
    -- Strategy: show ≤ pathLength(p) + rank(p), then
    --           use ih
    suffices h : 1 + pathLength self (self.parent x)
        + self.rank x ≤ pathLength self (self.parent x)
        + self.rank (self.parent x) from
      Nat.le_trans h ih
    -- Now generalize for omega
    generalize self.rank x = rx at hlt ⊢
    generalize pathLength self (self.parent x) = pl
      at ⊢
    generalize self.rank (self.parent x) = rp
      at hlt ⊢
    omega
termination_by self.rankMax - self.rank x

open Batteries in
/-- Path length is bounded by the rank of the root. -/
theorem pathLength_le_rank_root (self : UnionFind)
    (x : ℕ) :
    pathLength self x ≤ self.rank (self.rootD x) :=
  Nat.le_trans (Nat.le_add_right _ _)
    (pathLength_add_rank_le self x)

open Batteries in
/-- A root node is in its own descendants. -/
theorem root_mem_descendants (self : UnionFind) (x : ℕ)
    (hx : x < self.size) (hroot : self.rootD x = x) :
    x ∈ descendants self x := by
  simp only [descendants, Finset.mem_filter,
    Finset.mem_range]
  exact ⟨hx, hroot⟩

open Batteries in
/-- Every root has at least one descendant (itself). -/
theorem one_le_descendants_card (self : UnionFind)
    (x : ℕ) (hx : x < self.size)
    (hroot : self.rootD x = x) :
    1 ≤ (descendants self x).card := by
  rw [Finset.one_le_card]
  exact ⟨x, root_mem_descendants self x hx hroot⟩

open Batteries in
/-- The classical rank-size invariant: every root of rank `r`
has at least `2^r` descendants. This property is maintained by
the standard union-find operations but cannot be derived from
the `UnionFind` structure alone -- a hand-crafted array can
satisfy `parentD_lt` and `rankD_lt` while violating this bound
(e.g. a chain with ranks 0,1,2 has 3 nodes but 2^2=4). -/
def RankBound (self : UnionFind) : Prop :=
  ∀ x, x < self.size → self.rootD x = x →
    2 ^ self.rank x ≤ (descendants self x).card

open Batteries in
/-- The empty union-find satisfies `RankBound`. -/
theorem rankBound_empty : RankBound UnionFind.empty := by
  intro x hx
  simp [UnionFind.size] at hx

open Batteries in
/-- Pushing a fresh node preserves `RankBound`. -/
theorem rankBound_push {self : UnionFind}
    (h : RankBound self) : RankBound self.push := by
  intro x hx hroot
  simp only [UnionFind.size] at hx
  rw [UnionFind.rank_push]
  rw [UnionFind.root_push] at hroot
  -- Case split: is x the newly added node or an old one?
  by_cases hlt : x < self.size
  · -- Old node: descendants may include the new node
    have hold := h x hlt hroot
    -- The old descendants are a subset of the new ones
    suffices hsub : descendants self x ⊆
        descendants self.push x from
      Nat.le_trans hold (Finset.card_le_card hsub)
    intro j hj
    simp only [descendants, Finset.mem_filter,
      Finset.mem_range] at hj ⊢
    constructor
    · show j < self.push.size
      simp only [UnionFind.size, UnionFind.arr_push,
        Array.size_push]
      exact Nat.lt_succ_of_lt hj.1
    · rw [UnionFind.root_push]; exact hj.2
  · -- New node x = self.size: rank is 0, need card ≥ 1
    have hxeq : x = self.size := by
      have : self.size ≤ x := Nat.le_of_not_lt hlt
      have : x < self.size + 1 := by
        simp only [UnionFind.arr_push,
          Array.size_push] at hx
        exact hx
      omega
    subst hxeq
    -- After rw [rank_push], goal has self.rank self.size
    -- which is rankD for out-of-bounds index = 0
    have hrank0 : self.rank self.size = 0 := by
      simp [UnionFind.rank, UnionFind.rankD]
    rw [hrank0, Nat.pow_zero]
    have hroot' : self.push.rootD self.size =
        self.size := by
      rw [UnionFind.root_push]; exact hroot
    exact one_le_descendants_card self.push
      self.size hx hroot'

open Batteries in
/-- A node of rank `r` has at least `2^r` descendants.
Classical rank-size bound for union-by-rank.

This requires the `RankBound` invariant as a hypothesis because
the `UnionFind` structure's built-in invariants (`parentD_lt` and
`rankD_lt`) are insufficient -- see the module docstring. -/
theorem two_pow_rank_le_descendants_card
    (self : UnionFind) (x : ℕ)
    (hx : x < self.size)
    (hroot : self.rootD x = x)
    (hrb : RankBound self) :
    2 ^ self.rank x ≤ (descendants self x).card :=
  hrb x hx hroot

open Batteries in
/-- Rank of any node is at most `log₂` of the structure size. -/
theorem rank_le_log_size (self : UnionFind) (x : ℕ)
    (hx : x < self.size) (hrb : RankBound self) :
    self.rank x ≤ Nat.log 2 self.size := by
  have hroot : self.rootD x < self.size :=
    UnionFind.rootD_lt.mpr hx
  have hle := UnionFind.le_rank_root (self := self)
    (x := x)
  have hcard := two_pow_rank_le_descendants_card self
    (self.rootD x) hroot
    (UnionFind.rootD_eq_self.mpr
      (UnionFind.parent_rootD ..))
    hrb
  have hdesc : (descendants self (self.rootD x)).card
      ≤ self.size := by
    calc (descendants self (self.rootD x)).card
        ≤ (Finset.range self.size).card :=
          Finset.card_le_card
            (Finset.filter_subset _ _)
      _ = self.size := Finset.card_range self.size
  have h2r := Nat.le_trans hcard hdesc
  calc self.rank x
      ≤ self.rank (self.rootD x) := hle
    _ ≤ Nat.log 2 self.size :=
        Nat.le_log_of_pow_le (by omega) h2r

open Batteries in
/-- Per-call worst-case bound: path length ≤ `log₂(n)`. -/
theorem pathLength_le_log_size (self : UnionFind)
    (x : ℕ) (hrb : RankBound self) :
    pathLength self x ≤ Nat.log 2 self.size := by
  if hx : x < self.size then
    calc pathLength self x
        ≤ self.rank (self.rootD x) :=
          pathLength_le_rank_root self x
      _ ≤ Nat.log 2 self.size := by
          have := UnionFind.rootD_lt.mpr hx
          exact rank_le_log_size self
            (self.rootD x) this hrb
  else
    rw [pathLength, dif_pos]
    · exact Nat.zero_le _
    · exact UnionFind.parentD_of_not_lt hx

open Batteries in
/-- `findState` preserves the equivalence relation. -/
theorem findState_equiv (self : UnionFind) (x a b : ℕ) :
    UnionFind.Equiv (findState self x) a b ↔
    UnionFind.Equiv self a b := by
  simp only [findState, UnionFind.findD]
  split
  · exact UnionFind.equiv_find
  · exact Iff.rfl

open Batteries in
/-- `findState` preserves the size. -/
theorem findState_size (self : UnionFind) (x : ℕ) :
    (findState self x).size = self.size := by
  simp only [findState, UnionFind.findD]
  split
  · exact UnionFind.find_size ..
  · rfl

end Cslib.Algorithms.Lean.UnionFind

end -- section
