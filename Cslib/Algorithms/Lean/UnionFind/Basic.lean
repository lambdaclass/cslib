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
public import Mathlib.Data.Finset.Union
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

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

open Batteries
/-- Number of edges from node `x` to its root.
Returns 0 if `x` is out of bounds or is a root. -/
def pathLength (self : UnionFind) (x : ℕ) : ℕ :=
  if h : self.parent x = x then 0
  else
    have := Nat.sub_lt_sub_left
      (self.lt_rankMax x) (self.rank_lt h)
    1 + pathLength self (self.parent x)
termination_by self.rankMax - self.rank x


/-- The set of nodes whose root is `x`. -/
def descendants (self : UnionFind) (x : ℕ) : Finset ℕ :=
  (Finset.range self.size).filter fun j =>
    self.rootD j = x


/-- Union-find state after path compression for a find on `x`. -/
def findState (self : UnionFind) (x : ℕ) : UnionFind :=
  (self.findD x).1


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


/-- Path length is bounded by the rank of the root. -/
theorem pathLength_le_rank_root (self : UnionFind)
    (x : ℕ) :
    pathLength self x ≤ self.rank (self.rootD x) :=
  Nat.le_trans (Nat.le_add_right _ _)
    (pathLength_add_rank_le self x)


/-- A root node is in its own descendants. -/
theorem root_mem_descendants (self : UnionFind) (x : ℕ)
    (hx : x < self.size) (hroot : self.rootD x = x) :
    x ∈ descendants self x := by
  simp only [descendants, Finset.mem_filter,
    Finset.mem_range]
  exact ⟨hx, hroot⟩


/-- Every root has at least one descendant (itself). -/
theorem one_le_descendants_card (self : UnionFind)
    (x : ℕ) (hx : x < self.size)
    (hroot : self.rootD x = x) :
    1 ≤ (descendants self x).card := by
  rw [Finset.one_le_card]
  exact ⟨x, root_mem_descendants self x hx hroot⟩


/-- The classical rank-size invariant: every root of rank `r`
has at least `2^r` descendants. This property is maintained by
the standard union-find operations but cannot be derived from
the `UnionFind` structure alone -- a hand-crafted array can
satisfy `parentD_lt` and `rankD_lt` while violating this bound
(e.g. a chain with ranks 0,1,2 has 3 nodes but 2^2=4). -/
def RankBound (self : UnionFind) : Prop :=
  ∀ x, x < self.size → self.rootD x = x →
    2 ^ self.rank x ≤ (descendants self x).card


/-- The empty union-find satisfies `RankBound`. -/
theorem rankBound_empty : RankBound UnionFind.empty := by
  intro x hx
  simp [UnionFind.size] at hx


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


/-- Descendants of distinct roots are disjoint. -/
private theorem descendants_disjoint (self : UnionFind)
    (x y : ℕ) (hne : x ≠ y)
    (_hxr : self.rootD x = x) (_hyr : self.rootD y = y) :
    Disjoint (descendants self x) (descendants self y) := by
  simp only [Finset.disjoint_left, descendants,
    Finset.mem_filter, Finset.mem_range]
  intro j ⟨_, hjx⟩ ⟨_, hjy⟩
  exact hne (hjx.symm.trans hjy)


/-- After link, the new root's descendants contain the old
descendants of both merged roots. -/
private theorem descendants_link_superset
    (self : UnionFind) (x y : Fin self.size)
    (_ : self.parent x = x)
    (yroot : self.parent y = y) (_ : x.1 ≠ y.1)
    (r : Fin self.size) (_ : r = x ∨ r = y)
    (hroot : ∀ i, (self.link x y yroot).rootD i =
      if self.rootD i = x ∨ self.rootD i = y
      then r.1 else self.rootD i) :
    descendants self x ∪ descendants self y ⊆
      descendants (self.link x y yroot) r := by
  intro j hj
  simp only [descendants, Finset.mem_filter,
    Finset.mem_range, Finset.mem_union] at hj ⊢
  have hsize : (self.link x y yroot).size = self.size := by
    change (UnionFind.linkAux self.arr x y).size = _
    exact UnionFind.linkAux_size
  rcases hj with ⟨hjs, hjx⟩ | ⟨hjs, hjy⟩
  · exact ⟨by omega, by rw [hroot]; simp [hjx]⟩
  · exact ⟨by omega, by rw [hroot]; simp [hjy]⟩


/-- Rank of the link result for nodes other than the
two roots follows a predictable pattern. -/
private theorem rank_link_eq (self : UnionFind)
    (x y : Fin self.size)
    (yroot : self.parent y = y) (hxy : x.1 ≠ y.1)
    (i : ℕ) (hix : i ≠ x.1) (hiy : i ≠ y.1) :
    (self.link x y yroot).rank i = self.rank i := by
  change UnionFind.rankD (UnionFind.linkAux self.arr x y) i =
    UnionFind.rankD self.arr i
  simp only [UnionFind.linkAux, show ¬(x.1 = y.1) from hxy,
    ite_false]
  split
  · -- rank y < rank x
    rw [UnionFind.rankD_set, if_neg (Ne.symm hiy)]
  · split
    · -- rank x = rank y
      rw [UnionFind.rankD_set, if_neg (Ne.symm hiy),
        UnionFind.rankD_set, if_neg (Ne.symm hix)]
    · -- rank x < rank y
      rw [UnionFind.rankD_set, if_neg (Ne.symm hix)]


/-- In the y-loser case (rank y < rank x), ranks are
all unchanged after link. -/
private theorem rank_link_y_loser (self : UnionFind)
    (x y : Fin self.size)
    (yroot : self.parent y = y) (hxy : x.1 ≠ y.1)
    (hrank : self.rank y < self.rank x) (i : ℕ) :
    (self.link x y yroot).rank i = self.rank i := by
  change UnionFind.rankD (UnionFind.linkAux self.arr x y) i =
    UnionFind.rankD self.arr i
  have hrank' : self.arr[y.1].rank < self.arr[x.1].rank := by
    simp only [← UnionFind.rankD_eq y.2,
      ← UnionFind.rankD_eq x.2]; exact hrank
  simp only [UnionFind.linkAux, show ¬(x.1 = y.1) from hxy,
    ite_false, hrank', ite_true]
  rw [UnionFind.rankD_set]; split
  · rename_i h; subst h; simp [UnionFind.rankD_eq y.2]
  · rfl


/-- In the x-loser case with equal ranks, y's rank is
bumped by 1, x's rank unchanged. -/
private theorem rank_link_x_loser_eq (self : UnionFind)
    (x y : Fin self.size)
    (yroot : self.parent y = y) (hxy : x.1 ≠ y.1)
    (hrank : self.rank x = self.rank y) :
    (self.link x y yroot).rank y = self.rank y + 1 := by
  change UnionFind.rankD (UnionFind.linkAux self.arr x y) y =
    UnionFind.rankD self.arr y + 1
  have hxeq : self.arr[x.1].rank = self.rank x :=
    (UnionFind.rankD_eq x.2).symm
  have hyeq : self.arr[y.1].rank = self.rank y :=
    (UnionFind.rankD_eq y.2).symm
  simp only [UnionFind.linkAux, show ¬(x.1 = y.1) from hxy,
    ite_false]
  have hrank' : ¬(self.arr[y.1].rank < self.arr[x.1].rank) := by
    rw [hxeq, hyeq]; omega
  have hreq : self.arr[x.1].rank = self.arr[y.1].rank := by
    rw [hxeq, hyeq]; exact hrank
  rw [if_neg hrank']
  rw [if_pos hreq]
  rw [UnionFind.rankD_set, if_pos rfl]
  simp only [UnionFind.rankD_eq y.2]


/-- In the x-loser case with strictly greater rank for y,
y's rank is unchanged. -/
private theorem rank_link_x_loser_lt (self : UnionFind)
    (x y : Fin self.size)
    (yroot : self.parent y = y) (hxy : x.1 ≠ y.1)
    (hrank : self.rank x < self.rank y) :
    (self.link x y yroot).rank y = self.rank y := by
  change UnionFind.rankD (UnionFind.linkAux self.arr x y) y =
    UnionFind.rankD self.arr y
  have hxeq : self.arr[x.1].rank = self.rank x :=
    (UnionFind.rankD_eq x.2).symm
  have hyeq : self.arr[y.1].rank = self.rank y :=
    (UnionFind.rankD_eq y.2).symm
  simp only [UnionFind.linkAux, show ¬(x.1 = y.1) from hxy,
    ite_false]
  have hrank' : ¬(self.arr[y.1].rank < self.arr[x.1].rank) := by
    rw [hxeq, hyeq]; omega
  have hreq : ¬(self.arr[x.1].rank = self.arr[y.1].rank) := by
    rw [hxeq, hyeq]; omega
  simp only [hrank', ite_false, hreq, ite_false, UnionFind.rankD_set]
  rw [if_neg hxy]


/-- Find preserves `RankBound`. -/
theorem rankBound_findState {self : UnionFind}
    (hrb : RankBound self) (x : ℕ) :
    RankBound (findState self x) := by
  if hx : x < self.size then
    have hfs_size : (findState self x).size = self.size := by
      simp only [findState, UnionFind.findD, dif_pos hx]
      exact UnionFind.find_size ..
    intro z hz hzroot
    rw [hfs_size] at hz
    have hfs_rank : ∀ i, (findState self x).rank i =
        self.rank i := fun i => by
      simp only [findState, UnionFind.findD, dif_pos hx]
      exact UnionFind.rankD_findAux
    rw [hfs_rank]
    have hzroot' : self.rootD z = z := by
      simp only [findState, UnionFind.findD, dif_pos hx]
          at hzroot
      rwa [UnionFind.find_root_1] at hzroot
    have := hrb z hz hzroot'
    suffices h : descendants self z ⊆
        descendants (findState self x) z from
      Nat.le_trans this (Finset.card_le_card h)
    intro j hj
    simp only [descendants, Finset.mem_filter,
      Finset.mem_range] at hj ⊢
    constructor
    · rw [hfs_size]; exact hj.1
    · simp only [findState, UnionFind.findD, dif_pos hx]
      rw [UnionFind.find_root_1]; exact hj.2
  else
    have : findState self x = self := by
      simp [findState, UnionFind.findD, dif_neg hx]
    rw [this]; exact hrb


/-- Link preserves `RankBound`. -/
theorem rankBound_link {self : UnionFind}
    (hrb : RankBound self)
    (x y : Fin self.size)
    (xroot : self.parent x = x)
    (yroot : self.parent y = y) :
    RankBound (self.link x y yroot) := by
  by_cases hxy : x.1 = y.1
  · -- Same root: link is identity
    have : self.link x y yroot = self := by
      change ⟨UnionFind.linkAux self.arr x y, _, _⟩ = self
      simp only [UnionFind.linkAux, hxy, ite_true]
    rw [this]; exact hrb
  · -- Different roots: use root_link
    obtain ⟨r, hr_or, hrl⟩ :=
      UnionFind.root_link xroot yroot
        (x := x) (y := y)
    set L := self.link x y yroot
    have hLsize : L.size = self.size := by
      change (UnionFind.linkAux self.arr x y).size = _
      exact UnionFind.linkAux_size
    have hxr : self.rootD x = x :=
      UnionFind.rootD_eq_self.mpr xroot
    have hyr : self.rootD y = y :=
      UnionFind.rootD_eq_self.mpr yroot
    intro z hz hzroot
    rw [hLsize] at hz
    by_cases hz_m : self.rootD z = x ∨ self.rootD z = y
    · -- z is in the merged component → z = r
      have hLrz : L.rootD z = r.1 := by rw [hrl]; exact if_pos hz_m
      rw [hzroot] at hLrz
      subst hLrz
      -- desc(r) in L ⊇ desc(x) ∪ desc(y) in self
      have hsup := descendants_link_superset self x y
        xroot yroot hxy r hr_or hrl
      have hdisj := descendants_disjoint self x y
        (Fin.val_ne_of_ne (fun h => hxy (congrArg _ h))) hxr hyr
      have hcard := Finset.card_le_card hsup
      rw [Finset.card_union_of_disjoint hdisj] at hcard
      have hrb_x := hrb x x.2 hxr
      have hrb_y := hrb y y.2 hyr
      -- Suffices to show 2^(L.rank r) ≤ desc(x).card + desc(y).card
      -- since desc(x).card + desc(y).card ≤ desc_L(r).card by hcard.
      suffices h : 2 ^ L.rank r ≤
          (descendants self x).card +
          (descendants self y).card from
        Nat.le_trans h hcard
      -- Case split on rank comparison
      by_cases hrank_lt : self.rank y < self.rank x
      · -- y-loser: all ranks unchanged by rank_link_y_loser
        have hrl_all := rank_link_y_loser self x y
          yroot hxy hrank_lt
        -- r = x in this case (from root_link construction)
        -- L.rank r = self.rank r
        rw [hrl_all]
        -- Since r is x or y, and L.rank = self.rank for all:
        rcases hr_or with rfl | rfl
        · -- r = x
          calc 2 ^ self.rank r
              ≤ (descendants self r).card := hrb_x
            _ ≤ _ + _ := Nat.le_add_right _ _
        · -- r = y: but y is not a root in L (y's parent is x)
          exfalso
          have : L.parent r = x := by
            change UnionFind.parent
              (self.link x r yroot) r = x
            rw [UnionFind.parent_link yroot]
            simp only [hxy, ite_false, hrank_lt, ite_true]
          have hne : L.parent r ≠ ↑r := by
            rw [this]; exact Ne.symm
              (Fin.val_ne_of_ne fun h => hxy (congrArg _ h.symm))
          exact hne (UnionFind.rootD_eq_self.mp hzroot)
      · -- x-loser: rank x ≤ rank y
        push_neg at hrank_lt
        rcases hr_or with rfl | rfl
        · -- r = x: but x is not a root in L (x's parent is y)
          exfalso
          have hpr : L.parent r = y := by
            change UnionFind.parent
              (self.link r y yroot) r = y
            rw [UnionFind.parent_link yroot]
            simp only [hxy, ite_false,
              show ¬(self.rank y < self.rank r) from
                not_lt.mpr hrank_lt]
            simp
          have hne : L.parent r ≠ ↑r := by
            rw [hpr]; exact
              Fin.val_ne_of_ne fun h => hxy (congrArg _ h.symm)
          exact hne (UnionFind.rootD_eq_self.mp hzroot)
        · -- r = y (correct case)
          by_cases hreq : self.rank x = self.rank r
          · rw [rank_link_x_loser_eq self x r yroot hxy hreq]
            have h1 : 2 ^ self.rank r ≤
                (descendants self x).card := by rwa [← hreq]
            have h2 : 2 ^ self.rank r ≤
                (descendants self r).card := hrb_y
            have : 2 ^ (self.rank r + 1) =
                2 ^ self.rank r + 2 ^ self.rank r := by
              rw [Nat.pow_succ]; omega
            omega
          · have hlt : self.rank x < self.rank r := by omega
            rw [rank_link_x_loser_lt self x r yroot hxy hlt]
            exact Nat.le_trans hrb_y (Nat.le_add_left _ _)
    · -- z not in merged component
      push_neg at hz_m
      have hLrz : L.rootD z = self.rootD z := by
        rw [hrl, if_neg (by push_neg; exact hz_m)]
      have hzroot_self : self.parent z = z :=
        UnionFind.rootD_eq_self.mp (hLrz.symm.trans hzroot)
      have hzroot' : self.rootD z = z :=
        UnionFind.rootD_eq_self.mpr hzroot_self
      rw [UnionFind.rootD_eq_self.mpr hzroot_self] at hLrz
      have hrb_z := hrb z hz hzroot'
      have hzne_x : z ≠ x.1 :=
        fun h => hz_m.1 (by rw [h, hxr])
      have hzne_y : z ≠ y.1 :=
        fun h => hz_m.2 (by rw [h, hyr])
      rw [rank_link_eq self x y yroot hxy z hzne_x hzne_y]
      suffices hsub : descendants self z ⊆ descendants L z from
        Nat.le_trans hrb_z (Finset.card_le_card hsub)
      intro j hj
      simp only [descendants, Finset.mem_filter,
        Finset.mem_range] at hj ⊢
      refine ⟨by rw [hLsize]; exact hj.1, ?_⟩
      rw [hrl, if_neg]
      · exact hj.2
      · push_neg; constructor
        · intro h; exact hzne_x (by rw [← hj.2]; exact h)
        · intro h; exact hzne_y (by rw [← hj.2]; exact h)


/-- Union preserves `RankBound`. -/
theorem rankBound_union {self : UnionFind}
    (hrb : RankBound self)
    (x y : Fin self.size) :
    RankBound (self.union x y) := by
  -- Unfold union: find x, find y, link rx ry
  unfold UnionFind.union
  simp only
  -- After unfolding, the goal is about a link on self₂
  -- self₁ = (self.find x).1, self₂ = (self₁.find y').1
  set res := self.find x with hres
  set self₁ := res.1
  set rx := res.2 with hrx_def
  have hsize₁ : self₁.size = self.size :=
    UnionFind.find_size self x
  have hy₁ : ↑y < self₁.size := by rw [hsize₁]; exact y.2
  -- RankBound for self₁
  have hself₁ : self₁ = findState self ↑x := by
    change res.1 = (self.findD ↑x).1
    rw [UnionFind.findD, dif_pos x.2, ← hres]
  have hrb₁ : RankBound self₁ :=
    hself₁ ▸ rankBound_findState hrb ↑x
  -- self₂
  set res₂ := self₁.find ⟨↑y, hy₁⟩ with hres₂
  set self₂ := res₂.1
  set ry := res₂.2 with hry_def
  -- RankBound for self₂
  have hself₂ : self₂ = findState self₁ ↑y := by
    change res₂.1 = (self₁.findD ↑y).1
    rw [UnionFind.findD, dif_pos hy₁, ← hres₂]
  have hrb₂ : RankBound self₂ :=
    hself₂ ▸ rankBound_findState hrb₁ ↑y
  -- rx is a root in self₂
  have hrx_val : rx.1.1 = self.rootD x :=
    UnionFind.find_root_2 self x
  have h0 : self₁.rootD x = self.rootD x :=
    UnionFind.find_root_1 self x x
  have h1 : self₁.parent (self.rootD x) = self.rootD x := by
    rw [← h0, UnionFind.parent_rootD, h0]
  have hrx_root : self₂.parent rx.1.1 = rx.1.1 := by
    rw [hrx_val]
    rcases UnionFind.find_parent_or self₁ ⟨↑y, hy₁⟩
      (self.rootD x) with ⟨h2, _⟩ | h2
    · rw [h2]
      exact UnionFind.rootD_eq_self.mpr h1
    · rw [h2, h1]
  -- The goal should now be about self₂.link ...
  -- Apply rankBound_link
  change RankBound (self₂.link _ _ _)
  exact rankBound_link hrb₂ _ _ hrx_root _


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


/-- `findState` preserves the equivalence relation. -/
theorem findState_equiv (self : UnionFind) (x a b : ℕ) :
    UnionFind.Equiv (findState self x) a b ↔
    UnionFind.Equiv self a b := by
  simp only [findState, UnionFind.findD]
  split
  · exact UnionFind.equiv_find
  · exact Iff.rfl


/-- `findState` preserves the size. -/
theorem findState_size (self : UnionFind) (x : ℕ) :
    (findState self x).size = self.size := by
  simp only [findState, UnionFind.findD]
  split
  · exact UnionFind.find_size ..
  · rfl

/-! ### RankCountBound

The rank-count invariant: for each rank level r, at most ⌊n/2^r⌋
nodes have rank ≥ r. This is preserved by all union-find operations
and follows from the Tarjan (1975) observation that same-rank nodes
have disjoint subtrees in the uncompressed tree. -/

/-- The exact rank-count bound: at most ⌊n/2^r⌋ nodes have rank
exactly r. Equivalently, #{rank = r} · 2^r ≤ n. This is the
standard formulation from Tarjan (1975), Lemma 2. -/
def RankCountBound (uf : UnionFind) : Prop :=
  ∀ r : ℕ, ((Finset.range uf.size).filter
    (fun i => decide (uf.rank i = r) = true)).card *
      2 ^ r ≤ uf.size

/-- Ghost state: for each rank level r, an assignment of
disjoint witness sets of size ≥ 2^r to all rank-r nodes.
This formalizes Tarjan's "disjoint subtrees" observation.

From `HasRankBacking`, we derive `RankCountBound`
(#{rank = r} · 2^r ≤ n for each r) using the pairwise
disjointness of same-rank backings.

The key additional invariant is that each backing is
contained in the descendants of the node's root. This
gives cross-level disjointness for nodes in different
components, which is needed to maintain the backing
through equal-rank link operations. -/
def HasRankBacking (uf : UnionFind)
    (B : ℕ → ℕ → Finset ℕ) : Prop :=
  -- Each rank-r node's backing has ≥ 2^r elements
  (∀ r i, i < uf.size → uf.rank i = r →
    2 ^ r ≤ (B r i).card) ∧
  -- Same-rank backings are pairwise disjoint
  (∀ r i j, i < uf.size → j < uf.size →
    uf.rank i = r → uf.rank j = r → i ≠ j →
    Disjoint (B r i) (B r j)) ∧
  -- All backings are within {0..n-1}
  (∀ r i, B r i ⊆ Finset.range uf.size) ∧
  -- Non-rank-r nodes have empty backing at level r
  (∀ r i, uf.rank i ≠ r → B r i = ∅) ∧
  -- Each backing is contained in the descendants of
  -- the node's root (gives cross-level disjointness
  -- for nodes in different components)
  (∀ r i, i < uf.size → B r i ⊆ descendants uf (uf.rootD i))

/-- From `HasRankBacking`, derive `RankCountBound`
(#{rank = r} · 2^r ≤ n for each r).

Proof: The disjoint union of same-rank backings at level r
has cardinality = Σ |B(r,i)| ≥ #{rank=r} · 2^r, and this
union is ⊆ range n, so #{rank=r} · 2^r ≤ n. -/
theorem rankCountBound_of_backing {uf : UnionFind}
    {B : ℕ → ℕ → Finset ℕ} (hB : HasRankBacking uf B) :
    RankCountBound uf := by
  obtain ⟨hsize, hdisj, hrange, hempty, _hdesc⟩ := hB
  intro r
  set S := (Finset.range uf.size).filter
    (fun i => decide (uf.rank i = r) = true) with hS
  -- The biUnion of backings at level r for all rank-r nodes
  -- is a disjoint union within range n.
  have hpwd : (S : Set ℕ).PairwiseDisjoint (fun i => B r i) := by
    intro i hi j hj hne
    simp only [hS, Finset.mem_coe, Finset.mem_filter,
      Finset.mem_range, decide_eq_true_eq] at hi hj
    exact hdisj r i j hi.1 hj.1 hi.2 hj.2 hne
  have hbij : S.card * 2 ^ r ≤ (S.biUnion (fun i => B r i)).card := by
    rw [Finset.card_biUnion hpwd]
    calc S.card * 2 ^ r
        = S.sum (fun _ => 2 ^ r) := by
          simp [Finset.sum_const]
      _ ≤ S.sum (fun i => (B r i).card) := by
          apply Finset.sum_le_sum; intro i hi
          simp only [hS, Finset.mem_filter, Finset.mem_range,
            decide_eq_true_eq] at hi
          exact hsize r i hi.1 hi.2
  -- The biUnion ⊆ range n, so its cardinality ≤ n.
  have hsub : (S.biUnion (fun i => B r i)) ⊆ Finset.range uf.size := by
    intro x hx
    simp only [Finset.mem_biUnion] at hx
    obtain ⟨i, _, hxi⟩ := hx
    exact hrange r i hxi
  calc S.card * 2 ^ r
      ≤ (S.biUnion (fun i => B r i)).card := hbij
    _ ≤ (Finset.range uf.size).card := Finset.card_le_card hsub
    _ = uf.size := Finset.card_range uf.size

/-- Empty UF has trivial backing. -/
theorem hasRankBacking_empty :
    HasRankBacking UnionFind.empty (fun _ _ => ∅) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro r i hi; simp [UnionFind.size] at hi
  · intro r i j hi; simp [UnionFind.size] at hi
  · intro r i; exact Finset.empty_subset _
  · intro r i _; rfl
  · intro r i hi; simp [UnionFind.size] at hi

/-- Push preserves backing: new node gets {n} at rank 0. -/
theorem hasRankBacking_push {self : UnionFind}
    {B : ℕ → ℕ → Finset ℕ} (hB : HasRankBacking self B) :
    ∃ B', HasRankBacking self.push B' := by
  obtain ⟨hsize, hdisj, hrange, hempty, hdesc⟩ := hB
  have hn_rank : self.rank self.size = 0 := by
    unfold UnionFind.rank UnionFind.rankD
    rw [dif_neg (show ¬(self.size < self.arr.size) by simp [UnionFind.size])]
  have hpsize : self.push.size = self.size + 1 := by
    simp [UnionFind.size, UnionFind.arr_push, Array.size_push]
  -- B' uses {n} for the new node at rank 0, B otherwise
  let B' : ℕ → ℕ → Finset ℕ :=
    fun r i => if i = self.size ∧ r = 0 then {self.size} else B r i
  refine ⟨B', ?_, ?_, ?_, ?_, ?_⟩
  -- All goals involve B'(r,i). Use split_ifs to handle the if-then-else.
  -- 1. Size bound
  · intro r i hi hri; rw [UnionFind.rank_push] at hri; rw [hpsize] at hi
    dsimp only [B']; split_ifs with h
    · obtain ⟨_, hr⟩ := h; subst hr; simp
    · have hi' : i < self.size := by
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h' | h'
        · exact h'
        · exfalso; exact h ⟨h', by rw [← hri, h', hn_rank]⟩
      exact hsize r i hi' hri
  -- 2. Disjointness
  · intro r i j hi hj hri hrj hne
    rw [UnionFind.rank_push] at hri hrj; rw [hpsize] at hi hj
    dsimp only [B']; split_ifs with h1 h2 h2
    · exact absurd (h1.1.trans h2.1.symm) hne
    · have hj' : j < self.size := by
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h' | h'
        · exact h'
        · exfalso; exact h2 ⟨h', by rw [← hrj, h', hn_rank]⟩
      rw [Finset.disjoint_left]; intro x hx hxB
      simp at hx; subst hx
      exact absurd (Finset.mem_range.mp (hrange _ j hxB)) (by omega)
    · have hi' : i < self.size := by
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h' | h'
        · exact h'
        · exfalso; exact h1 ⟨h', by rw [← hri, h', hn_rank]⟩
      rw [Finset.disjoint_left]; intro x hxB hx
      simp at hx; subst hx
      exact absurd (Finset.mem_range.mp (hrange _ i hxB)) (by omega)
    · have hi' : i < self.size := by
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h' | h'
        · exact h'
        · exfalso; exact h1 ⟨h', by rw [← hri, h', hn_rank]⟩
      have hj' : j < self.size := by
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h' | h'
        · exact h'
        · exfalso; exact h2 ⟨h', by rw [← hrj, h', hn_rank]⟩
      exact hdisj r i j hi' hj' hri hrj hne
  -- 3. Range bound
  · intro r i; rw [hpsize]; dsimp only [B']; split_ifs with h
    · intro x hx; simp at hx; subst hx
      exact Finset.mem_range.mpr (by omega)
    · exact fun x hx => Finset.mem_range.mpr (by
        have := Finset.mem_range.mp (hrange r i hx); omega)
  -- 4. Empty for wrong rank
  · intro r i hri; rw [UnionFind.rank_push] at hri
    dsimp only [B']; split_ifs with h
    · obtain ⟨hieq, hr⟩ := h; subst hr; subst hieq
      exact absurd hn_rank hri
    · exact hempty r i hri
  -- 5. Descendants constraint
  · intro r i hi; rw [hpsize] at hi; dsimp only [B']
    split_ifs with h
    · obtain ⟨hin, hr⟩ := h; subst hin; subst hr
      intro x hx; simp at hx; subst hx
      simp only [descendants, Finset.mem_filter, Finset.mem_range]
      constructor
      · rw [hpsize]; omega
      · simp only [UnionFind.root_push]
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | hi'
      · intro x hx
        have hxd := hdesc r i hi' hx
        simp only [descendants, Finset.mem_filter, Finset.mem_range] at hxd ⊢
        exact ⟨by rw [hpsize]; omega,
          by rw [UnionFind.root_push, UnionFind.root_push]; exact hxd.2⟩
      · -- i = self.size but r ≠ 0, so B'(r, n) = B(r, n) = ∅
        subst hi'
        have : B r self.size = ∅ := hempty r self.size (by rw [hn_rank]; omega)
        rw [this]; exact Finset.empty_subset _


/-- Find preserves backing (ranks and size unchanged). -/
theorem hasRankBacking_findState {self : UnionFind}
    {B : ℕ → ℕ → Finset ℕ} (hB : HasRankBacking self B)
    (x : ℕ) :
    ∃ B', HasRankBacking (findState self x) B' := by
  obtain ⟨hsize, hdisj, hrange, hempty, hdesc⟩ := hB
  have hfs_size : (findState self x).size = self.size :=
    findState_size self x
  have hfs_rank : ∀ i, (findState self x).rank i = self.rank i := by
    intro i; simp only [findState, UnionFind.findD]
    split
    · exact UnionFind.rankD_findAux
    · rfl
  -- Use the same backing B.
  refine ⟨B, ?_, ?_, ?_, ?_, ?_⟩
  · intro r i hi hri; rw [hfs_size] at hi; rw [hfs_rank] at hri
    exact hsize r i hi hri
  · intro r i j hi hj hri hrj hne
    rw [hfs_size] at hi hj; rw [hfs_rank] at hri hrj
    exact hdisj r i j hi hj hri hrj hne
  · intro r i; rw [hfs_size]; exact hrange r i
  · intro r i hri; rw [hfs_rank] at hri; exact hempty r i hri
  · intro r i hi; rw [hfs_size] at hi
    intro j hj
    have hjd := hdesc r i hi hj
    simp only [descendants, Finset.mem_filter, Finset.mem_range] at hjd ⊢
    constructor
    · rw [hfs_size]; exact hjd.1
    · -- rootD in findState = rootD in self
      have hroot_eq : ∀ k, (findState self x).rootD k = self.rootD k := by
        intro k; simp only [findState, UnionFind.findD]
        split
        · exact UnionFind.find_root_1 ..
        · rfl
      rw [hroot_eq, hroot_eq]; exact hjd.2

/-- Link preserves backing. In the equal-rank case,
y's new backing at rank r+1 is B(r,x) ∪ B(r,y). -/
theorem hasRankBacking_link {self : UnionFind}
    {B : ℕ → ℕ → Finset ℕ} (hB : HasRankBacking self B)
    (hrb : RankBound self)
    (x y : Fin self.size)
    (xroot : self.parent x = x)
    (yroot : self.parent y = y) :
    ∃ B', HasRankBacking (self.link x y yroot) B' := by
  obtain ⟨hsize, hdisj, hrange, hempty, hdesc⟩ := hB
  by_cases hxy : x.1 = y.1
  · -- Case 1: x = y, link is identity
    have : self.link x y yroot = self := by
      change ⟨UnionFind.linkAux self.arr x y, _, _⟩ = self
      simp only [UnionFind.linkAux, hxy, ite_true]
    rw [this]; exact ⟨B, hsize, hdisj, hrange, hempty, hdesc⟩
  · -- Case 2: x ≠ y
    set L := self.link x y yroot
    have hLsize : L.size = self.size := by
      change (UnionFind.linkAux self.arr x y).size = _
      exact UnionFind.linkAux_size
    have hxr : self.rootD x = x :=
      UnionFind.rootD_eq_self.mpr xroot
    have hyr : self.rootD y = y :=
      UnionFind.rootD_eq_self.mpr yroot
    obtain ⟨r, hr_or, hrl⟩ :=
      UnionFind.root_link xroot yroot (x := x) (y := y)
    -- Helper: descendants grow after link for nodes in merged component
    have hdesc_grow : ∀ i, i < self.size →
        (self.rootD i = x ∨ self.rootD i = y) →
        descendants self (self.rootD i) ⊆ descendants L r := by
      intro i hi hmerge
      intro j hj
      simp only [descendants, Finset.mem_filter, Finset.mem_range] at hj ⊢
      constructor
      · rw [hLsize]; exact hj.1
      · rw [hrl]; simp only [hj.2]
        rcases hmerge with h | h <;> simp [h]
    -- Helper: descendants unchanged for nodes not in merged component
    have hdesc_same : ∀ i, i < self.size →
        self.rootD i ≠ x ∧ self.rootD i ≠ y →
        descendants self (self.rootD i) ⊆ descendants L (self.rootD i) := by
      intro i hi ⟨hnex, hney⟩
      intro j hj
      simp only [descendants, Finset.mem_filter, Finset.mem_range] at hj ⊢
      constructor
      · rw [hLsize]; exact hj.1
      · rw [hrl]
        have : ¬(self.rootD j = ↑x ∨ self.rootD j = ↑y) := by
          push_neg; constructor
          · intro h; exact hnex (by rw [← hj.2]; exact h)
          · intro h; exact hney (by rw [← hj.2]; exact h)
        rw [if_neg this]; exact hj.2
    -- Case split on rank comparison
    by_cases hrank_lt : self.rank y < self.rank x
    · -- Sub-case 2a: y-loser. All ranks unchanged. Use B' = B.
      have hrl_all := rank_link_y_loser self x y yroot hxy hrank_lt
      refine ⟨B, ?_, ?_, ?_, ?_, ?_⟩
      · -- size bound
        intro s i hi hri; rw [hLsize] at hi; rw [hrl_all] at hri
        exact hsize s i hi hri
      · -- disjointness
        intro s i j hi hj hri hrj hne
        rw [hLsize] at hi hj; rw [hrl_all] at hri hrj
        exact hdisj s i j hi hj hri hrj hne
      · -- range
        intro s i; rw [hLsize]; exact hrange s i
      · -- empty for wrong rank
        intro s i hri; rw [hrl_all] at hri; exact hempty s i hri
      · -- descendants
        intro s i hi; rw [hLsize] at hi
        intro j hj
        have hjd := hdesc s i hi hj
        simp only [descendants, Finset.mem_filter, Finset.mem_range] at hjd ⊢
        refine ⟨by rw [hLsize]; exact hjd.1, ?_⟩
        have heq : self.rootD j = self.rootD i := hjd.2
        rw [show L.rootD j = _ from hrl j, show L.rootD i = _ from hrl i]
        simp only [heq]
    · -- x-loser: rank x ≤ rank y
      push_neg at hrank_lt
      have hrank_other : ∀ i, i ≠ x.1 → i ≠ y.1 → L.rank i = self.rank i :=
        fun i hix hiy => rank_link_eq self x y yroot hxy i hix hiy
      by_cases hrank_eq : self.rank x = self.rank y
      · -- Sub-case 2c: equal ranks, y bumped to r+1
        set rr := self.rank x
        -- In equal-rank case, the winner is y (x becomes child of y)
        -- Define B'
        let B' : ℕ → ℕ → Finset ℕ :=
          fun s i =>
            if s = rr ∧ i = y.1 then ∅
            else if s = rr + 1 ∧ i = y.1 then B rr x ∪ B rr y
            else B s i
        -- Rank lemma for L
        have hrank_y : L.rank y = rr + 1 := by
          rw [rank_link_x_loser_eq self x y yroot hxy hrank_eq, hrank_eq]
        have hrank_x : L.rank x = self.rank x := by
          change UnionFind.rankD (UnionFind.linkAux self.arr x y) x =
            UnionFind.rankD self.arr x
          simp only [UnionFind.linkAux, show ¬(x.1 = y.1) from hxy, ite_false]
          have : ¬(self.arr[y.1].rank < self.arr[x.1].rank) := by
            simp [← UnionFind.rankD_eq x.2, ← UnionFind.rankD_eq y.2]; omega
          simp only [this, ite_false]
          have : self.arr[x.1].rank = self.arr[y.1].rank := by
            simp [← UnionFind.rankD_eq x.2, ← UnionFind.rankD_eq y.2]; exact hrank_eq
          rw [if_pos this]
          rw [UnionFind.rankD_set,
            if_neg (Ne.symm (Fin.val_ne_of_ne (fun h => hxy (congrArg _ h))))]
          rw [UnionFind.rankD_set, if_pos rfl]
          simp [UnionFind.rankD_eq x.2]
        -- x had rank rr, y had rank rr, both roots, x ≠ y → B rr x and B rr y disjoint
        have hBdisj : Disjoint (B rr x) (B rr y) :=
          hdisj rr x y x.2 y.2 rfl hrank_eq.symm
            (Fin.val_ne_of_ne (fun h => hxy (congrArg _ h)))
        -- Helper to get self.rank from L.rank for non-y nodes
        have Lrank_self : ∀ k, k ≠ y.1 → L.rank k = self.rank k := by
          intro k hky
          by_cases hkx : k = x.1
          · subst hkx; exact hrank_x
          · exact hrank_other k hkx hky
        refine ⟨B', ?_, ?_, ?_, ?_, ?_⟩
        · -- 1. Size bound: 2^s ≤ |B'(s,i)| when L.rank i = s
          intro s i hi hri; rw [hLsize] at hi
          dsimp only [B']
          by_cases hiy : i = y.1
          · subst hiy
            rw [if_neg (by rw [hrank_y] at hri; omega : ¬(s = rr ∧ y.1 = y.1))]
            by_cases hs : s = rr + 1
            · rw [if_pos ⟨hs, rfl⟩]; subst hs
              rw [Finset.card_union_of_disjoint hBdisj]
              have h1 := hsize rr x x.2 rfl
              have h2 := hsize rr y y.2 hrank_eq.symm
              rw [Nat.pow_succ]; omega
            · -- s ≠ rr+1: resolve second if, then L.rank y = rr+1 contradicts
              rw [if_neg (fun h => hs h.1 : ¬(s = rr + 1 ∧ y.1 = y.1))]
              rw [hrank_y] at hri; exact absurd hri.symm hs
          · rw [if_neg (fun h => hiy h.2 : ¬(s = rr ∧ i = y.1)),
                if_neg (fun h => hiy h.2 : ¬(s = rr + 1 ∧ i = y.1))]
            have hLri := Lrank_self i hiy; rw [hLri] at hri
            exact hsize s i hi hri
        · -- 2. Disjointness
          intro s i j hi hj hri hrj hne; rw [hLsize] at hi hj
          -- Case split on whether i or j is y
          by_cases hiy : i = y.1
          · subst hiy
            -- i = y.1. L.rank y = rr+1, so s = rr+1
            rw [hrank_y] at hri
            by_cases hjy : j = y.1
            · exact absurd hjy (Ne.symm hne)
            · -- j ≠ y.1
              dsimp only [B']
              -- B'(s, y) with s = rr+1: first if is (s=rr ∧ y=y) → s=rr, but s=rr+1, so false
              rw [if_neg (by omega : ¬(s = rr ∧ y.1 = y.1)),
                  if_pos ⟨hri.symm, rfl⟩]
              -- B'(s, j) with j ≠ y.1: both ifs have i=y.1 condition fail
              rw [if_neg (fun h => hjy h.2 : ¬(s = rr ∧ j = y.1)),
                  if_neg (fun h => hjy h.2 : ¬(s = rr + 1 ∧ j = y.1))]
              -- Goal: Disjoint (B rr x ∪ B rr y) (B s j)
              have hLrj := Lrank_self j hjy; rw [hLrj] at hrj
              have hrootj_nex : self.rootD j ≠ ↑x := by
                intro h; have := UnionFind.le_rank_root (self := self) (x := j)
                rw [h] at this; omega
              have hrootj_ney : self.rootD j ≠ ↑y := by
                intro h; have := UnionFind.le_rank_root (self := self) (x := j)
                rw [h] at this; rw [← hrank_eq] at this; omega
              rw [Finset.disjoint_left]
              intro a ha haBj
              rcases Finset.mem_union.mp ha with haBx | haBy
              · have h1 := hdesc rr x x.2 haBx
                have h2 := hdesc s j hj haBj
                simp only [hxr, descendants, Finset.mem_filter, Finset.mem_range] at h1 h2
                exact hrootj_nex ((h1.2.symm.trans h2.2).symm)
              · have h1 := hdesc rr y y.2 haBy
                have h2 := hdesc s j hj haBj
                simp only [hyr, descendants, Finset.mem_filter, Finset.mem_range] at h1 h2
                exact hrootj_ney ((h1.2.symm.trans h2.2).symm)
          · by_cases hjy : j = y.1
            · subst hjy
              -- j = y.1, i ≠ y.1
              rw [hrank_y] at hrj
              dsimp only [B']
              -- B'(s, i) with i ≠ y.1: both ifs false
              rw [if_neg (fun h => hiy h.2 : ¬(s = rr ∧ i = y.1)),
                  if_neg (fun h => hiy h.2 : ¬(s = rr + 1 ∧ i = y.1))]
              -- B'(s, y) with s = rr+1
              rw [if_neg (by omega : ¬(s = rr ∧ y.1 = y.1)),
                  if_pos ⟨hrj.symm, rfl⟩]
              -- Goal: Disjoint (B s i) (B rr x ∪ B rr y)
              have hLri := Lrank_self i hiy; rw [hLri] at hri
              have hrooti_nex : self.rootD i ≠ ↑x := by
                intro h; have := UnionFind.le_rank_root (self := self) (x := i)
                rw [h] at this; omega
              have hrooti_ney : self.rootD i ≠ ↑y := by
                intro h; have := UnionFind.le_rank_root (self := self) (x := i)
                rw [h] at this; rw [← hrank_eq] at this; omega
              rw [Finset.disjoint_left]
              intro a haBi ha
              rcases Finset.mem_union.mp ha with haBx | haBy
              · have h1 := hdesc s i hi haBi
                have h2 := hdesc rr x x.2 haBx
                simp only [hxr, descendants, Finset.mem_filter, Finset.mem_range] at h1 h2
                exact hrooti_nex (h1.2.symm.trans h2.2)
              · have h1 := hdesc s i hi haBi
                have h2 := hdesc rr y y.2 haBy
                simp only [hyr, descendants, Finset.mem_filter, Finset.mem_range] at h1 h2
                exact hrooti_ney (h1.2.symm.trans h2.2)
            · -- Neither i nor j is y. B'(s,i) = B(s,i), B'(s,j) = B(s,j)
              dsimp only [B']
              rw [if_neg (fun h => hiy h.2 : ¬(s = rr ∧ i = y.1)),
                  if_neg (fun h => hiy h.2 : ¬(s = rr + 1 ∧ i = y.1)),
                  if_neg (fun h => hjy h.2 : ¬(s = rr ∧ j = y.1)),
                  if_neg (fun h => hjy h.2 : ¬(s = rr + 1 ∧ j = y.1))]
              have hLri := Lrank_self i hiy; rw [hLri] at hri
              have hLrj := Lrank_self j hjy; rw [hLrj] at hrj
              exact hdisj s i j hi hj hri hrj hne
        · -- 3. Range bound
          intro s i; rw [hLsize]
          dsimp only [B']
          split_ifs with h1 h2
          · exact Finset.empty_subset _
          · exact Finset.union_subset (hrange rr x) (hrange rr y)
          · exact hrange s i
        · -- 4. Empty for wrong rank
          intro s i hri
          dsimp only [B']
          by_cases hiy : i = y.1
          · subst hiy
            by_cases hs_rr : s = rr
            · -- s = rr: B'(rr, y) = ∅
              rw [if_pos ⟨hs_rr, rfl⟩]
            · -- s ≠ rr
              rw [if_neg (fun h => hs_rr h.1)]
              by_cases hs_rr1 : s = rr + 1
              · -- s = rr+1: contradiction with hri
                rw [if_pos ⟨hs_rr1, rfl⟩]; exfalso; exact hri (hs_rr1 ▸ hrank_y)
              · rw [if_neg (fun h => hs_rr1 h.1)]
                apply hempty; intro h; exact hs_rr (h.symm.trans hrank_eq.symm)
          · rw [if_neg (fun h => hiy h.2 : ¬(s = rr ∧ i = y.1)),
                if_neg (fun h => hiy h.2 : ¬(s = rr + 1 ∧ i = y.1))]
            have hLri := Lrank_self i hiy; rw [hLri] at hri
            exact hempty s i hri
        · -- 5. Descendants constraint
          intro s i hi; rw [hLsize] at hi
          dsimp only [B']
          by_cases hiy : i = y.1
          · subst hiy
            by_cases hs : s = rr
            · -- s = rr, i = y: B' = ∅
              rw [if_pos ⟨hs, rfl⟩]; exact Finset.empty_subset _
            · -- s ≠ rr, i = y: check if s = rr+1
              rw [if_neg (fun h => hs h.1)]
              by_cases hs' : s = rr + 1
              · -- s = rr+1, i = y: B' = B(rr,x) ∪ B(rr,y)
                rw [if_pos ⟨hs', rfl⟩]
                intro j hj
                rcases Finset.mem_union.mp hj with hjBx | hjBy
                · have hjd := hdesc rr x x.2 hjBx
                  simp only [hxr, descendants, Finset.mem_filter, Finset.mem_range] at hjd ⊢
                  refine ⟨by rw [hLsize]; exact hjd.1, ?_⟩
                  rw [show L.rootD j = _ from hrl j, show L.rootD y = _ from hrl y]
                  simp [hjd.2, hyr]
                · have hjd := hdesc rr y y.2 hjBy
                  simp only [hyr, descendants, Finset.mem_filter, Finset.mem_range] at hjd ⊢
                  refine ⟨by rw [hLsize]; exact hjd.1, ?_⟩
                  rw [show L.rootD j = _ from hrl j, show L.rootD y = _ from hrl y]
                  simp [hjd.2, hyr]
              · -- s ≠ rr+1, i = y: B' = B(s, y)
                rw [if_neg (fun h => hs' h.1)]
                -- B(s, y) should be ∅ since self.rank y = rr and s ≠ rr
                -- Actually it might not be ∅ in general. We still need to prove the descendant property.
                intro j hj
                have hjd := hdesc s y y.2 hj
                simp only [descendants, Finset.mem_filter, Finset.mem_range] at hjd ⊢
                refine ⟨by rw [hLsize]; exact hjd.1, ?_⟩
                have heq : self.rootD j = self.rootD y := hjd.2
                rw [show L.rootD j = _ from hrl j, show L.rootD y = _ from hrl y]
                simp [heq, hyr]
          · -- i ≠ y
            rw [if_neg (fun h => hiy h.2 : ¬(s = rr ∧ i = y.1)),
                if_neg (fun h => hiy h.2 : ¬(s = rr + 1 ∧ i = y.1))]
            intro j hj
            have hjd := hdesc s i hi hj
            simp only [descendants, Finset.mem_filter, Finset.mem_range] at hjd ⊢
            refine ⟨by rw [hLsize]; exact hjd.1, ?_⟩
            have heq : self.rootD j = self.rootD i := hjd.2
            rw [show L.rootD j = _ from hrl j, show L.rootD i = _ from hrl i]
            simp only [heq]
      · -- Sub-case 2b: strict x-loser (rank x < rank y). All ranks unchanged. Use B' = B.
        have hlt : self.rank x < self.rank y := by omega
        have hrank_y' : L.rank y = self.rank y :=
          rank_link_x_loser_lt self x y yroot hxy hlt
        have hrank_x' : L.rank x = self.rank x := by
          change UnionFind.rankD (UnionFind.linkAux self.arr x y) x =
            UnionFind.rankD self.arr x
          simp only [UnionFind.linkAux, show ¬(x.1 = y.1) from hxy, ite_false]
          have : ¬(self.arr[y.1].rank < self.arr[x.1].rank) := by
            simp [← UnionFind.rankD_eq x.2, ← UnionFind.rankD_eq y.2]; omega
          simp only [this, ite_false]
          have : ¬(self.arr[x.1].rank = self.arr[y.1].rank) := by
            simp [← UnionFind.rankD_eq x.2, ← UnionFind.rankD_eq y.2]; omega
          simp only [this, ite_false]
          simp [UnionFind.rankD_set, UnionFind.rankD_eq x.2]
        have hrank_all : ∀ i, L.rank i = self.rank i := by
          intro i
          by_cases hix : i = x.1
          · subst hix; exact hrank_x'
          · by_cases hiy : i = y.1
            · subst hiy; exact hrank_y'
            · exact hrank_other i hix hiy
        refine ⟨B, ?_, ?_, ?_, ?_, ?_⟩
        · intro s i hi' hri; rw [hLsize] at hi'; rw [hrank_all] at hri
          exact hsize s i hi' hri
        · intro s i j hi' hj' hri hrj hne
          rw [hLsize] at hi' hj'; rw [hrank_all] at hri hrj
          exact hdisj s i j hi' hj' hri hrj hne
        · intro s i; rw [hLsize]; exact hrange s i
        · intro s i hri; rw [hrank_all] at hri; exact hempty s i hri
        · intro s i hi'; rw [hLsize] at hi'
          intro j hj
          have hjd := hdesc s i hi' hj
          simp only [descendants, Finset.mem_filter, Finset.mem_range] at hjd ⊢
          refine ⟨by rw [hLsize]; exact hjd.1, ?_⟩
          have heq : self.rootD j = self.rootD i := hjd.2
          rw [show L.rootD j = _ from hrl j, show L.rootD i = _ from hrl i]
          simp only [heq]

/-- Union preserves backing. -/
theorem hasRankBacking_union {self : UnionFind}
    {B : ℕ → ℕ → Finset ℕ} (hB : HasRankBacking self B)
    (hrb : RankBound self)
    (x y : Fin self.size) :
    ∃ B', HasRankBacking (self.union x y) B' := by
  -- Use rankBound_union to get RankBound, then construct
  -- backing for the result. The result IS self₂.link ...
  -- but matching the type is tricky. Instead, use the fact
  -- that union = self₂.link and go through the backing chain.
  -- Simpler: just prove RankCountBound and note that
  -- RankCountBound for union follows from the link backing.
  -- Actually we need the existential B'. Let's go step by step.
  have hrbu := rankBound_union hrb x y
  -- We'll construct B' by showing each intermediate step has one.
  -- findState preserves backing
  have hfs1 : ∃ B₁, HasRankBacking (findState self x) B₁ :=
    hasRankBacking_findState hB x
  obtain ⟨B₁, hB₁⟩ := hfs1
  have hrb₁ := rankBound_findState hrb x
  -- self₁ = findState self x = (self.find x).1
  set self₁ := (self.find x).1
  have hself₁ : self₁ = findState self ↑x := by
    change (self.find x).1 = (self.findD ↑x).1
    rw [UnionFind.findD, dif_pos x.2]
  have hB₁' : HasRankBacking self₁ B₁ := hself₁ ▸ hB₁
  have hrb₁' : RankBound self₁ := hself₁ ▸ hrb₁
  have hsize₁ : self₁.size = self.size :=
    UnionFind.find_size self x
  have hy₁ : ↑y < self₁.size := by rw [hsize₁]; exact y.2
  -- findState on self₁
  have hfs2 : ∃ B₂, HasRankBacking (findState self₁ y) B₂ :=
    hasRankBacking_findState hB₁' y
  obtain ⟨B₂, hB₂⟩ := hfs2
  have hrb₂ := rankBound_findState hrb₁' y
  set self₂ := (self₁.find ⟨↑y, hy₁⟩).1
  have hself₂ : self₂ = findState self₁ ↑y := by
    change (self₁.find ⟨↑y, hy₁⟩).1 = (self₁.findD ↑y).1
    rw [UnionFind.findD, dif_pos hy₁]
  have hB₂' : HasRankBacking self₂ B₂ := hself₂ ▸ hB₂
  have hrb₂' : RankBound self₂ := hself₂ ▸ hrb₂
  -- Root of x in self₂
  have h0 : self₁.rootD x = self.rootD x :=
    UnionFind.find_root_1 self x x
  have h1 : self₁.parent (self.rootD x) = self.rootD x := by
    rw [← h0, UnionFind.parent_rootD, h0]
  have hrx_root : self₂.parent (self.find x).2.1.1 =
      (self.find x).2.1.1 := by
    rw [UnionFind.find_root_2 self x]
    rcases UnionFind.find_parent_or self₁ ⟨↑y, hy₁⟩
      (self.rootD x) with ⟨h2, _⟩ | h2
    · rw [h2]; exact UnionFind.rootD_eq_self.mpr h1
    · rw [h2, h1]
  -- self.union x y is definitionally self₂.link rx ry _
  -- Use hasRankBacking_link on self₂
  have hsize₂ : self₂.size = self.size :=
    (UnionFind.find_size self₁ ⟨↑y, hy₁⟩).trans hsize₁
  -- The yroot proof for the link
  have hry : self₂.parent (self₁.find ⟨↑y, hy₁⟩).2.1.1 =
      (self₁.find ⟨↑y, hy₁⟩).2.1.1 := by
    have := UnionFind.find_root_1 self₁ ⟨↑y, hy₁⟩
      (⟨↑y, hy₁⟩ : Fin _)
    rw [← UnionFind.find_root_2] at this
    simp only at this; rw [← this, UnionFind.parent_rootD]
  have hrx_lt : (self.find x).2.1.1 < self₂.size := by
    calc (self.find x).2.1.1
        < self₁.size := (self.find x).2.1.2
      _ = self.size := hsize₁
      _ = self₂.size := hsize₂.symm
  obtain ⟨B₃, hB₃⟩ := hasRankBacking_link hB₂' hrb₂'
    ⟨(self.find x).2.1.1, hrx_lt⟩
    (self₁.find ⟨↑y, hy₁⟩).2.1
    hrx_root hry
  -- Show the union definitionally equals this link
  exact ⟨B₃, by unfold UnionFind.union; exact hB₃⟩

theorem rankCountBound_empty :
    RankCountBound UnionFind.empty :=
  rankCountBound_of_backing hasRankBacking_empty

theorem rankCountBound_push {self : UnionFind}
    (hrc : RankCountBound self) :
    RankCountBound self.push := by
  intro r
  simp only [UnionFind.rank_push]
  have hsize : self.push.size = self.size + 1 := by
    simp [UnionFind.size, UnionFind.arr_push, Array.size_push]
  rw [hsize, Finset.range_add_one, Finset.filter_insert]
  have hcard_old := hrc r
  have hn_rank : self.rank self.size = 0 := by
    simp [UnionFind.rank, UnionFind.rankD]
  split
  · -- self.size passes filter: rank self.size = r, so r = 0
    rename_i hr; simp only [decide_eq_true_eq] at hr
    have hr0 : r = 0 := by rw [hn_rank] at hr; exact hr.symm
    subst hr0; simp only [Nat.pow_zero, Nat.mul_one]
    rw [Finset.card_insert_of_notMem (by simp)]
    -- old #{rank=0} * 1 ≤ n, so #{rank=0} ≤ n, so #{rank=0} + 1 ≤ n + 1
    simp only [Nat.pow_zero, Nat.mul_one] at hcard_old; omega
  · -- self.size doesn't pass: #{rank=r} unchanged, size grows
    calc ((Finset.range self.size).filter _).card * 2 ^ r
        ≤ self.size := hcard_old
      _ ≤ self.size + 1 := by omega

theorem rankCountBound_findState {self : UnionFind}
    (hrc : RankCountBound self) (x : ℕ) :
    RankCountBound (findState self x) := by
  intro r
  have hsize : (findState self x).size = self.size :=
    findState_size self x
  have hrank : ∀ i, (findState self x).rank i = self.rank i := by
    intro i
    simp only [findState, UnionFind.findD]
    split
    · exact UnionFind.rankD_findAux
    · rfl
  simp only [hsize, hrank]
  exact hrc r


theorem rankCountBound_link {self : UnionFind}
    (hrb : RankBound self)
    {B : ℕ → ℕ → Finset ℕ} (hB : HasRankBacking self B)
    (x y : Fin self.size)
    (xroot : self.parent x = x)
    (yroot : self.parent y = y) :
    RankCountBound (self.link x y yroot) := by
  have hrc : RankCountBound self := rankCountBound_of_backing hB
  by_cases hxy : x.1 = y.1
  · -- Same root: link is identity
    have : self.link x y yroot = self := by
      change ⟨UnionFind.linkAux self.arr x y, _, _⟩ = self
      simp only [UnionFind.linkAux, hxy, ite_true]
    rw [this]; exact hrc
  · -- Different roots
    set L := self.link x y yroot
    have hLsize : L.size = self.size := by
      change (UnionFind.linkAux self.arr x y).size = _
      exact UnionFind.linkAux_size
    intro s
    rw [hLsize]
    -- Three sub-cases based on rank comparison
    by_cases hrank_lt : self.rank y < self.rank x
    · -- y-loser: all ranks unchanged
      have hrl : ∀ i, L.rank i = self.rank i :=
        rank_link_y_loser self x y yroot hxy hrank_lt
      simp only [hrl]; exact hrc s
    · push_neg at hrank_lt
      -- Prove rank formula for L
      have hrank_i : ∀ i, L.rank i =
          if self.rank x = self.rank y then
            if i = y.1 then self.rank y + 1 else self.rank i
          else self.rank i := by
        intro i
        by_cases hreq : self.rank x = self.rank y
        · rw [if_pos hreq]
          by_cases hiy : i = y.1
          · subst hiy; simp; exact rank_link_x_loser_eq self x y yroot hxy hreq
          · rw [if_neg hiy]
            by_cases hix : i = x.1
            · subst hix
              change UnionFind.rankD (UnionFind.linkAux self.arr x y) x =
                UnionFind.rankD self.arr x
              simp only [UnionFind.linkAux, show ¬(x.1 = y.1) from hxy, ite_false]
              have : ¬(self.arr[y.1].rank < self.arr[x.1].rank) := by
                simp [← UnionFind.rankD_eq x.2, ← UnionFind.rankD_eq y.2]; omega
              simp only [this, ite_false]
              have : self.arr[x.1].rank = self.arr[y.1].rank := by
                simp [← UnionFind.rankD_eq x.2, ← UnionFind.rankD_eq y.2]; exact hreq
              rw [if_pos this]
              rw [UnionFind.rankD_set,
                if_neg (Ne.symm (Fin.val_ne_of_ne (fun h => hxy (congrArg _ h))))]
              rw [UnionFind.rankD_set, if_pos rfl]
              simp [UnionFind.rankD_eq x.2]
            · exact rank_link_eq self x y yroot hxy i hix hiy
        · rw [if_neg hreq]
          have hlt : self.rank x < self.rank y := by omega
          by_cases hix : i = x.1
          · subst hix
            change UnionFind.rankD (UnionFind.linkAux self.arr x y) x =
              UnionFind.rankD self.arr x
            simp only [UnionFind.linkAux, show ¬(x.1 = y.1) from hxy, ite_false]
            have : ¬(self.arr[y.1].rank < self.arr[x.1].rank) := by
              simp [← UnionFind.rankD_eq x.2, ← UnionFind.rankD_eq y.2]; omega
            simp only [this, ite_false]
            have : ¬(self.arr[x.1].rank = self.arr[y.1].rank) := by
              simp [← UnionFind.rankD_eq x.2, ← UnionFind.rankD_eq y.2]; omega
            simp only [this, ite_false]
            simp [UnionFind.rankD_set, UnionFind.rankD_eq x.2]
          · by_cases hiy : i = y.1
            · subst hiy; exact rank_link_x_loser_lt self x y yroot hxy hlt
            · exact rank_link_eq self x y yroot hxy i hix hiy
      by_cases hreq : self.rank x = self.rank y
      · -- Equal ranks: y bumped r → r+1. Case split on s vs ranks.
        simp only [hreq, ite_true] at hrank_i
        set rr := self.rank x
        -- Compute how the filter changes for each s
        by_cases hs_ne_rr : s ≠ rr ∧ s ≠ rr + 1
        · -- s ≠ rr and s ≠ rr+1: the filter is unchanged
          have hfilt_eq : ((Finset.range self.size).filter
              (fun i => decide (L.rank i = s) = true)).card =
              ((Finset.range self.size).filter
              (fun i => decide (self.rank i = s) = true)).card := by
            congr 1; ext i; simp only [Finset.mem_filter, Finset.mem_range,
              decide_eq_true_eq, hrank_i]
            constructor
            · intro ⟨hi, hge⟩
              by_cases hiy : i = y.1
              · subst hiy; rw [if_pos rfl] at hge; omega
              · rw [if_neg hiy] at hge; exact ⟨hi, hge⟩
            · intro ⟨hi, hge⟩
              refine ⟨hi, ?_⟩
              by_cases hiy : i = y.1
              · subst hiy; rw [if_pos rfl]; omega
              · rw [if_neg hiy]; exact hge
          rw [hfilt_eq]; exact hrc s
        · -- s = rr or s = rr+1
          have hs_or : s = rr ∨ s = rr + 1 := by
            by_contra h; push_neg at h; exact hs_ne_rr ⟨h.1, h.2⟩
          rcases hs_or with rfl | rfl
          · -- s = rr: y leaves this level. Count decreases by 1.
            -- #{rank_L = rr} = #{rank = rr} - 1 (y moved out)
            -- (#{rank=rr} - 1) * 2^rr ≤ #{rank=rr} * 2^rr ≤ n
            have hfilt : ((Finset.range self.size).filter
                (fun i => decide (L.rank i = rr) = true)) ⊆
                ((Finset.range self.size).filter
                (fun i => decide (self.rank i = rr) = true)) := by
              intro i hi
              simp only [Finset.mem_filter, Finset.mem_range,
                decide_eq_true_eq, hrank_i] at hi ⊢
              by_cases hiy : i = y.1
              · subst hiy; rw [if_pos rfl] at hi; omega
              · rw [if_neg hiy] at hi; exact ⟨hi.1, hi.2⟩
            calc ((Finset.range self.size).filter _).card * 2 ^ rr
                ≤ ((Finset.range self.size).filter
                    (fun i => decide (self.rank i = rr) = true)).card * 2 ^ rr :=
                  Nat.mul_le_mul_right _ (Finset.card_le_card hfilt)
              _ ≤ self.size := hrc rr
          · -- s = rr + 1: y joins this level. Key case.
            -- Use ghost-state backing to derive the bound.
            obtain ⟨B', hB'⟩ := hasRankBacking_link hB hrb x y
              xroot yroot
            have := (rankCountBound_of_backing hB') (rr + 1)
            rwa [hLsize] at this
      · -- Strict: rank x < rank y, all ranks unchanged
        simp only [hreq, ite_false] at hrank_i
        have hfilt_eq : ((Finset.range self.size).filter
            (fun i => decide (L.rank i = s) = true)).card =
            ((Finset.range self.size).filter
            (fun i => decide (self.rank i = s) = true)).card := by
          congr 1; ext i; simp only [Finset.mem_filter, Finset.mem_range,
            decide_eq_true_eq, hrank_i]
        rw [hfilt_eq]; exact hrc s

theorem rankCountBound_union {self : UnionFind}
    (hrb : RankBound self)
    {B : ℕ → ℕ → Finset ℕ} (hB : HasRankBacking self B)
    (x y : Fin self.size) :
    RankCountBound (self.union x y) := by
  -- Decompose union, thread backing through find + link
  unfold UnionFind.union; simp only
  set res := self.find x with hres
  set self₁ := res.1
  have hsize₁ : self₁.size = self.size :=
    UnionFind.find_size self x
  have hy₁ : ↑y < self₁.size := by rw [hsize₁]; exact y.2
  have hself₁ : self₁ = findState self ↑x := by
    change res.1 = (self.findD ↑x).1
    rw [UnionFind.findD, dif_pos x.2, ← hres]
  have hrb₁ : RankBound self₁ :=
    hself₁ ▸ rankBound_findState hrb ↑x
  obtain ⟨B₁, hB₁⟩ := hself₁ ▸ hasRankBacking_findState hB x
  set res₂ := self₁.find ⟨↑y, hy₁⟩ with hres₂
  set self₂ := res₂.1
  have hself₂ : self₂ = findState self₁ ↑y := by
    change res₂.1 = (self₁.findD ↑y).1
    rw [UnionFind.findD, dif_pos hy₁, ← hres₂]
  have hrb₂ : RankBound self₂ :=
    hself₂ ▸ rankBound_findState hrb₁ ↑y
  obtain ⟨B₂, hB₂⟩ := hself₂ ▸ hasRankBacking_findState hB₁ y
  have h0 : self₁.rootD x = self.rootD x :=
    UnionFind.find_root_1 self x x
  have h1 : self₁.parent (self.rootD x) = self.rootD x := by
    rw [← h0, UnionFind.parent_rootD, h0]
  have hrx_root : self₂.parent (self.find x).2.1.1 =
      (self.find x).2.1.1 := by
    rw [UnionFind.find_root_2 self x]
    rcases UnionFind.find_parent_or self₁ ⟨↑y, hy₁⟩
      (self.rootD x) with ⟨h2, _⟩ | h2
    · rw [h2]; exact UnionFind.rootD_eq_self.mpr h1
    · rw [h2, h1]
  change RankCountBound (self₂.link _ _ _)
  exact rankCountBound_link hrb₂ hB₂ _ _ hrx_root _

/-- From exact rank bound, derive #{rank = r} ≤ n/2^r. -/
theorem rankCount_le_div {uf : UnionFind}
    (hrc : RankCountBound uf) (r : ℕ) :
    ((Finset.range uf.size).filter
      (fun i => decide (uf.rank i = r) = true)).card ≤
      uf.size / 2 ^ r := by
  exact (Nat.le_div_iff_mul_le (Nat.two_pow_pos r)).mpr (hrc r)

/-- From exact rank bound, rank of any node ≤ size. -/
theorem rank_le_size_of_rankCountBound {uf : UnionFind}
    (hrc : RankCountBound uf) (i : ℕ) (hi : i < uf.size) :
    uf.rank i ≤ uf.size := by
  by_contra h; push_neg at h
  have h1 := hrc (uf.rank i)
  -- node i has rank = rank i, so it's counted
  have h3 : 1 * 2 ^ uf.rank i ≤ uf.size := by
    calc 1 * 2 ^ uf.rank i
        ≤ ((Finset.range uf.size).filter
            (fun j => decide (uf.rank j = uf.rank i) = true)).card *
            2 ^ uf.rank i := by
          apply Nat.mul_le_mul_right
          rw [Finset.one_le_card]
          exact ⟨i, by simp [Finset.mem_filter, Finset.mem_range, hi]⟩
      _ ≤ uf.size := h1
  simp at h3
  -- But n < 2^rank when rank > n
  have h6 : uf.size < 2 ^ uf.rank i := by
    calc uf.size < 2 ^ uf.size := by
          induction uf.size with
          | zero => simp
          | succ n ih => calc n + 1 < 2 * 2 ^ n := by omega
              _ = 2 ^ (n + 1) := by rw [Nat.pow_succ]; omega
      _ ≤ 2 ^ uf.rank i := Nat.pow_le_pow_right (by omega) (by omega)
  omega


end Cslib.Algorithms.Lean.UnionFind

end -- section
