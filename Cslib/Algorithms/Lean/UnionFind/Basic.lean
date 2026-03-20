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

end Cslib.Algorithms.Lean.UnionFind

end -- section
