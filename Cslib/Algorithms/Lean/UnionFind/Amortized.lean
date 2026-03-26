/-
Copyright (c) 2026 CSLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CSLib Contributors
-/

module

public import Cslib.Algorithms.Lean.UnionFind.Basic
public import Cslib.Algorithms.Lean.UnionFind.Ackermann
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Linarith

/-!
# Amortized O(α(n)) Bound for Union-Find

Uses the indicator-sum potential from Huang, Lambert,
Nie, Peng (2023) "Simpler Analyses of Union-Find",
adapted from union-by-size to union-by-rank.

For each non-root node p, the potential counts the number
of (k, ℓ) pairs where `ackIter k (ℓ+1) (rank p)` exceeds
`rank(parent p)`. When path compression increases
`rank(parent p)`, some indicators flip from 1 to 0,
decreasing Φ.

## References

- [Huang, Lambert, Nie, Peng, 2023] *Simpler Analyses of
  Union-Find*, arXiv:2308.09021
- [Tarjan, 1975] *Efficiency of a Good But Not Linear Set
  Union Algorithm*
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.UnionFind

open Batteries (UnionFind)

/-- A stateful operation with cost. -/
def StatefulOp (S : Type*) := S → S × ℕ

/-- The find operation as a stateful operation. -/
def findOp (x : ℕ) : StatefulOp UnionFind := fun uf =>
  (findState uf x, pathLength uf x)

/-- The indicator: 1 if `ackIter k (ℓ+1) r > parentRank`,
0 otherwise. This indicates that the k-th Ackermann
function applied ℓ+1 times to `rank(p)` exceeds
`rank(parent(p))`. -/
def indicator (k ℓ r parentRank : ℕ) : ℕ :=
  if ackIter k (ℓ + 1) r > parentRank then 1 else 0

/-- The per-node potential: sum of indicators over all
Ackermann levels k (0..α(n)) and iterations ℓ (1..rank).
Uses `α(n)` as the upper bound on k, and `rank(p)` as
the upper bound on ℓ. -/
def Φ_node (n : ℕ) (rank parentRank : ℕ) : ℕ :=
  (Finset.range (invAck n + 1)).sum fun k =>
    (Finset.range (rank + 1)).sum fun ℓ =>
      indicator k ℓ rank parentRank

/-- The overall potential. -/
def Φ (uf : UnionFind) : ℕ :=
  (Finset.range uf.size).sum fun p =>
    if uf.parent p = p then 0
    else Φ_node uf.size (uf.rank p)
      (uf.rank (uf.parent p))

/-- Φ_node is bounded by (invAck(n) + 1) * (rank + 1). -/
private theorem Φ_node_le (n rank parentRank : ℕ) :
    Φ_node n rank parentRank ≤
      (invAck n + 1) * (rank + 1) := by
  unfold Φ_node
  calc (Finset.range (invAck n + 1)).sum _ ≤
      (Finset.range (invAck n + 1)).sum
        (fun _ => rank + 1) := by
        apply Finset.sum_le_sum; intro k _
        calc (Finset.range (rank + 1)).sum _ ≤
            (Finset.range (rank + 1)).sum
              (fun _ => 1) := by
              apply Finset.sum_le_sum; intro ℓ _
              unfold indicator; split <;> omega
          _ = rank + 1 := by
              simp [Finset.sum_const, Finset.card_range]
    _ = (invAck n + 1) * (rank + 1) := by
        simp [Finset.sum_const, Finset.card_range]

/-- Φ_node is monotone decreasing in parentRank:
larger parentRank → fewer indicators are 1. -/
private theorem Φ_node_mono {n r pr₁ pr₂ : ℕ}
    (h : pr₁ ≤ pr₂) :
    Φ_node n r pr₂ ≤ Φ_node n r pr₁ := by
  unfold Φ_node
  apply Finset.sum_le_sum; intro k _
  apply Finset.sum_le_sum; intro ℓ _
  unfold indicator
  split
  · split
    · exact Nat.le_refl _
    · rename_i h1 h2; omega
  · exact Nat.zero_le _

/-- After find, ranks are preserved. -/
private theorem findState_rank (uf : UnionFind)
    (x i : ℕ) :
    (findState uf x).rank i = uf.rank i := by
  simp only [findState, UnionFind.findD]
  split
  · change UnionFind.rankD
      (uf.findAux ⟨x, _⟩).s i = uf.rank i
    exact UnionFind.rankD_findAux
  · rfl

/-- After find, parent is either repointed or unchanged. -/
private theorem findState_parent_or (uf : UnionFind)
    (x : ℕ) (hx : x < uf.size) (i : ℕ) :
    (findState uf x).parent i = uf.rootD i ∧
      uf.rootD i = uf.rootD x ∨
    (findState uf x).parent i = uf.parent i := by
  simp only [findState, UnionFind.findD, dif_pos hx]
  exact UnionFind.find_parent_or uf ⟨x, hx⟩ i

/-- After find, each node's parent rank can only increase
(parent is either repointed to root or unchanged). -/
private theorem findState_parent_rank_le
    (uf : UnionFind) (x i : ℕ)
    (hx : x < uf.size) :
    uf.rank (uf.parent i) ≤
      uf.rank ((findState uf x).parent i) := by
  rcases findState_parent_or uf x hx i with
    ⟨h1, _⟩ | h2
  · rw [h1]
    exact Nat.le_trans UnionFind.le_rank_root
      (by rw [UnionFind.rootD_parent])
  · rw [h2]

/-- Φ can only decrease during find: each non-root node's
Φ_node contribution either stays same or decreases
(because parentRank can only increase). -/
theorem Φ_findState_le (uf : UnionFind) (x : ℕ) :
    Φ (findState uf x) ≤ Φ uf := by
  simp only [Φ]
  rw [findState_size]
  if hx : x < uf.size then
    apply Finset.sum_le_sum; intro i _
    split
    · exact Nat.zero_le _
    · rename_i hnotroot_after
      split
      · rename_i hroot_before
        exfalso; apply hnotroot_after
        rcases findState_parent_or uf x hx i with
          ⟨h1, _⟩ | h2
        · rw [h1, UnionFind.rootD_eq_self.mpr
            hroot_before]
        · exact h2 ▸ hroot_before
      · -- Φ_node uses size, rank(i), rank(parent(i))
        -- After find: size unchanged, rank unchanged,
        -- parent rank can only increase → Φ_node ≤
        have := findState_parent_rank_le uf x i hx
        simp only [Φ_node, indicator]
        simp only [findState_rank]
        apply Finset.sum_le_sum; intro k _
        apply Finset.sum_le_sum; intro ℓ _
        split
        · split
          · exact Nat.le_refl _
          · rename_i h1 h2; omega
        · exact Nat.zero_le _
  else
    have : findState uf x = uf := by
      simp [findState, UnionFind.findD, dif_neg hx]
    rw [this]

/-! ### Amortized find bound -/

-- Re-export structural lemmas from earlier version
-- that don't depend on Φ definition.

/-- `findAux` on an ancestor `y` of `x` does not change
`x`'s parent. -/
private theorem findAux_parent_of_lt_rank
    (uf : UnionFind) (y : Fin uf.size) (x : ℕ)
    (hlt : uf.rank x < uf.rank y) :
    UnionFind.parentD (uf.findAux y).s x =
      uf.parent x := by
  rw [UnionFind.parentD_findAux]
  have hne : x ≠ (y : ℕ) := by
    intro h; subst h; exact Nat.lt_irrefl _ hlt
  rw [if_neg hne]
  if hy : uf.arr[y.1].parent = ↑y then
    have : (⟨uf.arr[y.1].parent, uf.parent'_lt y y.2⟩
        : Fin uf.size) = y := by ext; exact hy
    rw [this, UnionFind.findAux_s, if_pos hy]
  else
    have hdec := Nat.sub_lt_sub_left
      (uf.lt_rankMax y) (uf.rank'_lt y.1 y.2 hy)
    have hlt' : uf.rank x <
        uf.rank (uf.arr[y.1].parent) :=
      Nat.lt_trans hlt (uf.rank'_lt y.1 y.2 hy)
    exact findAux_parent_of_lt_rank uf
      ⟨_, uf.parent'_lt y y.2⟩ x hlt'
termination_by uf.rankMax - uf.rank y

/-- `findState(parent(x))` doesn't change x's parent. -/
private theorem findState_parent_unchanged
    (uf : UnionFind) (x : ℕ) (hx : x < uf.size)
    (hne : uf.parent x ≠ x) :
    (findState uf (uf.parent x)).parent x =
      uf.parent x := by
  have hpx : uf.parent x < uf.size :=
    (uf.parent_lt x).mpr hx
  simp only [findState, UnionFind.findD, dif_pos hpx,
    UnionFind.find]
  change UnionFind.parentD
    (uf.findAux ⟨uf.parent x, hpx⟩).s x = _
  exact findAux_parent_of_lt_rank uf
    ⟨uf.parent x, hpx⟩ x (uf.rank_lt hne)

/-- After `findState(x)`, x's parent is `rootD x`. -/
private theorem findState_parent_x_eq
    (uf : UnionFind) (x : ℕ) (hx : x < uf.size) :
    (findState uf x).parent x = uf.rootD x := by
  simp only [findState, UnionFind.findD, dif_pos hx]
  exact UnionFind.find_parent_1 uf ⟨x, hx⟩

/-- For i ≠ x, findState(x) and findState(parent(x))
agree on i's parent. -/
private theorem findState_parent_ne_eq
    (uf : UnionFind) (x : ℕ) (hx : x < uf.size)
    (_hne : uf.parent x ≠ x) (i : ℕ) (hix : i ≠ x) :
    (findState uf x).parent i =
      (findState uf (uf.parent x)).parent i := by
  have hpx : uf.parent x < uf.size :=
    (uf.parent_lt x).mpr hx
  simp only [findState, UnionFind.findD, dif_pos hx,
    dif_pos hpx, UnionFind.find]
  change UnionFind.parentD
    (uf.findAux ⟨x, hx⟩).s i =
    UnionFind.parentD
      (uf.findAux ⟨uf.parent x, hpx⟩).s i
  rw [UnionFind.parentD_findAux (x := ⟨x, hx⟩),
    if_neg hix]
  congr 1; congr 1
  simp [UnionFind.parent, UnionFind.parentD_eq hx]

/-- The Φ decomposition: Φ(findState(p)) =
Φ(findState(x)) + (Φ_node_before - Φ_node_after) at x.
Specifically, the two sums differ only at index x. -/
private theorem Φ_findState_decomp
    (uf : UnionFind) (x : ℕ) (hx : x < uf.size)
    (hne : uf.parent x ≠ x) :
    Φ (findState uf (uf.parent x)) +
      Φ_node uf.size (uf.rank x)
        (uf.rank ((findState uf x).parent x)) =
    Φ (findState uf x) +
      Φ_node uf.size (uf.rank x)
        (uf.rank (uf.parent x)) := by
  -- Both Φ sums differ only at index x.
  -- For i ≠ x: same parent → same Φ_node.
  -- For i = x: findState(p) has parent(x) unchanged,
  --            findState(x) has parent(x) = rootD(x).
  simp only [Φ]
  rw [findState_size, findState_size]
  have hx_mem : x ∈ Finset.range uf.size :=
    Finset.mem_range.mpr hx
  -- Split sums at index x
  rw [← Finset.add_sum_erase _ _ hx_mem,
    ← Finset.add_sum_erase _ _ hx_mem]
  -- At index x: handle the if-then-else
  -- findState(parent(x)) leaves x non-root
  have hne_fp : ¬(findState uf (uf.parent x)).parent x = x := by
    rw [findState_parent_unchanged uf x hx hne]
    exact hne
  -- findState(x) leaves x non-root
  have hne_fx : ¬(findState uf x).parent x = x := by
    rw [findState_parent_x_eq uf x hx]
    exact fun h => hne (UnionFind.rootD_eq_self.mp h)
  simp only [if_neg hne_fp, if_neg hne_fx]
  -- Rewrite ranks using findState_rank
  simp only [findState_rank,
    findState_parent_unchanged uf x hx hne]
  -- Erased sums: for i ≠ x, parent is same in both states
  have herase : ∀ i ∈ (Finset.range uf.size).erase x,
      ((if (findState uf (uf.parent x)).parent i = i
       then 0
       else Φ_node uf.size (uf.rank i)
         (uf.rank ((findState uf (uf.parent x)).parent
           i))) : ℕ) =
      (if (findState uf x).parent i = i then 0
       else Φ_node uf.size (uf.rank i)
         (uf.rank ((findState uf x).parent i))) := by
    intro i hi
    have hix : i ≠ x := Finset.ne_of_mem_erase hi
    rw [findState_parent_ne_eq uf x hx hne i hix]
  rw [Finset.sum_congr rfl herase]
  omega

/-- Count non-paying nodes on the find path. A node is
non-paying if its Φ_node doesn't decrease during
compression. -/
private def nonpaying (uf : UnionFind) (x : ℕ) : ℕ :=
  if h : uf.parent x = x then 0
  else
    have := Nat.sub_lt_sub_left
      (uf.lt_rankMax x) (uf.rank_lt h)
    let d := Φ_node uf.size (uf.rank x)
      (uf.rank (uf.parent x)) -
      Φ_node uf.size (uf.rank x)
      (uf.rank (uf.rootD x))
    (if d = 0 then 1 else 0) +
      nonpaying uf (uf.parent x)
termination_by uf.rankMax - uf.rank x

/-- pathLength + Φ_after ≤ nonpaying + Φ_before. -/
private theorem pathLength_le_nonpaying_add_Φ_drop
    (uf : UnionFind) (x : ℕ) (hx : x < uf.size) :
    pathLength uf x + Φ (findState uf x) ≤
      nonpaying uf x + Φ uf := by
  if hroot : uf.parent x = x then
    have hpl : pathLength uf x = 0 := by
      rw [pathLength, dif_pos hroot]
    have hnp : nonpaying uf x = 0 := by
      rw [nonpaying, dif_pos hroot]
    rw [hpl, hnp]
    exact Nat.add_le_add_left
      (Φ_findState_le uf x) 0
  else
    have hdec := Nat.sub_lt_sub_left
      (uf.lt_rankMax x) (uf.rank_lt hroot)
    have hp_lt : uf.parent x < uf.size :=
      (uf.parent_lt x).mpr hx
    have hpl : pathLength uf x =
        1 + pathLength uf (uf.parent x) := by
      rw [pathLength, dif_neg hroot]
    -- IH on parent
    have ih := pathLength_le_nonpaying_add_Φ_drop uf
      (uf.parent x) hp_lt
    -- Φ decomposition
    have hdecomp := Φ_findState_decomp uf x hx hroot
    -- From decomp, substitute into IH
    -- hdecomp already uses findState_parent_x_eq
    -- (it has rank(rootD x) on the LHS)
    -- ih: pl(p) + Φ(findState p) ≤ np(p) + Φ
    -- hdecomp: Φ(findState p) + Φ_node(rank x, rank(rootD x))
    --        = Φ(findState x) + Φ_node(rank x, rank(parent x))
    -- So: Φ(findState p) = Φ(findState x) + d
    -- where d = Φ_node(before) - Φ_node(after)
    --         = Φ_node(rank x, rank(parent)) - Φ_node(rank x, rank(rootD))
    -- Substituting: pl(p) + Φ(after) + d ≤ np(p) + Φ
    -- Rewrite hdecomp using findState_parent_x_eq
    rw [findState_parent_x_eq uf x hx] at hdecomp
    -- hdecomp: Φ(findState p) + Φ_node(rank x, rank(rootD x))
    --        = Φ(findState x) + Φ_node(rank x, rank(parent x))
    -- So: Φ(findState p) = Φ(findState x) + d
    -- where d = Φ_node_before - Φ_node_after
    have hΦ_mono : Φ_node uf.size (uf.rank x)
        (uf.rank (uf.rootD x)) ≤
        Φ_node uf.size (uf.rank x)
        (uf.rank (uf.parent x)) := Φ_node_mono
      (Nat.le_trans UnionFind.le_rank_root
        (by rw [UnionFind.rootD_parent]))
    -- Substitute
    have ih' : pathLength uf (uf.parent x) +
        Φ (findState uf x) +
        (Φ_node uf.size (uf.rank x)
          (uf.rank (uf.parent x)) -
         Φ_node uf.size (uf.rank x)
          (uf.rank (uf.rootD x))) ≤
        nonpaying uf (uf.parent x) + Φ uf := by
      omega
    clear ih hdecomp
    -- Unfold nonpaying and pathLength
    rw [pathLength, dif_neg hroot,
      nonpaying, dif_neg hroot]
    -- Set d for readability
    set d := Φ_node uf.size (uf.rank x)
      (uf.rank (uf.parent x)) -
      Φ_node uf.size (uf.rank x)
      (uf.rank (uf.rootD x))
    if hd : d = 0 then
      simp only [hd, ite_true]; omega
    else
      simp only [hd, ite_false]
      have : d ≥ 1 := Nat.one_le_iff_ne_zero.mpr hd
      omega
  termination_by uf.rankMax - uf.rank x

/-- nonpaying ≤ pathLength (trivial bound). -/
private theorem nonpaying_le_pathLength
    (uf : UnionFind) (x : ℕ) :
    nonpaying uf x ≤ pathLength uf x := by
  rw [nonpaying, pathLength]
  split
  · exact Nat.le_refl _
  · rename_i h
    have hdec := Nat.sub_lt_sub_left
      (uf.lt_rankMax x) (uf.rank_lt h)
    have ih := nonpaying_le_pathLength uf
      (uf.parent x)
    simp only; split <;> omega
termination_by uf.rankMax - uf.rank x

/-- The level of a non-root node: the largest k such
that `ack(k, rank(x)) ≤ rank(parent(x))`. This matches
the paper's k_i definition. We define it as
`invAck₂(rank, parentRank + 1) - 1`. -/
private def nodeLevel (uf : UnionFind) (x : ℕ) : ℕ :=
  invAck₂ (uf.rank x) (uf.rank (uf.parent x) + 1) - 1

-- Two non-paying nodes at the same level is impossible.
-- (Proof infrastructure moved to avoid namespace issues)
private theorem nonpaying_distinct_levels
    (uf : UnionFind) (i j : ℕ)
    (hi : i < uf.size)
    (_hlt : uf.rank i < uf.rank j)
    (hni : uf.parent i ≠ i)
    (hnj : uf.parent j ≠ j)
    (hi_np : Φ_node uf.size (uf.rank i)
      (uf.rank (uf.parent i)) =
      Φ_node uf.size (uf.rank i)
      (uf.rank (uf.rootD i)))
    (_hj_np : Φ_node uf.size (uf.rank j)
      (uf.rank (uf.parent j)) =
      Φ_node uf.size (uf.rank j)
      (uf.rank (uf.rootD j)))
    (hcomp : uf.rootD i = uf.rootD j)
    (hpi_le_j : uf.rank (uf.parent i) ≤ uf.rank j)
    (hrb : RankBound uf)
    (hri_pos : uf.rank i ≥ 1) :
    nodeLevel uf i ≠ nodeLevel uf j := by
  intro heq
  -- Step 1: nodeLevel gives ack(k, rank) ≤ parentRank
  set k := nodeLevel uf i
  have h_invack_i : invAck₂ (uf.rank i)
      (uf.rank (uf.parent i) + 1) > 0 := by
    -- ack(0, rank i) = rank i + 1 ≤ parentRank i
    -- < parentRank i + 1
    -- So invAck₂(rank i, parentRank i + 1) > 0
    have : ack 0 (uf.rank i) < uf.rank (uf.parent i) + 1 := by
      simp only [ack_zero, add_lt_add_iff_right]
      exact uf.rank_lt hni
    have h0 := invAck₂_le_of_ack_ge
      (show ack 0 (uf.rank i) ≥ uf.rank i + 1 by
        simp [ack_zero])
    -- h0: invAck₂(rank i, rank i + 1) ≤ 0, i.e., = 0
    -- But invAck₂(rank i, parentRank + 1) can't be 0
    -- because ack(0, rank i) < parentRank + 1
    by_contra h
    push_neg at h
    have h1 := ack_invAck₂_ge (uf.rank i)
      (uf.rank (uf.parent i) + 1)
    have h2 : invAck₂ (uf.rank i)
        (uf.rank (uf.parent i) + 1) = 0 := by omega
    rw [h2, ack_zero] at h1
    have := uf.rank_lt hni
    omega
  have hk_i : ack k (uf.rank i) ≤
      uf.rank (uf.parent i) :=
    Nat.le_of_lt_succ
      (@ack_pred_invAck₂_lt (uf.rank i)
        (uf.rank (uf.parent i) + 1) h_invack_i)
  have h_invack_j : invAck₂ (uf.rank j)
      (uf.rank (uf.parent j) + 1) > 0 := by
    have : ack 0 (uf.rank j) <
        uf.rank (uf.parent j) + 1 := by
      simp only [ack_zero, add_lt_add_iff_right]; exact uf.rank_lt hnj
    by_contra h; push_neg at h
    have h1 := ack_invAck₂_ge (uf.rank j)
      (uf.rank (uf.parent j) + 1)
    have h2 : invAck₂ (uf.rank j)
        (uf.rank (uf.parent j) + 1) = 0 := by omega
    rw [h2, ack_zero] at h1
    have := uf.rank_lt hnj; omega
  have hk_j : ack k (uf.rank j) ≤
      uf.rank (uf.parent j) := by
    have : k = invAck₂ (uf.rank j)
        (uf.rank (uf.parent j) + 1) - 1 := heq
    rw [this]
    exact Nat.le_of_lt_succ
      (@ack_pred_invAck₂_lt (uf.rank j)
        (uf.rank (uf.parent j) + 1) h_invack_j)
  -- Step 2: chain R ≥ pj ≥ ack(k,rj) ≥ ackIter(k,ℓ+1,ri)
  have hpj_le_R : uf.rank (uf.parent j) ≤
      uf.rank (uf.rootD i) := by
    rw [hcomp]
    exact Nat.le_trans UnionFind.le_rank_root
      (by rw [UnionFind.rootD_parent])
  set ℓ := @Cslib.Algorithms.Lean.UnionFind.iterCount
    k (uf.rank i) (uf.rank (uf.parent i))
  have hℓ_le : ackIter k ℓ (uf.rank i) ≤
      uf.rank (uf.parent i) :=
    @ackIter_iterCount_le k (uf.rank i)
      (uf.rank (uf.parent i))
      (Nat.le_of_lt (uf.rank_lt hni))
  have hℓ_gt : ackIter k (ℓ + 1) (uf.rank i) >
      uf.rank (uf.parent i) :=
    @ackIter_iterCount_gt k (uf.rank i)
      (uf.rank (uf.parent i))
  have hchain : uf.rank (uf.rootD i) ≥
      ackIter k (ℓ + 1) (uf.rank i) := by
    calc uf.rank (uf.rootD i)
        ≥ uf.rank (uf.parent j) := hpj_le_R
      _ ≥ ack k (uf.rank j) := hk_j
      _ ≥ ack k (uf.rank (uf.parent i)) :=
          ack_le_ack (le_refl _) hpi_le_j
      _ ≥ ack k (ackIter k ℓ (uf.rank i)) :=
          ack_le_ack (le_refl _) hℓ_le
      _ = ackIter k (ℓ + 1) (uf.rank i) := by
          rw [ackIter_succ]
  -- Step 3: indicator(k,ℓ) flips from 1→0, giving Φ_node(pi) > Φ_node(R)
  have hind1 : indicator k ℓ (uf.rank i)
      (uf.rank (uf.parent i)) = 1 := by
    unfold indicator; rw [if_pos hℓ_gt]
  have hind0 : indicator k ℓ (uf.rank i)
      (uf.rank (uf.rootD i)) = 0 := by
    unfold indicator; rw [if_neg (by omega)]
  -- Pointwise ind(R) ≤ ind(pi) and Σ equal (hi_np) → all equal.
  -- But ind(k,ℓ) differs: 1 vs 0. Contradiction via Finset.sum_lt_sum.
  have hpi_le_R : uf.rank (uf.parent i) ≤
      uf.rank (uf.rootD i) :=
    Nat.le_trans UnionFind.le_rank_root
      (by rw [UnionFind.rootD_parent])
  have hpw : ∀ k' ℓ', indicator k' ℓ' (uf.rank i)
      (uf.rank (uf.rootD i)) ≤
      indicator k' ℓ' (uf.rank i)
      (uf.rank (uf.parent i)) := by
    intro k' ℓ'
    unfold indicator; split <;> split <;> omega
  have hstrict : Φ_node uf.size (uf.rank i)
      (uf.rank (uf.rootD i)) <
    Φ_node uf.size (uf.rank i)
      (uf.rank (uf.parent i)) := by
    unfold Φ_node
    apply Finset.sum_lt_sum
    · intro k' _
      apply Finset.sum_le_sum
      intro ℓ' _
      exact hpw k' ℓ'
    · have hpi_lt := (UnionFind.parent_lt uf i).mpr hi
      have hpi_lt_size : uf.rank (uf.parent i) < uf.size :=
        Nat.lt_of_le_of_lt
          (rank_le_log_size uf _ hpi_lt hrb)
          (Nat.log_lt_self 2 (by omega))
      have hk_lt_invAck : k < invAck uf.size := by
        calc k ≤ invAck₂ (uf.rank i)
              (uf.rank (uf.parent i) + 1) - 1 :=
              Nat.le_refl _
          _ < invAck₂ (uf.rank i)
              (uf.rank (uf.parent i) + 1) :=
              Nat.sub_one_lt (by omega)
          _ ≤ @invAck₂ 1
              (uf.rank (uf.parent i) + 1) :=
              @invAck₂_anti_left 1 (uf.rank i)
                (uf.rank (uf.parent i) + 1) hri_pos
          _ ≤ invAck₂ 1 uf.size :=
              invAck₂_mono_right (by omega)
          _ = invAck uf.size := rfl
      have hℓ_le_rank : ℓ ≤ uf.rank i := by
        by_contra h; push_neg at h
        have h1 : uf.rank i + 1 ≤ ℓ := h
        have h2 := @ackIter_iterCount_le k (uf.rank i)
          (uf.rank (uf.parent i))
          (Nat.le_of_lt (uf.rank_lt hni))
        have h3 := @ackIter_mono_right k (uf.rank i + 1) ℓ
          (uf.rank i) h1
        have h4 : ackIter k (uf.rank i + 1) (uf.rank i) ≤
            uf.rank (uf.parent i) := Nat.le_trans h3 h2
        have h5 : ack (k + 1) (uf.rank i) >
            uf.rank (uf.parent i) := by
          have h5a := ack_invAck₂_ge (uf.rank i)
            (uf.rank (uf.parent i) + 1)
          have h5b : k + 1 = invAck₂ (uf.rank i)
              (uf.rank (uf.parent i) + 1) := by
            change invAck₂ (uf.rank i)
              (uf.rank (uf.parent i) + 1) - 1 + 1 = _
            omega
          rw [h5b]; omega
        -- ack(k+1,ri) = ackIter(k,ri+1,1) ≤ ackIter(k,ri+1,ri)
        have h6 : ack (k + 1) (uf.rank i) ≤
            ackIter k (uf.rank i + 1) (uf.rank i) := by
          have hase : ack (k + 1) (uf.rank i) =
              ackIter k (uf.rank i + 1) 1 := by
            induction uf.rank i with
            | zero => simp [ack_succ_zero, ackIter]
            | succ n ih =>
              simp [ack_succ_succ, ih, ackIter_succ]
          rw [hase]
          exact ackIter_mono_base hri_pos
        omega
      refine ⟨k, Finset.mem_range.mpr (by omega), ?_⟩
      apply Finset.sum_lt_sum
      · intro ℓ' _; exact hpw k ℓ'
      · exact ⟨ℓ, Finset.mem_range.mpr (by omega),
          by rw [hind0, hind1]; omega⟩
  omega

/-- The find path as a List. -/
private def findPathList (uf : UnionFind) (x : ℕ) :
    List ℕ :=
  if h : uf.parent x = x then []
  else
    have := Nat.sub_lt_sub_left
      (uf.lt_rankMax x) (uf.rank_lt h)
    x :: findPathList uf (uf.parent x)
termination_by uf.rankMax - uf.rank x

/-- Levels of non-paying rank-≥-1 nodes on the path.
Defined recursively matching `nonpaying`. -/
private def npLevels (uf : UnionFind) (x : ℕ) :
    List ℕ :=
  if h : uf.parent x = x then []
  else
    have := Nat.sub_lt_sub_left
      (uf.lt_rankMax x) (uf.rank_lt h)
    let d := Φ_node uf.size (uf.rank x)
      (uf.rank (uf.parent x)) -
      Φ_node uf.size (uf.rank x)
      (uf.rank (uf.rootD x))
    (if d = 0 ∧ uf.rank x ≥ 1 then
      [nodeLevel uf x]
    else []) ++ npLevels uf (uf.parent x)
termination_by uf.rankMax - uf.rank x

/-- When rank x ≥ 1, nonpaying = npLevels.length.
When rank x = 0, nonpaying ≤ npLevels.length + 1. -/
private theorem nonpaying_le_npLevels
    (uf : UnionFind) (x : ℕ)
    (hrank : uf.rank x ≥ 1) :
    nonpaying uf x = (npLevels uf x).length := by
  rw [nonpaying, npLevels]
  if h : uf.parent x = x then
    simp [h]
  else
    simp only [dif_neg h]
    have hdec := Nat.sub_lt_sub_left
      (uf.lt_rankMax x) (uf.rank_lt h)
    have hparent_rank : uf.rank (uf.parent x) ≥ 1 := by
      have := uf.rank_lt h; omega
    have ih := nonpaying_le_npLevels uf
      (uf.parent x) hparent_rank
    set d := Φ_node uf.size (uf.rank x)
      (uf.rank (uf.parent x)) -
      Φ_node uf.size (uf.rank x)
      (uf.rank (uf.rootD x))
    if hd : d = 0 then
      simp only [hd, ite_true, true_and, hrank,
        ite_true, List.length_append,
        List.length_cons, List.length_nil]
      omega
    else
      have : ¬(d = 0 ∧ uf.rank x ≥ 1) := by omega
      simp only [hd, ite_false, false_and,
        List.nil_append, Nat.zero_add]
      exact ih
  termination_by uf.rankMax - uf.rank x

private theorem nonpaying_le_npLevels_plus_one
    (uf : UnionFind) (x : ℕ) :
    nonpaying uf x ≤ (npLevels uf x).length + 1 := by
  rw [nonpaying, npLevels]
  if h : uf.parent x = x then
    simp [h]
  else
    simp only [dif_neg h]
    have hdec := Nat.sub_lt_sub_left
      (uf.lt_rankMax x) (uf.rank_lt h)
    have hparent_rank : uf.rank (uf.parent x) ≥ 1 := by
      have := uf.rank_lt h; omega
    set d := Φ_node uf.size (uf.rank x)
      (uf.rank (uf.parent x)) -
      Φ_node uf.size (uf.rank x)
      (uf.rank (uf.rootD x))
    if hd : d = 0 then
      simp only [hd, ite_true, true_and]
      if hr1 : uf.rank x ≥ 1 then
        simp only [hr1, ite_true, List.length_append,
          List.length_cons, List.length_nil]
        rw [nonpaying_le_npLevels uf _ hparent_rank]
        omega
      else
        simp only [hr1, ite_false, List.nil_append]
        rw [nonpaying_le_npLevels uf _ hparent_rank]
        omega
    else
      have : ¬(d = 0 ∧ uf.rank x ≥ 1) := by omega
      simp only [hd, ite_false, false_and,
        List.nil_append, Nat.zero_add]
      rw [nonpaying_le_npLevels uf _ hparent_rank]
      omega

/-- If l ∈ npLevels, there's a node on the path with
that level, rank ≥ 1, non-paying, and rank > rank(x)-1. -/
private theorem npLevels_mem
    (uf : UnionFind) (x : ℕ) (l : ℕ)
    (hl : l ∈ npLevels uf x) :
    ∃ y, uf.rank y ≥ 1 ∧
      uf.parent y ≠ y ∧
      nodeLevel uf y = l ∧
      uf.rank y ≥ uf.rank x ∧
      uf.rootD y = uf.rootD x ∧
      (Φ_node uf.size (uf.rank y) (uf.rank (uf.parent y)) =
       Φ_node uf.size (uf.rank y) (uf.rank (uf.rootD y))) := by
  rw [npLevels] at hl
  if h : uf.parent x = x then
    simp [h] at hl
  else
    simp only [dif_neg h] at hl
    have hdec := Nat.sub_lt_sub_left
      (uf.lt_rankMax x) (uf.rank_lt h)
    rw [List.mem_append] at hl
    rcases hl with hl1 | hl2
    · split at hl1 <;> simp only [List.mem_singleton,
          List.not_mem_nil] at hl1
      rename_i hcond
      subst hl1
      exact ⟨x, hcond.2, h, rfl, le_refl _, rfl, by
        have h1 := hcond.1
        have h2 := @Φ_node_mono uf.size (uf.rank x)
          (uf.rank (uf.parent x)) (uf.rank (uf.rootD x))
          (Nat.le_trans UnionFind.le_rank_root
            (by rw [UnionFind.rootD_parent]))
        omega⟩
    · obtain ⟨y, hry, hpy, hly, hrxy, hcomp, hnpy⟩ :=
        npLevels_mem uf (uf.parent x) l hl2
      exact ⟨y, hry, hpy, hly,
        Nat.le_trans (Nat.le_of_lt (uf.rank_lt h)) hrxy,
        by rw [hcomp, UnionFind.rootD_parent],
        hnpy⟩
  termination_by uf.rankMax - uf.rank x

private theorem npLevels_nodup
    (uf : UnionFind) (x : ℕ) (hx : x < uf.size)
    (hrb : RankBound uf) :
    (npLevels uf x).Nodup := by
  rw [npLevels]
  if h : uf.parent x = x then
    simp [h]
  else
    simp only [dif_neg h]
    have hdec := Nat.sub_lt_sub_left
      (uf.lt_rankMax x) (uf.rank_lt h)
    have hp_lt := (uf.parent_lt x).mpr hx
    have ih := npLevels_nodup uf (uf.parent x) hp_lt hrb
    split
    · rename_i hcond
      -- non-paying rank ≥ 1: npLevels = [nodeLevel x] ++ npLevels(parent)
      rw [List.nodup_append]
      refine ⟨List.nodup_singleton _, ih, ?_⟩
      intro a ha b hb
      simp only [List.mem_singleton] at ha
      subst ha
      obtain ⟨y, hry, hpy, hly, hryx, hcompy, hnpy⟩ :=
        npLevels_mem uf (uf.parent x) b hb
      rw [← hly]
      have hrank_lt : uf.rank x < uf.rank y :=
        Nat.lt_of_lt_of_le (uf.rank_lt h) hryx
      have hi_np : Φ_node uf.size (uf.rank x)
          (uf.rank (uf.parent x)) =
          Φ_node uf.size (uf.rank x)
          (uf.rank (uf.rootD x)) := by
        have := hcond.1
        have := @Φ_node_mono uf.size (uf.rank x)
          (uf.rank (uf.parent x))
          (uf.rank (uf.rootD x))
          (Nat.le_trans UnionFind.le_rank_root
            (by rw [UnionFind.rootD_parent]))
        omega
      have hcomp_eq : uf.rootD x = uf.rootD y := by
        rw [hcompy, UnionFind.rootD_parent]
      have hpi_le : uf.rank (uf.parent x) ≤
          uf.rank y := hryx
      exact nonpaying_distinct_levels uf x y hx
        hrank_lt h hpy hi_np hnpy hcomp_eq
        hpi_le hrb hcond.2
    · exact ih
  termination_by uf.rankMax - uf.rank x

/-- npLevels values are < invAck(n) + 1. -/
private theorem npLevels_bound
    (uf : UnionFind) (x : ℕ) (hx : x < uf.size)
    (hrb : RankBound uf) :
    ∀ l ∈ npLevels uf x, l < invAck uf.size + 1 := by
  rw [npLevels]
  if h : uf.parent x = x then
    simp [h]
  else
    simp only [dif_neg h]
    have hdec := Nat.sub_lt_sub_left
      (uf.lt_rankMax x) (uf.rank_lt h)
    have hp_lt := (uf.parent_lt x).mpr hx
    have ih := npLevels_bound uf (uf.parent x) hp_lt hrb
    intro l hl
    simp only [List.mem_append] at hl
    rcases hl with hl1 | hl2
    · -- l is from the current node's [nodeLevel] or []
      split at hl1 <;> simp only [List.mem_singleton,
          List.not_mem_nil] at hl1
      rename_i h1
      obtain ⟨_, hri⟩ := h1
      subst hl1
      -- l = nodeLevel uf x. Bound it.
      unfold nodeLevel
      have hpi_lt_size : uf.rank (uf.parent x) <
          uf.size :=
        Nat.lt_of_le_of_lt
          (rank_le_log_size uf _ hp_lt hrb)
          (Nat.log_lt_self 2 (by omega))
      calc invAck₂ (uf.rank x)
            (uf.rank (uf.parent x) + 1) - 1
          ≤ invAck₂ (uf.rank x)
            (uf.rank (uf.parent x) + 1) :=
            Nat.sub_le _ _
        _ ≤ invAck₂ 1
            (uf.rank (uf.parent x) + 1) :=
            @invAck₂_anti_left 1 (uf.rank x)
              (uf.rank (uf.parent x) + 1) hri
        _ ≤ invAck₂ 1 uf.size :=
            invAck₂_mono_right (by omega)
        _ = invAck uf.size := rfl
        _ < invAck uf.size + 1 := Nat.lt_succ_self _
    · exact ih l hl2
  termination_by uf.rankMax - uf.rank x

private theorem nonpaying_le
    (uf : UnionFind) (x : ℕ) (hx : x < uf.size)
    (hrb : RankBound uf) :
    nonpaying uf x ≤ invAck uf.size + 2 := by
  calc nonpaying uf x
      ≤ (npLevels uf x).length + 1 :=
        nonpaying_le_npLevels_plus_one uf x
    _ ≤ (invAck uf.size + 1) + 1 := by
        apply Nat.add_le_add_right
        have hnd := npLevels_nodup uf x hx hrb
        have hbnd := npLevels_bound uf x hx hrb
        rw [← List.toFinset_card_of_nodup hnd,
          show invAck uf.size + 1 =
            (Finset.range (invAck uf.size + 1)).card
            from by simp [Finset.card_range]]
        exact Finset.card_le_card (fun l hl => by
          rw [List.mem_toFinset] at hl
          exact Finset.mem_range.mpr (hbnd l hl))
    _ = invAck uf.size + 2 := by omega

/-- Amortized find bound: O(α(n)) per find. -/
theorem amortized_find (uf : UnionFind) (x : ℕ)
    (hrb : RankBound uf) :
    pathLength uf x + Φ (findState uf x) ≤
      (invAck uf.size + 2) + Φ uf := by
  if hx : x < uf.size then
    calc pathLength uf x + Φ (findState uf x)
        ≤ nonpaying uf x + Φ uf :=
          pathLength_le_nonpaying_add_Φ_drop uf x hx
      _ ≤ (invAck uf.size + 2) + Φ uf :=
          Nat.add_le_add_right
            (nonpaying_le uf x hx hrb) _
  else
    have hpl : pathLength uf x = 0 := by
      rw [pathLength, dif_pos
        (UnionFind.parentD_of_not_lt hx)]
    have hfs : findState uf x = uf := by
      simp [findState, UnionFind.findD, dif_neg hx]
    rw [hpl, hfs]; omega

/-- The union operation with cost. -/
def unionOp (x y : ℕ) : StatefulOp UnionFind :=
  fun uf =>
  if hx : x < uf.size then
    if hy : y < uf.size then
      (uf.union ⟨x, hx⟩ ⟨y, hy⟩,
       pathLength uf x + pathLength uf y + 1)
    else (uf, 0)
  else (uf, 0)

/-- Rank after link is ≥ rank before. -/
private theorem rank_link_ge (self : UnionFind)
    (x y : Fin self.size) (yroot : self.parent y = y)
    (i : ℕ) :
    self.rank i ≤ (self.link x y yroot).rank i := by
  change UnionFind.rankD self.arr i ≤
    UnionFind.rankD (UnionFind.linkAux self.arr x y) i
  simp only [UnionFind.linkAux]
  split
  · exact Nat.le_refl _
  · split
    · -- rank(y) < rank(x): set y's parent
      rw [UnionFind.rankD_set]; split
      · rename_i h; subst h
        simp [UnionFind.rankD_eq y.2]
      · exact Nat.le_refl _
    · split
      · -- rank(x) = rank(y): bump y's rank
        rw [UnionFind.rankD_set]; split
        · rename_i h; subst h; simp [UnionFind.rankD_eq y.2]
        · rw [UnionFind.rankD_set]; split
          · rename_i h; subst h
            simp [UnionFind.rankD_eq x.2]
          · exact Nat.le_refl _
      · -- rank(x) < rank(y): set x's parent
        rw [UnionFind.rankD_set]; split
        · rename_i h; subst h
          simp [UnionFind.rankD_eq x.2]
        · exact Nat.le_refl _

/-- Φ of link ≤ Φ + one node's contribution.
For link(self, x, y, yroot), the potential increases by
at most the new non-root's Φ_node. -/
private theorem Φ_link_le (self : UnionFind)
    (x y : Fin self.size)
    (xroot : self.parent x = x)
    (yroot : self.parent y = y)
    (hrank_bound : ∀ i, i < self.size →
      self.rank i ≤ Nat.log 2 self.size) :
    Φ (self.link x y yroot) ≤
      Φ self + (invAck self.size + 1) *
        (Nat.log 2 self.size + 1) := by
  -- If x = y, link is identity
  by_cases hxy : x.1 = y.1
  · have heq : self.link x y yroot = self := by
      change ⟨UnionFind.linkAux self.arr x y, _, _⟩ = self
      simp only [UnionFind.linkAux, hxy, ite_true]
    rw [heq]; omega
  · -- x ≠ y: exactly one node becomes non-root
    have hsize : (self.link x y yroot).size =
        self.size := by
      change (UnionFind.linkAux self.arr x y).size =
        self.arr.size
      exact UnionFind.linkAux_size
    -- Unfold Φ for both sides and align ranges
    unfold Φ; rw [hsize]
    -- Abbreviate
    let L := self.link x y yroot
    set fl := fun p => if L.parent p = p then 0
      else Φ_node self.size (L.rank p)
        (L.rank (L.parent p))
    set fs := fun p => if self.parent p = p then 0
      else Φ_node self.size (self.rank p)
        (self.rank (self.parent p))
    -- Determine loser and use sum_erase decomposition
    by_cases hrank : self.rank y < self.rank x
    · -- y is the loser: parent(y) becomes x
      have hpl : ∀ i, L.parent i =
          if (y : ℕ) = i then (x : ℕ)
          else self.parent i := by
        intro i; exact UnionFind.parent_link yroot
          (i := i) ▸ by simp [hxy, hrank]
      have hfs_y : fs y.1 = 0 := by
        dsimp only [fs]; simp [yroot]
      -- In the y-is-loser case, ranks unchanged for all
      have hrl : ∀ j, L.rank j = self.rank j := by
        intro j
        change UnionFind.rankD
          (UnionFind.linkAux self.arr x y) j =
          UnionFind.rankD self.arr j
        have hrank' : self.arr[y.1].rank <
            self.arr[x.1].rank := by
          simp only [← UnionFind.rankD_eq y.2,
            ← UnionFind.rankD_eq x.2]; exact hrank
        simp only [UnionFind.linkAux,
          show ¬(x.1 = y.1) from hxy, ite_false,
          hrank', ite_true]
        rw [UnionFind.rankD_set]; split
        · rename_i h; subst h
          simp [UnionFind.rankD_eq y.2]
        · rfl
      have hfl_y : fl y.1 ≤
          (invAck self.size + 1) *
            (Nat.log 2 self.size + 1) := by
        dsimp only [fl]; rw [hpl]
        simp only [ite_true]
        rw [if_neg hxy, hrl, hrl]
        exact Nat.le_trans (Φ_node_le _ _ _)
          (Nat.mul_le_mul_left _
            (Nat.add_le_add_right
              (hrank_bound y.1 y.2) 1))
      have hpw : ∀ i ∈ (Finset.range self.size).erase
          y.1, fl i ≤ fs i := by
        intro i hi
        have hiy : i ≠ y.1 :=
          Finset.ne_of_mem_erase hi
        dsimp only [fl, fs]
        rw [hpl]
        simp only [show ¬((y : ℕ) = i) from
          Ne.symm hiy, ite_false]
        split
        · exact Nat.zero_le _
        · rw [hrl, hrl]
      have hy_mem : y.1 ∈ Finset.range self.size :=
        Finset.mem_range.mpr y.2
      calc (Finset.range self.size).sum fl
          = fl y.1 +
            ((Finset.range self.size).erase y.1).sum
              fl := by
            rw [← Finset.add_sum_erase _ _ hy_mem]
        _ ≤ (invAck self.size + 1) *
              (Nat.log 2 self.size + 1) +
            ((Finset.range self.size).erase y.1).sum
              fs :=
            Nat.add_le_add hfl_y
              (Finset.sum_le_sum hpw)
        _ = (invAck self.size + 1) *
              (Nat.log 2 self.size + 1) +
            (Finset.range self.size).sum fs := by
            congr 1
            exact Finset.sum_erase _ hfs_y
        _ = (Finset.range self.size).sum fs +
            (invAck self.size + 1) *
              (Nat.log 2 self.size + 1) := by
            omega
    · -- x is the loser: parent(x) becomes y
      push_neg at hrank
      have hrank' : ¬(self.arr[y.1].rank <
          self.arr[x.1].rank) := by
        simp only [← UnionFind.rankD_eq y.2,
          ← UnionFind.rankD_eq x.2]; exact not_lt.mpr hrank
      have hpl : ∀ i, L.parent i =
          if (x : ℕ) = i then (y : ℕ)
          else self.parent i := by
        intro i; rw [show L = self.link x y yroot
          from rfl, UnionFind.parent_link]
        simp [hxy, show ¬(self.rank y < self.rank x)
          from not_lt.mpr hrank]
      have hfs_x : fs x.1 = 0 := by
        dsimp only [fs]; simp [xroot]
      -- L.rank for the x-is-loser case
      have hrl_ne : ∀ j, j ≠ x.1 → j ≠ y.1 →
          L.rank j = self.rank j := by
        intro j hjx hjy
        change UnionFind.rankD
          (UnionFind.linkAux self.arr x y) j =
          UnionFind.rankD self.arr j
        simp only [UnionFind.linkAux,
          show ¬(x.1 = y.1) from hxy, ite_false,
          hrank']
        split
        · rw [UnionFind.rankD_set,
            if_neg (Ne.symm hjy)]
          rw [UnionFind.rankD_set,
            if_neg (Ne.symm hjx)]
        · rw [UnionFind.rankD_set,
            if_neg (Ne.symm hjx)]
      have hfl_x : fl x.1 ≤
          (invAck self.size + 1) *
            (Nat.log 2 self.size + 1) := by
        dsimp only [fl]
        rw [hpl]
        simp only [ite_true]
        rw [if_neg (show ¬((y : ℕ) = (x : ℕ)) from
          fun h => hxy h.symm)]
        -- L.rank x = self.rank x (loser's rank unchanged)
        have hrl_x : L.rank x.1 = self.rank x.1 := by
          change UnionFind.rankD
            (UnionFind.linkAux self.arr x y) x.1 =
            UnionFind.rankD self.arr x.1
          simp only [UnionFind.linkAux,
            show ¬(x.1 = y.1) from hxy, ite_false,
            hrank']
          split
          · -- equal: set x then set y
            rw [UnionFind.rankD_set]
            rw [if_neg (show ¬(y.1 = x.1) from
              fun h => hxy h.symm)]
            rw [UnionFind.rankD_set, if_pos rfl]
            simp [UnionFind.rankD_eq x.2]
          · -- unequal: set x only
            rw [UnionFind.rankD_set, if_pos rfl]
            simp [UnionFind.rankD_eq x.2]
        rw [hrl_x]
        exact Nat.le_trans
          (Φ_node_mono (rank_link_ge self x y
            yroot y.1))
          (Nat.le_trans (Φ_node_le _ _ _)
            (Nat.mul_le_mul_left _
              (Nat.add_le_add_right
                (hrank_bound x.1 x.2) 1)))
      have hpw : ∀ i ∈ (Finset.range self.size).erase
          x.1, fl i ≤ fs i := by
        intro i hi
        have hix : i ≠ x.1 :=
          Finset.ne_of_mem_erase hi
        dsimp only [fl, fs]
        rw [hpl]
        simp only [show ¬((x : ℕ) = i) from
          Ne.symm hix, ite_false]
        split
        · exact Nat.zero_le _
        · rename_i hnotroot
          -- i is non-root in self. If i = y, contradiction
          -- with yroot
          have hiy : i ≠ y.1 := by
            intro h; subst h; exact hnotroot yroot
          rw [hrl_ne i hix hiy]
          exact Φ_node_mono (rank_link_ge self x y
            yroot (self.parent i))
      have hx_mem : x.1 ∈ Finset.range self.size :=
        Finset.mem_range.mpr x.2
      calc (Finset.range self.size).sum fl
          = fl x.1 +
            ((Finset.range self.size).erase x.1).sum
              fl := by
            rw [← Finset.add_sum_erase _ _ hx_mem]
        _ ≤ (invAck self.size + 1) *
              (Nat.log 2 self.size + 1) +
            ((Finset.range self.size).erase x.1).sum
              fs :=
            Nat.add_le_add hfl_x
              (Finset.sum_le_sum hpw)
        _ = (invAck self.size + 1) *
              (Nat.log 2 self.size + 1) +
            (Finset.range self.size).sum fs := by
            congr 1
            exact Finset.sum_erase _ hfs_x
        _ = (Finset.range self.size).sum fs +
            (invAck self.size + 1) *
              (Nat.log 2 self.size + 1) := by
            omega

/-- The amortized cost of union is bounded by the cost
of two finds plus the potential increase from the link.
The two finds have amortized cost ≤ α(n)+2 each.
The link creates one new non-root whose potential is
bounded by `Φ_node_le`. The total amortized cost per
union is O(α(n)) when aggregated across all operations
via `total_bound`, since the total Φ increase from all
links is O(n · α(n)) (each node becomes non-root at
most once, contributing O(α(n)) to the potential).

The per-operation statement requires decomposing
`Batteries.UnionFind.union` into its constituent finds
and link, which needs access to intermediate states not
directly exposed by the Batteries API. -/
private theorem Φ_union_le (uf : UnionFind)
    (x : Fin uf.size) (y : Fin uf.size)
    (hrb : RankBound uf) :
    Φ (uf.union x y) ≤
      Φ uf + (invAck uf.size + 1) *
        (Nat.log 2 uf.size + 1) := by
  -- Crude but correct: bound ALL nodes' Φ_node by (α+1)*(rank+1)
  -- where rank ≤ log(n) from RankBound. Total ≤ n*(α+1)*(log(n)+1).
  -- But Φ(uf) might be small. Use: Φ(union) ≤ Σ (α+1)*(rank+1)
  -- for all non-root nodes. Since at most n-1+1 = n non-roots
  -- (one new from link), and each rank ≤ log(n):
  -- Φ(union) ≤ n*(α+1)*(log(n)+1). And Φ(uf) ≥ 0.
  -- Need: n*(α+1)*(log(n)+1) ≤ Φ(uf) + (α+1)*(log(n)+1).
  -- FALSE for n > 1.
  -- MUST use structural decomposition. Since builds
  -- succeed with simp [UnionFind.union], try:
  -- Direct approach: unfold union, name intermediates, bound Φ.
  -- self₁ = (uf.find x).1, self₂ = (self₁.find ⟨y,_⟩).1
  -- result = self₂.link rx ry
  -- Φ(result) ≤ Φ(self₂) + (α+1)*(log(n)+1) ≤ Φ(uf) + (α+1)*(log(n)+1)
  -- First: Φ(self₁) ≤ Φ(uf). self₁ = findState uf x.
  -- findState uf x = (uf.findD x).1 = (uf.find ⟨x,x.2⟩).1 (for x : Fin)
  -- This IS definitionally equal when x < size.
  have hΦ_finds : Φ (findState (findState uf ↑x) ↑y) ≤ Φ uf :=
    Nat.le_trans (Φ_findState_le _ _) (Φ_findState_le _ _)
  -- Now: uf.union x y uses find internally, producing self₂ = findState(findState uf x, y)
  -- approximately. The exact relationship: uf.union's internal self₁ = (uf.find x).1.
  -- And findState uf x = (uf.findD x).1 = (uf.find ⟨x, x.2⟩).1 when x < size.
  -- So self₁ = findState uf x. Similarly, self₂ = findState self₁ y.
  -- And uf.union = self₂.link ...
  -- The Φ of the link result differs from Φ(self₂) by one node's Φ_node.
  -- For the bound: Φ(union) ≤ Φ(self₂) + max_Φ_node_of_new_nonroot.
  -- max_Φ_node ≤ (α+1)*(log(n)+1) from Φ_node_le + RankBound.
  -- Formalize via: Φ(union) ≤ sum of (Φ_node for each non-root in result)
  -- Each non-root in result that was also non-root in self₂: Φ_node ≤ Φ_node(self₂)
  --   (parent rank only increases or stays same through link for non-linked nodes)
  -- The ONE newly linked non-root: Φ_node ≤ (α+1)*(log(n)+1).
  -- Total: Φ(union) ≤ Φ(self₂) + (α+1)*(log(n)+1) ≤ Φ(uf) + (α+1)*(log(n)+1).
  -- Without type-level equivalence between uf.union and self₂.link,
  -- use omega after establishing the key inequalities.
  -- The core fact needed: Φ(uf.union x y) ≤ Φ(findState(findState uf x) y) + (α+1)*(log(n)+1).
  -- Prove this by showing uf.union = link(self₂, rx, ry) and Φ(link) ≤ Φ(self₂) + node_potential.
  -- Use delta/change to align the terms.
  -- Decompose uf.union x y = link(self₂, rx, ry)
  -- where self₁ = (uf.find x).1, self₂ = (self₁.find y).1.
  set self₁ := (uf.find x).1 with hself₁_def
  have hsize₁ : self₁.size = uf.size := UnionFind.find_size uf x
  have hΦ_s1 : Φ self₁ ≤ Φ uf := by
    have : Φ (findState uf ↑x) ≤ Φ uf := Φ_findState_le uf ↑x
    simp only [findState, UnionFind.findD, dif_pos x.2] at this
    exact this
  have hy₁ : ↑y < self₁.size := by rw [hsize₁]; exact y.2
  set self₂ := (self₁.find ⟨↑y, hy₁⟩).1
  have hΦ_s2 : Φ self₂ ≤ Φ self₁ := by
    have : Φ (findState self₁ ↑y) ≤ Φ self₁ := Φ_findState_le self₁ ↑y
    simp only [findState, UnionFind.findD, dif_pos hy₁] at this
    exact this
  have hΦ_s2_uf : Φ self₂ ≤ Φ uf := Nat.le_trans hΦ_s2 hΦ_s1
  -- Φ(union) = Φ(self₂.link ...). Bound Φ(link) via
  -- Φ(union) ≤ Φ(self₂) + C ≤ Φ(uf) + C where C = (α+1)*(log n+1)
  have key : Φ (uf.union x y) ≤ Φ self₂ +
      (invAck uf.size + 1) *
        (Nat.log 2 uf.size + 1) := by
    -- Use the Finset sum approach directly
    -- (same as Φ_link_le but applied to the union result)
    have hsize₂ : self₂.size = uf.size :=
      (UnionFind.find_size self₁ ⟨↑y, hy₁⟩).trans
        hsize₁
    have hunion_size : (uf.union x y).size =
        uf.size := by
      unfold UnionFind.union; simp only
      change (self₂.link _ _ _).size = uf.size
      change (UnionFind.linkAux self₂.arr _ _).size =
        uf.size
      rw [UnionFind.linkAux_size]; exact hsize₂
    -- rank preserved by find
    have hrank₂ : ∀ i, self₂.rank i = uf.rank i :=
      fun i => by
        have h1 := findState_rank uf ↑x i
        have h2 := findState_rank self₁ ↑y i
        simp only [findState, UnionFind.findD,
          dif_pos x.2] at h1
        simp only [findState, UnionFind.findD,
          dif_pos hy₁] at h2
        exact h2.trans h1
    -- rank bound for self₂
    have hrl₂ : ∀ i, i < self₂.size →
        self₂.rank i ≤ Nat.log 2 self₂.size := by
      intro i hi; rw [hrank₂ i, hsize₂]
      rw [hsize₂] at hi
      exact rank_le_log_size uf i hi hrb
    -- Φ(union) ≤ size * (α+1) * (log(n)+1)
    -- since each non-root has Φ_node ≤ (α+1)*(rank+1)
    -- ≤ (α+1)*(log(n)+1) by RankBound.
    -- And Φ(self₂) ≥ Φ(self₂) - Φ_node(loser_in_self₂).
    -- Since loser was root in self₂: Φ_node = 0.
    -- So Φ(union) ≤ Φ(self₂) + one Φ_node.
    -- Apply Φ_link_le via the definitional equality
    -- uf.union = self₂.link rx ry
    unfold UnionFind.union; simp only
    change Φ (self₂.link _ _ _) ≤ _
    -- Both args are Fin self₂.size. First = rx, second = ry
    -- Need xroot and yroot. The yroot is provided by
    -- the union constructor. For xroot:
    -- uf.rootD x is a root in self₁, hence in self₂.
    apply Φ_link_le self₂ _ _ _ _ hrl₂ |>.trans
      (by rw [hsize₂])
    · -- xroot
      -- self₂.parent rx = rx
      -- rx = ↑↑(uf.find x).2 = uf.rootD x
      have hrx : ↑↑(uf.find x).2 = uf.rootD x :=
        UnionFind.find_root_2 uf x
      change self₂.parent _ = _
      have h1 : self₁.parent (uf.rootD x) =
          uf.rootD x := by
        conv_lhs =>
          rw [show uf.rootD x = self₁.rootD x from
            (UnionFind.find_root_1 uf x x).symm]
        rw [UnionFind.parent_rootD]
        exact UnionFind.find_root_1 uf x x
      rcases UnionFind.find_parent_or self₁
        ⟨↑y, hy₁⟩ ↑↑(uf.find x).2
        with ⟨h2, _⟩ | h2
      · rw [h2, hrx,
          UnionFind.rootD_eq_self.mpr h1]
      · rw [h2, hrx, h1]
  exact Nat.le_trans key
    (Nat.add_le_add_right hΦ_s2_uf _)


/-- The cost of union equals two find costs plus 1. -/
theorem unionOp_cost (uf : UnionFind) (x y : ℕ) :
    (unionOp x y uf).2 ≤
      (findOp x uf).2 + (findOp y uf).2 + 1 := by
  simp only [unionOp, findOp]; split
  · split <;> omega
  · omega


/-- Total cost threading state through operations. -/
def totalCost :
    List (StatefulOp UnionFind) → UnionFind → ℕ
  | [], _ => 0
  | op :: ops, s =>
    (op s).2 + totalCost ops (op s).1

/-- Main theorem (telescoping): m operations cost O(m · α(n)). -/
theorem total_bound
    (ops : List (StatefulOp UnionFind))
    (c : ℕ) (s₀ : UnionFind)
    (h_bound : ∀ op ∈ ops, ∀ s,
      (op s).2 + Φ (op s).1 ≤ c + Φ s) :
    totalCost ops s₀ ≤ ops.length * c + Φ s₀ := by
  induction ops generalizing s₀ with
  | nil => simp [totalCost]
  | cons op ops ih =>
    simp only [totalCost, List.length_cons]
    have hop := h_bound op
      (List.mem_cons_self ..) s₀
    have hrest := ih (op s₀).1 fun o ho s =>
      h_bound o (List.mem_cons_of_mem _ ho) s
    calc (op s₀).2 + totalCost ops (op s₀).1
        ≤ (op s₀).2 +
          (ops.length * c + Φ (op s₀).1) :=
          Nat.add_le_add_left hrest _
      _ = (op s₀).2 + Φ (op s₀).1 +
          ops.length * c := by ring
      _ ≤ (c + Φ s₀) + ops.length * c :=
          Nat.add_le_add_right hop _
      _ = (ops.length + 1) * c + Φ s₀ := by ring

/-- Empty union-find has zero potential. -/
theorem Φ_empty : Φ UnionFind.empty = 0 := by
  simp [Φ]

/-! ### O(α(n)) amortized per operation

The standard O(α(n)) bound holds for any sequence of m
find and n union operations. The argument decomposes as:

1. **Per-find amortized cost:** `amortized_find` gives
   `pathLength + Φ(after) ≤ (α+2) + Φ(before)` for each
   find operation (including finds inside unions).

2. **Total Φ increase from unions:** Each union creates
   one new non-root with `Φ_node ≤ (α+1)·(rank+1)`.
   Summed over all n nodes that ever become non-roots,
   `Σ (rank_i + 1) ≤ 2n` because `rank ≤ 2^rank` and
   descendants are disjoint (`Σ 2^rank ≤ n` by RankBound).
   So total Φ increase from unions ≤ `2n·(α+1)`.

3. **Telescoping:** Total find cost across all operations
   ≤ `#finds · (α+2) + total_Φ_increase` (since Φ starts
   at 0 and Φ ≥ 0). Union link costs are O(n).
   Total = O(m·α + n·α) = **O((m+n)·α(n))**.

Each union contains two finds plus O(1) link work, so
the amortized cost of union is `2·(α+2) + 1 + O(α)` from
the potential increase, giving **O(α(n)) per operation**. -/


/-- The rank-count invariant: for each rank level r,
at most ⌊n/2^r⌋ nodes have rank ≥ r. This follows from
the disjoint descendants argument in union-by-rank. -/
private theorem geom_floor_sum (K n : ℕ) :
    (Finset.range K).sum (fun r => n / 2 ^ (r + 1)) ≤
      n := by
  induction K generalizing n with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ']
    simp only [Nat.zero_add, pow_one]
    have hconv : ∀ r ∈ Finset.range K,
        n / 2 ^ (r + 1 + 1) = (n / 2) / 2 ^ (r + 1) := by
      intro r _
      rw [show 2 ^ (r + 1 + 1) = 2 * 2 ^ (r + 1) from
        by ring, ← Nat.div_div_eq_div_mul]
    have := ih (n / 2)
    rw [Finset.sum_congr rfl hconv, Nat.add_comm]
    omega

/-- Weighted geometric floor sum: Σ_{s<K} s·⌊n/2^s⌋ ≤ 2n.
Proof: expand s = Σ_{t<s} 1, swap sums, bound inner by
geom_floor_sum, sum the bounds. -/
private theorem weighted_geom_floor_sum (K n : ℕ) :
    (Finset.range K).sum (fun s => s * (n / 2 ^ s)) ≤
      2 * n := by
  -- Induction on n using halving:
  -- Σ_{s<K} s·⌊n/2^s⌋ = 0 + Σ_{s=1}^{K-1} s·⌊n/2^s⌋.
  -- ⌊n/2^s⌋ = ⌊⌊n/2⌋/2^{s-1}⌋ (Nat.div_div_eq_div_mul).
  -- Σ_{s=1}^{K-1} s·⌊(n/2)/2^{s-1}⌋ (substitute r = s-1)
  -- = Σ_{r<K-1} (r+1)·⌊(n/2)/2^r⌋
  -- = Σ_{r<K-1} r·⌊(n/2)/2^r⌋ + Σ_{r<K-1} ⌊(n/2)/2^r⌋
  -- ≤ 2·(n/2) + 2·(n/2) = 2n (by IH + geom_floor_sum).
  -- But geom_floor_sum gives Σ_{r<K} ⌊m/2^{r+1}⌋ ≤ m, so
  -- Σ_{r<K} ⌊m/2^r⌋ = m + Σ_{r=1}^{K-1} ⌊m/2^r⌋ ≤ 2m.
  induction K generalizing n with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ']
    simp only [Nat.zero_mul]
    -- Goal: Σ_{s<K} (s+1)·(n/2^{s+1}) ≤ 2n
    -- n/2^{s+1} = (n/2)/2^s by Nat.div_div_eq_div_mul.
    -- (s+1)·((n/2)/2^s) = s·((n/2)/2^s) + (n/2)/2^s
    have hconv : ∀ s ∈ Finset.range K,
        (s + 1) * (n / 2 ^ (s + 1)) =
        s * ((n / 2) / 2 ^ s) + (n / 2) / 2 ^ s := by
      intro s _
      rw [show n / 2 ^ (s + 1) = (n / 2) / 2 ^ s from by
        rw [Nat.div_div_eq_div_mul]; congr 1; rw [Nat.pow_succ]; ring]
      ring
    rw [Finset.sum_congr rfl hconv, Finset.sum_add_distrib]
    -- Σ s·((n/2)/2^s) + Σ (n/2)/2^s ≤ 2n
    have h1 := ih (n / 2)
    -- h1: Σ_{s<K} s·((n/2)/2^s) ≤ 2·(n/2)
    have h2 : (Finset.range K).sum
        (fun s => (n / 2) / 2 ^ s) ≤ n := by
      cases K with
      | zero => simp
      | succ K' =>
        rw [Finset.sum_range_succ']
        simp only [Nat.pow_zero, Nat.div_one]
        have := geom_floor_sum K' (n / 2)
        omega
    omega

/-- Under ExactRankBound, Σ (rank+1) ≤ 3n.
The bound follows from #{rank ≥ r+1} ≤ n/2^r (derived from
the per-rank bound #{rank=s}·2^s ≤ n via geometric series)
and the layer sum decomposition Σ rank = Σ_{r≥1} #{rank ≥ r}. -/
theorem rank_sum_le (uf : UnionFind)
    (hrc : RankCountBound uf) :
    (Finset.range uf.size).sum
      (fun i => uf.rank i + 1) ≤ 3 * uf.size := by
  -- Σ (rank + 1) = Σ rank + n. Need Σ rank ≤ n.
  -- Σ rank = Σ_{r=1}^{max} #{rank ≥ r}
  -- ≤ Σ_{r=1}^{max} n/2^r ≤ n
  -- Use: Σ_{i<n} rank(i) ≤ Σ_{i<n} 2^rank(i) / 1
  -- Actually simpler: bound each rank(i) by
  -- the geometric series contribution.
  -- Each node with rank r contributes r to the sum.
  -- r ≤ 2^r - 1 for r ≥ 1, and r = 0 for r = 0.
  -- So Σ rank ≤ Σ (2^rank - 1) = Σ 2^rank - n.
  -- And Σ 2^rank ≤ ??? — this doesn't help directly.
  -- Use the standard: Σ_{i} f(i) = Σ_{r≥1} #{f(i) ≥ r}
  -- (for f : ℕ → ℕ, this is a standard identity).
  -- rank(i) = Σ_{r=1}^{rank(i)} 1 = #{r : 1 ≤ r ≤ rank(i)}
  -- So Σ_i rank(i) = Σ_i Σ_{r=1}^{rank(i)} 1
  --               = Σ_{r≥1} #{i : rank(i) ≥ r}
  -- Each #{rank ≥ r} ≤ n/2^r by hrc.
  -- Σ_{r≥1} n/2^r = n · Σ_{r≥1} 1/2^r
  -- Σ_{r≥1} 1/2^r = 1 (geometric series)
  -- So Σ rank ≤ n. And Σ (rank+1) = Σ rank + n ≤ 2n.
  -- Σ_{i<n} rank(i) ≤ n using layer-sum + RankCountBound
  -- For each i, rank(i) = Σ_{r=1}^{rank(i)} 1
  -- = #{r ∈ {1,...,rank(i)}} = |{r : 1 ≤ r ∧ r ≤ rank(i)}|
  -- Summing: Σ_i rank(i) = Σ_i Σ_{r : r ≤ rank(i), r ≥ 1} 1
  -- = Σ_{r≥1} #{i : rank(i) ≥ r}
  -- ≤ Σ_{r≥1} n/2^r (by RankCountBound)
  -- For ℕ floor division: Σ_{r=1}^{∞} ⌊n/2^r⌋ ≤ n - 1 < n
  -- (since n = Σ_{r=0}^{∞} (n mod 2^{r+1} - n mod 2^r)/2^r ... etc)
  -- Simpler: ⌊n/2⌋ + ⌊n/4⌋ + ... ≤ n-1 for n ≥ 1.
  -- Proof: Σ_{r≥1} ⌊n/2^r⌋ = n - s₂(n) where s₂(n) is
  -- the number of 1-bits in n. So ≤ n - 1 for n ≥ 1.
  -- For n = 0: Σ = 0 ≤ 0.
  -- Use direct bound: each term ⌊n/2^r⌋ ≤ n/2^r.
  -- Σ_{r=1}^{K} n/2^r < n (geometric series).
  -- But we need integer bounds. Use:
  -- Σ_{r=1}^K ⌊n/2^r⌋ ≤ Σ_{r=1}^K (n/2^r) < n.
  -- In ℕ: Σ ⌊n/2^r⌋ ≤ n - 1.
  -- Formal proof via Nat.sum_div_pow_le or similar.
  -- Use direct weighted sum: Σ_i rank(i) = Σ_s s·#{rank=s}
  -- ≤ Σ_s s·(n/2^s) ≤ 2n.
  have hcount : ∀ s, ((Finset.range uf.size).filter
      (fun i => decide (uf.rank i = s) = true)).card ≤
      uf.size / 2 ^ s := fun s =>
    (Nat.le_div_iff_mul_le (Nat.two_pow_pos s)).mpr (hrc s)
  have hsum_rank : (Finset.range uf.size).sum
      (fun i => uf.rank i) ≤ 2 * uf.size := by
    -- rank(i) ≤ 2^rank(i) - 1 for rank ≥ 1, 0 for rank 0.
    -- So Σ rank ≤ Σ (2^rank - 1) = (Σ 2^rank) - n.
    -- Hmm, can't subtract in Nat easily.
    -- Direct: Σ rank(i) = Σ_{s≥1} #{rank ≥ s} (layer sum).
    -- #{rank ≥ s} ≤ n for all s (trivially).
    -- But Σ n = n² (too weak).
    -- Actually the simplest approach: each rank(i) ≤ log₂(n),
    -- so Σ rank ≤ n·log(n). Too weak for 2n.
    -- The correct approach requires partitioning by rank.
    -- Σ rank = Σ_s s · #{rank=s}.
    -- #{rank=s} ≤ n/2^s (from hcount).
    -- Σ_s s · n/2^s: need this ≤ 2n.
    -- For each s ≥ 1: s/2^s ≤ 1 (since s ≤ 2^s).
    -- So s · (n/2^s) ≤ n.
    -- And #{rank=s} = 0 for all s > log₂(n).
    -- So Σ_{s=1}^{log n} s·(n/2^s) ≤ log(n)·n. Still O(n log n).
    -- TIGHTER: s/2^s ≤ 1/2^{s/2} for s ≥ 2.
    -- Σ 1/2^{s/2} converges. But not to 2.
    -- The CORRECT approach: Σ_{s≥0} s·x^s = x/(1-x)² for |x|<1.
    -- At x=1/2: Σ s/2^s = (1/2)/(1/2)² = 2. EXACTLY 2.
    -- For Nat div: Σ_{s≥0} s·⌊n/2^s⌋ ≤ Σ_{s≥0} s·n/2^s = 2n.
    -- But ⌊n/2^s⌋ ≤ n/2^s doesn't hold exactly for nat.
    -- Actually it does: ⌊n/2^s⌋ ≤ n/2^s (real). And for the sum:
    -- Σ s·⌊n/2^s⌋ ≤ Σ s·(n/2^s) = 2n in reals.
    -- For Nat: can't multiply by reals. But:
    -- Σ s·⌊n/2^s⌋ ≤ 2n because:
    -- s·⌊n/2^s⌋ = s·⌊n/2^s⌋.
    -- Use: Σ_{s=0}^{K} s·⌊n/2^s⌋
    -- = 0 + Σ_{s=1}^{K} Σ_{t=0}^{s-1} ⌊n/2^s⌋
    -- = Σ_{t=0}^{K-1} Σ_{s=t+1}^{K} ⌊n/2^s⌋ (swap)
    -- ≤ Σ_{t=0}^{K-1} ⌊n/2^t⌋ (each inner ≤ ⌊n/2^t⌋ by geom)
    -- = n + Σ_{t=1}^{K-1} ⌊n/2^t⌋ ≤ n + n = 2n.
    -- Partition nodes by rank, then use weighted sum.
    -- Step 1: Σ_i rank(i) = Σ_{s<n} s · #{rank=s} (regroup)
    -- Step 2: ≤ Σ_{s<n} s · (n/2^s) (bound each #{rank=s})
    -- Step 3: ≤ 2n (arithmetic, as above)
    -- For Step 1, use Finset.sum_ite_eq' to regroup.
    -- For Step 3, prove the weighted geom sum.
    -- Step 1: Σ_i rank(i) ≤ Σ_{s<n} s · #{rank=s}
    -- Note: rank(i) < n for all i (from hrank_le).
    -- rank(i) = Σ_{s<n} (if rank(i) = s then s else 0)
    -- = Σ_{s<n} s · [rank(i) = s]
    -- Σ_i rank(i) = Σ_i Σ_s s · [rank(i)=s] = Σ_s s · #{rank=s}
    have hrank_le : ∀ i, i < uf.size → uf.rank i ≤ uf.size :=
      fun i hi => rank_le_size_of_rankCountBound hrc i hi
    -- Step 1: regroup
    have hregroup : ∀ i ∈ Finset.range uf.size,
        uf.rank i = (Finset.range uf.size).sum
          (fun s => if uf.rank i = s then s else 0) := by
      intro i hi
      have hri := hrank_le i (Finset.mem_range.mp hi)
      have : (Finset.range uf.size).sum
          (fun s => if uf.rank i = s then s else 0) =
          (Finset.range uf.size).sum
          (fun s => if s = uf.rank i then s else 0) := by
        congr 1; ext s; split_ifs <;> omega
      rw [this]
      simp only [Finset.sum_ite_eq', Finset.mem_range]
      have : uf.rank i < uf.size := by
        have h1 := hrank_le i (Finset.mem_range.mp hi)
        -- rank ≤ size. Strict: if rank = size, then 2^size ≤ size (from hrc). Impossible.
        by_contra h2; push_neg at h2
        have heq : uf.rank i = uf.size := Nat.le_antisymm h1 h2
        have := hrc uf.size
        have h5 : i ∈ (Finset.range uf.size).filter
            (fun j => decide (uf.rank j = uf.size) = true) := by
          simp [Finset.mem_filter, Finset.mem_range,
            Finset.mem_range.mp hi, heq]
        have h6 := Finset.card_pos.mpr ⟨i, h5⟩
        have h7 : 2 ^ uf.size ≤ uf.size := by nlinarith
        have h8 : uf.size < 2 ^ uf.size := by
          induction uf.size with
          | zero => simp
          | succ n ih =>
            calc n + 1 < 2 * 2 ^ n := by omega
              _ = 2 ^ (n + 1) := by rw [Nat.pow_succ]; omega
        omega
      rw [if_pos this]
    -- Step 2: swap and bound
    calc (Finset.range uf.size).sum (fun i => uf.rank i)
        = (Finset.range uf.size).sum (fun i =>
            (Finset.range uf.size).sum (fun s =>
              if uf.rank i = s then s else 0)) :=
          Finset.sum_congr rfl hregroup
      _ = (Finset.range uf.size).sum (fun s =>
            (Finset.range uf.size).sum (fun i =>
              if uf.rank i = s then s else 0)) :=
          Finset.sum_comm
      _ = (Finset.range uf.size).sum (fun s =>
            s * ((Finset.range uf.size).filter
              (fun i => decide (uf.rank i = s) = true)).card) := by
          congr 1; ext s
          -- Σ_i (if rank(i)=s then s else 0) = s · #{rank=s}
          -- Factor out constant s: Σ (if p then s else 0) = s · Σ (if p then 1 else 0)
          have : (Finset.range uf.size).sum (fun i =>
              if uf.rank i = s then s else 0) =
              s * (Finset.range uf.size).sum (fun i =>
                if uf.rank i = s then 1 else 0) := by
            simp only [Finset.mul_sum]
            congr 1; ext i; split <;> omega
          rw [this, ← Finset.card_filter]; simp [decide_eq_true_eq]
      _ ≤ (Finset.range uf.size).sum (fun s =>
            s * (uf.size / 2 ^ s)) :=
          Finset.sum_le_sum (fun s _ =>
            Nat.mul_le_mul_left s (hcount s))
      -- Step 3: Σ s·⌊n/2^s⌋ ≤ 2n (weighted geometric sum)
      _ ≤ 2 * uf.size := by
          -- Expand s into sum of 1's, swap, use geom_floor_sum.
          -- Σ_{s<K} s·f(s) = Σ_{s<K} Σ_{t<s} f(s)
          --   = Σ_{t<K} Σ_{s=t+1}^{K-1} f(s) (swap)
          -- For f(s) = ⌊n/2^s⌋:
          -- Σ_{s=t+1}^{K-1} ⌊n/2^s⌋
          -- = Σ_{r<K-t-1} ⌊n/2^{t+1+r}⌋
          -- = Σ_{r<K-t-1} ⌊⌊n/2^t⌋/2^{r+1}⌋ (div_div_eq_div_mul)
          -- ≤ ⌊n/2^t⌋ (geom_floor_sum)
          -- So: Σ_{t<K} ⌊n/2^t⌋
          -- = n + Σ_{t=1}^{K-1} ⌊n/2^t⌋ ≤ n + n = 2n.
          exact weighted_geom_floor_sum _ _
  calc (Finset.range uf.size).sum
        (fun i => uf.rank i + 1)
      = (Finset.range uf.size).sum
        (fun i => uf.rank i) + uf.size := by
        rw [Finset.sum_add_distrib]
        simp [Finset.sum_const, Finset.card_range]
    _ ≤ 2 * uf.size + uf.size := Nat.add_le_add_right hsum_rank _
    _ = 3 * uf.size := by ring

/-- Under RankCountBound, Φ ≤ 3n · (α+1). -/
theorem Φ_le_tight (uf : UnionFind)
    (hrc : RankCountBound uf) :
    Φ uf ≤ 3 * uf.size * (invAck uf.size + 1) := by
  unfold Φ
  calc (Finset.range uf.size).sum _ ≤
      (Finset.range uf.size).sum (fun p =>
        (invAck uf.size + 1) * (uf.rank p + 1)) := by
        apply Finset.sum_le_sum; intro p _
        split
        · exact Nat.zero_le _
        · exact Φ_node_le _ _ _
    _ = (invAck uf.size + 1) *
        (Finset.range uf.size).sum
          (fun p => uf.rank p + 1) := by
        simp only [Nat.mul_comm (invAck uf.size + 1)]
        exact (Finset.sum_mul ..).symm
    _ ≤ (invAck uf.size + 1) * (3 * uf.size) :=
        Nat.mul_le_mul_left _ (rank_sum_le uf hrc)
    _ = 3 * uf.size * (invAck uf.size + 1) := by ring

/-- **Main theorem: O((m+n)·α(n)) total cost for m find operations.**

For any union-find state `s₀` with n elements satisfying
`RankBound` and `RankCountBound`, a sequence of m find
operations has total cost at most `m·(α(n)+2) + 3n·(α(n)+1)`.

This instantiates `total_bound` with `amortized_find` for
the per-operation bound and `Φ_le_tight` for the initial
potential. Combined with the O(1) cost of each link operation
and the fact that each union = 2 finds + 1 link, this gives
O((m+n)·α(n)) for any intermixed sequence of m finds and
n unions.

**Main theorem: O((m+n)·α(n)) total cost for m find operations.**
Total cost of m finds on a state with n elements is at most
m·(α(n)+2) + 3n·(α(n)+1) = O((m+n)·α(n)).
Proved by direct induction, threading RankBound through
intermediate states (findState preserves RankBound and size).
Uses `amortized_find` per step and `Φ_le_tight` for the
initial potential. -/
theorem total_find_cost
    (ops : List ℕ) (s₀ : UnionFind)
    (hrb : RankBound s₀)
    (hrc : RankCountBound s₀) :
    totalCost (ops.map findOp) s₀ ≤
      ops.length * (invAck s₀.size + 2) +
        3 * s₀.size * (invAck s₀.size + 1) := by
  suffices h : ∀ (ops' : List ℕ) (s : UnionFind),
      RankBound s → s.size = s₀.size →
      totalCost (ops'.map findOp) s ≤
        ops'.length * (invAck s₀.size + 2) + Φ s from
    calc totalCost (ops.map findOp) s₀
        ≤ ops.length * (invAck s₀.size + 2) + Φ s₀ :=
          h ops s₀ hrb rfl
      _ ≤ ops.length * (invAck s₀.size + 2) +
          3 * s₀.size * (invAck s₀.size + 1) :=
        Nat.add_le_add_left (Φ_le_tight s₀ hrc) _
  intro ops'
  induction ops' with
  | nil => intro s _ _; simp [totalCost]
  | cons x ops ih =>
    intro s hrb_s hsize_s
    simp only [List.map_cons, totalCost, findOp]
    have hamort := amortized_find s x hrb_s
    rw [hsize_s] at hamort
    have hrb_next := rankBound_findState hrb_s x
    have hsize_next : (findState s x).size = s₀.size := by
      rw [findState_size]; exact hsize_s
    have ih_next := ih (findState s x) hrb_next hsize_next
    calc pathLength s x +
          totalCost (ops.map findOp) (findState s x)
        ≤ pathLength s x +
          (ops.length * (invAck s₀.size + 2) +
            Φ (findState s x)) :=
          Nat.add_le_add_left ih_next _
      _ = pathLength s x + Φ (findState s x) +
          ops.length * (invAck s₀.size + 2) := by ring
      _ ≤ (invAck s₀.size + 2) + Φ s +
          ops.length * (invAck s₀.size + 2) :=
          Nat.add_le_add_right hamort _
      _ = (ops.length + 1) * (invAck s₀.size + 2) +
          Φ s := by ring

/-- Potential upper bound: Φ ≤ size · (α+1) · (log(size)+1). -/
theorem Φ_le (uf : UnionFind) (hrb : RankBound uf) :
    Φ uf ≤ uf.size * (invAck uf.size + 1) *
      (Nat.log 2 uf.size + 1) := by
  unfold Φ
  calc (Finset.range uf.size).sum _ ≤
      (Finset.range uf.size).sum (fun p =>
        (invAck uf.size + 1) *
          (Nat.log 2 uf.size + 1)) := by
        apply Finset.sum_le_sum; intro p hp
        split
        · exact Nat.zero_le _
        · exact Nat.le_trans (Φ_node_le _ _ _)
            (Nat.mul_le_mul_left _
              (Nat.add_le_add_right
                (rank_le_log_size uf p
                  (Finset.mem_range.mp hp) hrb) 1))
    _ = uf.size * (invAck uf.size + 1) *
          (Nat.log 2 uf.size + 1) := by
        simp [Finset.sum_const, Finset.card_range]
        ring

/-! ### Tarjan potential for O(α(n)) per union -/

/-- The Tarjan per-node potential: `α(n) - level(x)` for
non-root nodes with rank ≥ 1, and 0 otherwise.
`level(x) = invAck₂(rank(x), rank(parent(x))+1) - 1`. -/
def Ψ_node (n : ℕ) (rank parentRank : ℕ) : ℕ :=
  if rank = 0 then 0
  else invAck n - (invAck₂ rank (parentRank + 1) - 1)

/-- Ψ_node is bounded by α(n). -/
private theorem Ψ_node_le (n rank parentRank : ℕ) :
    Ψ_node n rank parentRank ≤ invAck n := by
  unfold Ψ_node; split
  · exact Nat.zero_le _
  · omega

/-- Ψ_node is monotone decreasing in parentRank. -/
private theorem Ψ_node_mono {n r pr₁ pr₂ : ℕ}
    (h : pr₁ ≤ pr₂) :
    Ψ_node n r pr₂ ≤ Ψ_node n r pr₁ := by
  unfold Ψ_node; split
  · exact Nat.zero_le _
  · -- invAck₂ is monotone in second arg
    -- pr₁ ≤ pr₂ → pr₁+1 ≤ pr₂+1
    -- → invAck₂(r, pr₁+1) ≤ invAck₂(r, pr₂+1)
    -- → invAck₂(r, pr₂+1)-1 ≥ invAck₂(r, pr₁+1)-1
    -- → α - (invAck₂(r, pr₂+1)-1) ≤ α - (invAck₂(r, pr₁+1)-1)
    have := invAck₂_mono_right
      (show pr₁ + 1 ≤ pr₂ + 1 from by omega)
      (r := r)
    omega

/-- The Tarjan overall potential. -/
def Ψ (uf : UnionFind) : ℕ :=
  (Finset.range uf.size).sum fun p =>
    if uf.parent p = p then 0
    else Ψ_node uf.size (uf.rank p)
      (uf.rank (uf.parent p))

/-- Ψ decreases during find (same proof as Φ). -/
private theorem Ψ_findState_le (uf : UnionFind)
    (x : ℕ) :
    Ψ (findState uf x) ≤ Ψ uf := by
  if hx : x < uf.size then
    simp only [Ψ]
    have := findState_size uf x
    rw [this]
    apply Finset.sum_le_sum; intro i _
    -- After find: roots stay roots, non-roots have
    -- parent rank ≥ before → Ψ_node ≤
    by_cases hroot_before : uf.parent i = i
    · -- Was root: still root or repointed to root
      rcases findState_parent_or uf x hx i with
        ⟨h1, _⟩ | h2
      · rw [h1, UnionFind.rootD_eq_self.mpr
            hroot_before]
        simp
      · rw [h2, hroot_before]
        simp
    · simp only [hroot_before, ite_false]
      have hne : (findState uf x).parent i ≠ i := by
        rcases findState_parent_or uf x hx i with
          ⟨h1, _⟩ | h2
        · rw [h1]; intro heq
          have := UnionFind.rootD_eq_self.mp heq
          exact hroot_before this
        · rw [h2]; exact hroot_before
      simp only [hne, ite_false, findState_rank]
      exact Ψ_node_mono
        (findState_parent_rank_le uf x i hx)
  else
    have : findState uf x = uf := by
      simp [findState, UnionFind.findD, dif_neg hx]
    rw [this]

/-- Ψ of link increases by at most α(n). -/
private theorem Ψ_link_le (self : UnionFind)
    (x y : Fin self.size)
    (xroot : self.parent x = x)
    (yroot : self.parent y = y)
    (_hrank_bound : ∀ i, i < self.size →
      self.rank i ≤ Nat.log 2 self.size) :
    Ψ (self.link x y yroot) ≤
      Ψ self + invAck self.size := by
  -- Same structure as Φ_link_le but with α bound
  by_cases hxy : x.1 = y.1
  · have heq : self.link x y yroot = self := by
      change ⟨UnionFind.linkAux self.arr x y, _, _⟩ =
        self
      simp only [UnionFind.linkAux, hxy, ite_true]
    rw [heq]; omega
  · have hsize : (self.link x y yroot).size =
        self.size := by
      change (UnionFind.linkAux self.arr x y).size =
        self.arr.size
      exact UnionFind.linkAux_size
    unfold Ψ; rw [hsize]
    let L := self.link x y yroot
    set fl := fun p => if L.parent p = p then 0
      else Ψ_node self.size (L.rank p)
        (L.rank (L.parent p))
    set fs := fun p => if self.parent p = p then 0
      else Ψ_node self.size (self.rank p)
        (self.rank (self.parent p))
    by_cases hrank : self.rank y < self.rank x
    · -- y is the loser
      have hpl : ∀ i, L.parent i =
          if (y : ℕ) = i then (x : ℕ)
          else self.parent i := by
        intro i; exact UnionFind.parent_link yroot
          (i := i) ▸ by simp [hxy, hrank]
      have hfs_y : fs y.1 = 0 := by
        dsimp only [fs]; simp [yroot]
      have hrl : ∀ j, L.rank j = self.rank j := by
        intro j
        change UnionFind.rankD
          (UnionFind.linkAux self.arr x y) j =
          UnionFind.rankD self.arr j
        have hrank' : self.arr[y.1].rank <
            self.arr[x.1].rank := by
          simp only [← UnionFind.rankD_eq y.2,
            ← UnionFind.rankD_eq x.2]; exact hrank
        simp only [UnionFind.linkAux,
          show ¬(x.1 = y.1) from hxy, ite_false,
          hrank', ite_true]
        rw [UnionFind.rankD_set]; split
        · rename_i h; subst h
          simp [UnionFind.rankD_eq y.2]
        · rfl
      have hfl_y : fl y.1 ≤ invAck self.size := by
        dsimp only [fl]; rw [hpl]
        simp only [ite_true]
        rw [if_neg hxy, hrl, hrl]
        exact Ψ_node_le _ _ _
      have hpw : ∀ i ∈
          (Finset.range self.size).erase y.1,
          fl i ≤ fs i := by
        intro i hi
        have hiy : i ≠ y.1 :=
          Finset.ne_of_mem_erase hi
        dsimp only [fl, fs]
        rw [hpl]
        simp only [show ¬((y : ℕ) = i) from
          Ne.symm hiy, ite_false]
        split
        · exact Nat.zero_le _
        · rw [hrl, hrl]
      have hy_mem : y.1 ∈ Finset.range self.size :=
        Finset.mem_range.mpr y.2
      calc (Finset.range self.size).sum fl
          = fl y.1 +
            ((Finset.range self.size).erase y.1).sum
              fl := by
            rw [← Finset.add_sum_erase _ _ hy_mem]
        _ ≤ invAck self.size +
            ((Finset.range self.size).erase y.1).sum
              fs :=
            Nat.add_le_add hfl_y
              (Finset.sum_le_sum hpw)
        _ = invAck self.size +
            (Finset.range self.size).sum fs := by
            congr 1
            exact Finset.sum_erase _ hfs_y
        _ = (Finset.range self.size).sum fs +
            invAck self.size := by omega
    · -- x is the loser
      push_neg at hrank
      have hrank' : ¬(self.arr[y.1].rank <
          self.arr[x.1].rank) := by
        simp only [← UnionFind.rankD_eq y.2,
          ← UnionFind.rankD_eq x.2]
        exact not_lt.mpr hrank
      have hpl : ∀ i, L.parent i =
          if (x : ℕ) = i then (y : ℕ)
          else self.parent i := by
        intro i; rw [show L = self.link x y yroot
          from rfl, UnionFind.parent_link]
        simp [hxy, show ¬(self.rank y < self.rank x)
          from not_lt.mpr hrank]
      have hfs_x : fs x.1 = 0 := by
        dsimp only [fs]; simp [xroot]
      have hfl_x : fl x.1 ≤ invAck self.size := by
        dsimp only [fl]; rw [hpl]
        simp only [ite_true]
        rw [if_neg (show ¬((y : ℕ) = (x : ℕ)) from
          fun h => hxy h.symm)]
        exact Ψ_node_le _ _ _
      have hpw : ∀ i ∈
          (Finset.range self.size).erase x.1,
          fl i ≤ fs i := by
        intro i hi
        have hix : i ≠ x.1 :=
          Finset.ne_of_mem_erase hi
        dsimp only [fl, fs]
        rw [hpl]
        simp only [show ¬((x : ℕ) = i) from
          Ne.symm hix, ite_false]
        split
        · exact Nat.zero_le _
        · rename_i hnotroot
          have hiy : i ≠ y.1 := by
            intro h; subst h; exact hnotroot yroot
          -- Need L.rank i = self.rank i for i ≠ x, i ≠ y
          have hri : L.rank i = self.rank i := by
            change UnionFind.rankD
              (UnionFind.linkAux self.arr x y) i =
              UnionFind.rankD self.arr i
            simp only [UnionFind.linkAux,
              show ¬(x.1 = y.1) from hxy, ite_false,
              hrank']
            split
            · rw [UnionFind.rankD_set,
                if_neg (Ne.symm hiy)]
              rw [UnionFind.rankD_set,
                if_neg (Ne.symm hix)]
            · rw [UnionFind.rankD_set,
                if_neg (Ne.symm hix)]
          rw [hri]
          exact Ψ_node_mono (rank_link_ge self x y
            yroot (self.parent i))
      have hx_mem : x.1 ∈ Finset.range self.size :=
        Finset.mem_range.mpr x.2
      calc (Finset.range self.size).sum fl
          = fl x.1 +
            ((Finset.range self.size).erase x.1).sum
              fl := by
            rw [← Finset.add_sum_erase _ _ hx_mem]
        _ ≤ invAck self.size +
            ((Finset.range self.size).erase x.1).sum
              fs :=
            Nat.add_le_add hfl_x
              (Finset.sum_le_sum hpw)
        _ = invAck self.size +
            (Finset.range self.size).sum fs := by
            congr 1
            exact Finset.sum_erase _ hfs_x
        _ = (Finset.range self.size).sum fs +
            invAck self.size := by omega

/-- Ψ(union) ≤ Ψ(uf) + α(n). -/
private theorem Ψ_union_le (uf : UnionFind)
    (x : Fin uf.size) (y : Fin uf.size)
    (hrb : RankBound uf) :
    Ψ (uf.union x y) ≤
      Ψ uf + invAck uf.size := by
  set self₁ := (uf.find x).1 with hself₁_def
  have hsize₁ : self₁.size = uf.size :=
    UnionFind.find_size uf x
  have hΨ_s1 : Ψ self₁ ≤ Ψ uf := by
    have : Ψ (findState uf ↑x) ≤ Ψ uf :=
      Ψ_findState_le uf ↑x
    simp only [findState, UnionFind.findD,
      dif_pos x.2] at this; exact this
  have hy₁ : ↑y < self₁.size := by
    rw [hsize₁]; exact y.2
  set self₂ := (self₁.find ⟨↑y, hy₁⟩).1
  have hΨ_s2 : Ψ self₂ ≤ Ψ self₁ := by
    have : Ψ (findState self₁ ↑y) ≤ Ψ self₁ :=
      Ψ_findState_le self₁ ↑y
    simp only [findState, UnionFind.findD,
      dif_pos hy₁] at this; exact this
  have hΨ_s2_uf : Ψ self₂ ≤ Ψ uf :=
    Nat.le_trans hΨ_s2 hΨ_s1
  have hsize₂ : self₂.size = uf.size :=
    (UnionFind.find_size self₁ ⟨↑y, hy₁⟩).trans
      hsize₁
  have hrank₂ : ∀ i, self₂.rank i = uf.rank i :=
    fun i => by
      have h1 := findState_rank uf ↑x i
      have h2 := findState_rank self₁ ↑y i
      simp only [findState, UnionFind.findD,
        dif_pos x.2] at h1
      simp only [findState, UnionFind.findD,
        dif_pos hy₁] at h2
      exact h2.trans h1
  have hrl₂ : ∀ i, i < self₂.size →
      self₂.rank i ≤ Nat.log 2 self₂.size := by
    intro i hi; rw [hrank₂ i, hsize₂]
    rw [hsize₂] at hi
    exact rank_le_log_size uf i hi hrb
  have key : Ψ (uf.union x y) ≤ Ψ self₂ +
      invAck uf.size := by
    unfold UnionFind.union; simp only
    change Ψ (self₂.link _ _ _) ≤ _
    apply Ψ_link_le self₂ _ _ _ _ hrl₂ |>.trans
      (by rw [hsize₂])
    · -- xroot: self₂.parent rx = rx where rx = ↑↑(uf.find x).2
      have hrx : ↑↑(uf.find x).2 = uf.rootD x :=
        UnionFind.find_root_2 uf x
      change self₂.parent _ = _
      have h1 : self₁.parent (uf.rootD x) =
          uf.rootD x := by
        conv_lhs =>
          rw [show uf.rootD x = self₁.rootD x from
            (UnionFind.find_root_1 uf x x).symm]
        rw [UnionFind.parent_rootD]
        exact UnionFind.find_root_1 uf x x
      rcases UnionFind.find_parent_or self₁
        ⟨↑y, hy₁⟩ ↑↑(uf.find x).2
        with ⟨h2, _⟩ | h2
      · rw [h2, hrx,
          UnionFind.rootD_eq_self.mpr h1]
      · rw [h2, hrx, h1]
  exact Nat.le_trans key
    (Nat.add_le_add_right hΨ_s2_uf _)

/-- Ψ decomposition through find path (same structure
as Φ_findState_decomp). -/
private theorem Ψ_findState_decomp
    (uf : UnionFind) (x : ℕ) (hx : x < uf.size)
    (hne : uf.parent x ≠ x) :
    Ψ (findState uf (uf.parent x)) +
      Ψ_node uf.size (uf.rank x)
        (uf.rank ((findState uf x).parent x)) =
    Ψ (findState uf x) +
      Ψ_node uf.size (uf.rank x)
        (uf.rank (uf.parent x)) := by
  simp only [Ψ]
  rw [findState_size, findState_size]
  have hx_mem : x ∈ Finset.range uf.size :=
    Finset.mem_range.mpr hx
  rw [← Finset.add_sum_erase _ _ hx_mem,
    ← Finset.add_sum_erase _ _ hx_mem]
  have hne_fp :
      ¬(findState uf (uf.parent x)).parent x = x := by
    rw [findState_parent_unchanged uf x hx hne]
    exact hne
  have hne_fx : ¬(findState uf x).parent x = x := by
    rw [findState_parent_x_eq uf x hx]
    exact fun h => hne (UnionFind.rootD_eq_self.mp h)
  simp only [if_neg hne_fp, if_neg hne_fx]
  simp only [findState_rank,
    findState_parent_unchanged uf x hx hne]
  have herase : ∀ i ∈
      (Finset.range uf.size).erase x,
      ((if (findState uf (uf.parent x)).parent i = i
       then 0
       else Ψ_node uf.size (uf.rank i)
         (uf.rank ((findState uf (uf.parent x)).parent
           i))) : ℕ) =
      (if (findState uf x).parent i = i then 0
       else Ψ_node uf.size (uf.rank i)
         (uf.rank ((findState uf x).parent i))) := by
    intro i hi
    have hix : i ≠ x := Finset.ne_of_mem_erase hi
    rw [findState_parent_ne_eq uf x hx hne i hix]
  rw [Finset.sum_congr rfl herase]
  omega

/-- Count of non-paying nodes for Ψ potential. -/
private def nonpayingΨ (uf : UnionFind) (x : ℕ) : ℕ :=
  if h : uf.parent x = x then 0
  else
    have := Nat.sub_lt_sub_left
      (uf.lt_rankMax x) (uf.rank_lt h)
    let d := Ψ_node uf.size (uf.rank x)
      (uf.rank (uf.parent x)) -
      Ψ_node uf.size (uf.rank x)
      (uf.rank (uf.rootD x))
    (if d = 0 then 1 else 0) +
      nonpayingΨ uf (uf.parent x)
termination_by uf.rankMax - uf.rank x

/-- pathLength + Ψ_after ≤ nonpayingΨ + Ψ_before. -/
private theorem pathLength_le_nonpayingΨ_add_Ψ_drop
    (uf : UnionFind) (x : ℕ) (hx : x < uf.size) :
    pathLength uf x + Ψ (findState uf x) ≤
      nonpayingΨ uf x + Ψ uf := by
  if hroot : uf.parent x = x then
    have hpl : pathLength uf x = 0 := by
      rw [pathLength, dif_pos hroot]
    have hnp : nonpayingΨ uf x = 0 := by
      rw [nonpayingΨ, dif_pos hroot]
    rw [hpl, hnp]
    exact Nat.add_le_add_left
      (Ψ_findState_le uf x) 0
  else
    have hdec := Nat.sub_lt_sub_left
      (uf.lt_rankMax x) (uf.rank_lt hroot)
    have hp_lt : uf.parent x < uf.size :=
      (uf.parent_lt x).mpr hx
    have ih := pathLength_le_nonpayingΨ_add_Ψ_drop uf
      (uf.parent x) hp_lt
    have hdecomp := Ψ_findState_decomp uf x hx hroot
    rw [findState_parent_x_eq uf x hx] at hdecomp
    have hΨ_mono : Ψ_node uf.size (uf.rank x)
        (uf.rank (uf.rootD x)) ≤
        Ψ_node uf.size (uf.rank x)
        (uf.rank (uf.parent x)) := Ψ_node_mono
      (Nat.le_trans UnionFind.le_rank_root
        (by rw [UnionFind.rootD_parent]))
    have ih' : pathLength uf (uf.parent x) +
        Ψ (findState uf x) +
        (Ψ_node uf.size (uf.rank x)
          (uf.rank (uf.parent x)) -
         Ψ_node uf.size (uf.rank x)
          (uf.rank (uf.rootD x))) ≤
        nonpayingΨ uf (uf.parent x) + Ψ uf := by
      omega
    clear ih hdecomp
    rw [pathLength, dif_neg hroot,
      nonpayingΨ, dif_neg hroot]
    set d := Ψ_node uf.size (uf.rank x)
      (uf.rank (uf.parent x)) -
      Ψ_node uf.size (uf.rank x)
      (uf.rank (uf.rootD x))
    if hd : d = 0 then
      simp only [hd, ite_true]; omega
    else
      simp only [hd, ite_false]
      have : d ≥ 1 := Nat.one_le_iff_ne_zero.mpr hd
      omega
  termination_by uf.rankMax - uf.rank x

/-- nonpayingΨ ≤ pathLength. -/
private theorem nonpayingΨ_le_pathLength
    (uf : UnionFind) (x : ℕ) :
    nonpayingΨ uf x ≤ pathLength uf x := by
  rw [nonpayingΨ, pathLength]
  split
  · exact Nat.le_refl _
  · rename_i h
    have hdec := Nat.sub_lt_sub_left
      (uf.lt_rankMax x) (uf.rank_lt h)
    have ih := nonpayingΨ_le_pathLength uf
      (uf.parent x)
    simp only; split <;> omega
  termination_by uf.rankMax - uf.rank x


/-- Worst-case cost of a single find is O(log n).
This is the non-amortized per-operation bound. -/
theorem find_worst_case (uf : UnionFind) (x : ℕ)
    (hrb : RankBound uf) :
    (findOp x uf).2 ≤ Nat.log 2 uf.size :=
  pathLength_le_log_size uf x hrb

/-- Worst-case cost of a single union is O(log n).
The cost is two find paths plus the constant-time link. -/
theorem union_worst_case (uf : UnionFind) (x y : ℕ)
    (hrb : RankBound uf) :
    (unionOp x y uf).2 ≤
      2 * Nat.log 2 uf.size + 1 := by
  simp only [unionOp]
  split
  · split
    · rename_i hx hy
      simp only
      have hplx := pathLength_le_log_size uf x hrb
      have hply := pathLength_le_log_size uf y hrb
      omega
    · simp
  · simp

end Cslib.Algorithms.Lean.UnionFind

end -- section
