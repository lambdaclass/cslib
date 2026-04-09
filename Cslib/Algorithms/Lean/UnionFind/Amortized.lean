/-
Copyright (c) 2026 Juan Bono. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Bono
-/

module

public import Cslib.Algorithms.Lean.UnionFind.Operations
public import Cslib.Algorithms.Lean.UnionFind.Correctness
public import Cslib.Algorithms.Lean.UnionFind.Potential
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section

/-!
# Amortized Complexity of Union-Find

Proves that `m` find/union operations on `n` elements cost at most
`m * (3 * alpha(n) + 4)` total time, which is `O(m · α(n))`.

## Proof architecture

The proof uses Tarjan's potential method and is structured in five stages:

### Stage 1: Path compression preserves structure (§ Amortized cost of find, lines 45–97)

When `find` walks from `x` to its root and compresses the path, each node `x`
on the path gets a new parent (the root). We prove:

- `A_le_parent_of_le_level`: the Ackermann value `A k (rank x)` fits below the
  parent's rank whenever `k ≤ level(x)` — the defining property of `level`.
- `iter_value_le_parent`: the iterated Ackermann value at the `iter`-th step is
  still below the parent's rank — the defining property of `iter`.
- `find_preserves_parent_of_lt_rank`: `find` on a node `y` does not touch the
  parent pointer of any node whose rank is strictly below `rank(y)`. This is the
  key structural invariant that lets us reason about phi locally.

### Stage 2: Potential decrease from a single setParent (§ lines 98–377)

When path compression redirects `x` from its old parent to the root `r`, the
node potential `phi(x)` can only decrease (or stay the same). The argument has
two sub-cases depending on whether the *level* of `x` increases:

- `level_le_of_setParent_self`: the level never decreases, because the new
  parent's rank (`rank(r)`) is at least as large as the old parent's rank.
- `phi_setParent_self_le`: if the level stays the same, `iter` can only
  increase, so `phi` weakly decreases. If the level increases, the coefficient
  `(alpha − level)` shrinks, which more than compensates.
- `phi_setParent_self_drop`: under an *extra* condition (`hextra` — the next
  iterate of `A` at the current level still fits inside `rank(r)`), `phi`
  actually drops by **at least 1**. This is the mechanism that pays for the
  "same-level" interior nodes on the find path.

### Stage 3: Potential increase of link (§ Potential increase of link, lines 379–1011)

Linking two roots can *increase* the global potential Φ, but by at most
`alpha(n)`. The proof splits on the rank comparison:

- **Cases 1 & 2** (strict rank inequality): the attached root becomes a
  non-root, but `phi ≤ alpha(n) * rank` in both states, so Φ does not grow.
- **Case 3** (equal ranks): the winning root's rank increases by 1, adding
  exactly `alpha(n)` to its phi. Every other node's phi is unchanged or
  decreased (via `phi_le_of_parent_rank_le` / `phi_eq_of_same_data`).

This section also introduces the **findBudget** machinery:

- `findBudget(x)` = `interiorLevels(x).card + zeroBudget(x) + rootChildBudget(x)`,
  decomposing the find path from `x` to the root into three cost categories:
  - `interiorLevels`: the set of distinct level values seen at interior nodes
    (rank ≥ 1, parent not root) — bounded by `alpha(n)` since levels live
    in `{0, ..., alpha(n)−1}`.
  - `zeroBudget`: 1 if the path passes through a rank-0 node, else 0.
  - `rootChildBudget`: 1 if the path passes through a node whose parent is the
    root, else 0.
- `findBudget_le_alpha_add_two`: the total budget is at most `alpha(n) + 2`.

The crucial bridge lemma is `hextra_of_mem_interiorLevels`: when `level(x)`
already appears in `interiorLevels(parent(x))`, the witness node `y` deeper
in the path provides the `hextra` condition needed by `phi_setParent_self_drop`,
ensuring phi drops by ≥ 1.

### Stage 4: find_amortized via the budget bound (§ Proof of find_amortized)

The proof of `find_amortized` factors through a stronger inductive lemma
`find_Phi_le_budget`:

```
  find_time + Φ_after ≤ Φ_before + findBudget(x)
```

proved by well-founded induction on `rankMax − rank(x)` (matching `find`'s
recursion). Each recursive step costs 1 unit of actual time. We case-split:

| Node category       | Budget change | How the cost is paid             |
|----------------------|---------------|----------------------------------|
| Root (base case)     | 0             | No cost.                         |
| Rank 0               | +1            | Budget absorbs the 1 unit.       |
| Parent is root       | +1            | Budget absorbs the 1 unit.       |
| New level (interior) | +1            | Budget absorbs the 1 unit.       |
| Same level (interior)| 0             | `phi_setParent_self_drop` gives   |
|                      |               | `phi_after + 1 ≤ phi_before`,    |
|                      |               | so `Φ` drops by ≥ 1, paying.    |

Then `find_amortized` follows immediately:
```
  find_time + Φ_after ≤ Φ_before + findBudget(x) ≤ Φ_before + alpha(n) + 2
```

### Stage 5: Telescoping to the main theorem (§ Main theorem)

- `union_amortized`: union = two finds + one link, so its amortized cost is
  `≤ 2 * (alpha(n) + 2) + alpha(n) = 3 * alpha(n) + 4`.
- `runOps_amortized_from_init`: telescoping over a sequence of `m` operations:
  Σ actual_cost ≤ Σ amortized_cost = Σ (actual + ΔΦ) = total_actual + Φ_final − Φ_init.
  Since `Φ_init = 0` and `Φ_final ≥ 0`: total_actual ≤ `m * (3·alpha(n) + 4)`.
- `union_find_amortized`: the final result, using `Φ_init = 0` from `Phi_init`.

## References
- [CLRS] Chapter 19, Theorem 19.13
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.UnionFind

open Cslib.Algorithms.Lean.TimeM

variable {n : ℕ}

/-! ### Stage 1: Path compression preserves structure

These lemmas show that path compression does not disturb nodes of lower rank,
and establish the defining properties of `level` and `iter`. -/

-- find_amortized is proved below, after the findBudget infrastructure (Stage 4).

/-- The Ackermann value `A k (rank x)` fits below the parent's rank for all
`k ≤ level(x)`. This is the contrapositive of level's definition: level is the
first `k` where `A k (rank x)` *exceeds* the parent's rank. -/
private theorem A_le_parent_of_le_level (uf : UF n) (x : Fin n)
    (hx : ¬uf.isRoot x) (hr : 1 ≤ uf.rank x) {k : ℕ}
    (hk : k ≤ level uf x hx hr) :
    A k (uf.rank x) ≤ uf.rank (uf.parent x) := by
  have hfind_pos : 0 < Nat.find (exists_level uf x hx hr) := by
    rw [Nat.find_pos]
    have hlt := uf.rank_lt x (by rwa [UF.isRoot] at hx)
    simp [A_zero]
    omega
  have hk' : k < Nat.find (exists_level uf x hx hr) := by
    unfold level at hk
    omega
  have hmin := Nat.find_min (exists_level uf x hx hr) hk'
  simpa using Classical.not_not.mp hmin

/-- The iterated Ackermann value `A^iter(rank x)` is still below the parent's
rank. Dual to `A_le_parent_of_le_level`: iter is the first iteration count
where the *next* iterate exceeds the parent's rank. -/
private theorem iter_value_le_parent (uf : UF n) (x : Fin n)
    (hx : ¬uf.isRoot x) (hr : 1 ≤ uf.rank x) :
    iterFn (A (level uf x hx hr)) (iter uf x hx hr) (uf.rank x) ≤
      uf.rank (uf.parent x) := by
  unfold iter
  set I := Nat.find (exists_iter uf x hx hr) with hI
  have hI_pos : 0 < I := by
    rw [hI]
    exact one_le_iter uf x hx hr
  have hlt : I - 1 < I := Nat.sub_one_lt (Nat.ne_of_gt hI_pos)
  have hmin := Nat.find_min (exists_iter uf x hx hr) hlt
  have hvalue :
      iterFn (A (level uf x hx hr)) (I - 1 + 1) (uf.rank x) ≤ uf.rank (uf.parent x) := by
    exact Classical.not_not.mp hmin
  rw [Nat.sub_add_cancel (Nat.succ_le_of_lt hI_pos)] at hvalue
  simpa [hI] using hvalue

/-- `find` on node `y` does not change the parent of any node `z` with
`rank(z) < rank(y)`. Since `find` only performs `setParent` on nodes along the
path from `y` to its root, and all such nodes have rank ≥ rank(y), lower-rank
nodes are untouched. This is the key invariant that lets us reason about
`phi(x)` after `find(parent(x))`: since `rank(x) < rank(parent(x))`, node `x`
keeps its original parent. -/
private theorem find_preserves_parent_of_lt_rank (uf : UF n) (y z : Fin n)
    (hzy : uf.rank z < uf.rank y) :
    (⟪find uf y⟫).2.parent z = uf.parent z := by
  unfold find
  unfold findAux
  by_cases hy : uf.parent y = y
  · simp [hy]
  · have hzy' : uf.rank z < uf.rank (uf.parent y) := by
      exact Nat.lt_trans hzy (uf.rank_lt y hy)
    have ih := find_preserves_parent_of_lt_rank uf (uf.parent y) z hzy'
    have hzne : z ≠ y := by
      intro h
      subst h
      omega
    simpa [hy, hzne] using ih
termination_by uf.rankMax - uf.rank y
decreasing_by
  have h1 := uf.rank_lt y hy
  have h2 := uf.rank_le_max (uf.parent y)
  omega

/-! ### Stage 2: Potential decrease from a single setParent

When path compression redirects node `x` to a higher-rank target `r`, the node
potential `phi(x)` can only decrease. The argument splits on whether `level(x)`
increases:
- **Same level**: `iter(x)` can only increase (more iterations fit below the
  new, higher parent rank), so `phi = (α−level)·rank − iter` decreases.
- **Higher level**: the coefficient `(α−level)` shrinks by ≥ 1, which outweighs
  any change in `iter`, so `phi` decreases by at least `rank(x)`.

The "drop by 1" variant (`phi_setParent_self_drop`) additionally requires that
the *next* iterate of `A` at the old level fits inside `rank(r)`. This extra
condition is satisfied exactly when a deeper node on the find path shares the
same level, which is the situation handled in Stage 4 for "same-level interior
nodes". -/

/-- Level never decreases when parent rank increases: the set of `k` where
`A k (rank x) ≤ rank(parent)` can only grow, so `level = min failing k − 1`
can only increase. -/
private theorem level_le_of_setParent_self (uf : UF n) (x r : Fin n)
    (hx : ¬uf.isRoot x) (hr : 1 ≤ uf.rank x)
    (h_rank : uf.rank x < uf.rank r) (h_root : uf.rootOf x = r)
    (hpr : uf.rank (uf.parent x) ≤ uf.rank r)
    (hx' : ¬(uf.setParent x r h_rank h_root).isRoot x)
    (hr' : 1 ≤ (uf.setParent x r h_rank h_root).rank x) :
    level uf x hx hr ≤ level (uf.setParent x r h_rank h_root) x hx' hr' := by
  have hconv :
      ∀ k,
        (¬A k ((uf.setParent x r h_rank h_root).rank x) ≤
            (uf.setParent x r h_rank h_root).rank ((uf.setParent x r h_rank h_root).parent x)) →
        (¬A k (uf.rank x) ≤ uf.rank (uf.parent x)) := by
    intro k hk h
    apply hk
    simpa [UF.setParent] using le_trans h hpr
  have hfind_le :
      Nat.find (exists_level uf x hx hr) ≤
      Nat.find (exists_level (uf.setParent x r h_rank h_root) x hx' hr') := by
    exact Nat.find_mono hconv
  unfold level
  omega

private theorem iter_le_of_setParent_self_same_level (uf : UF n) (x r : Fin n)
    (hx : ¬uf.isRoot x) (hr : 1 ≤ uf.rank x)
    (h_rank : uf.rank x < uf.rank r) (h_root : uf.rootOf x = r)
    (hpr : uf.rank (uf.parent x) ≤ uf.rank r)
    (hx' : ¬(uf.setParent x r h_rank h_root).isRoot x)
    (hr' : 1 ≤ (uf.setParent x r h_rank h_root).rank x)
    (hlevel :
      level (uf.setParent x r h_rank h_root) x hx' hr' = level uf x hx hr) :
    iter uf x hx hr ≤ iter (uf.setParent x r h_rank h_root) x hx' hr' := by
  have hconv :
      ∀ i,
        (¬iterFn (A (level (uf.setParent x r h_rank h_root) x hx' hr')) (i + 1)
            ((uf.setParent x r h_rank h_root).rank x) ≤
          (uf.setParent x r h_rank h_root).rank ((uf.setParent x r h_rank h_root).parent x)) →
        (¬iterFn (A (level uf x hx hr)) (i + 1) (uf.rank x) ≤
          uf.rank (uf.parent x)) := by
    intro i hi h
    apply hi
    rw [hlevel]
    simp only [UF.setParent]
    exact le_trans h hpr
  unfold iter
  exact Nat.find_mono hconv

private theorem iter_succ_le_of_setParent_self_same_level (uf : UF n) (x r : Fin n)
    (hx : ¬uf.isRoot x) (hr : 1 ≤ uf.rank x)
    (h_rank : uf.rank x < uf.rank r) (h_root : uf.rootOf x = r)
    (hpr : uf.rank (uf.parent x) ≤ uf.rank r)
    (hx' : ¬(uf.setParent x r h_rank h_root).isRoot x)
    (hr' : 1 ≤ (uf.setParent x r h_rank h_root).rank x)
    (hlevel :
      level (uf.setParent x r h_rank h_root) x hx' hr' = level uf x hx hr)
    (hextra :
      iterFn (A (level uf x hx hr)) (iter uf x hx hr + 1) (uf.rank x) ≤ uf.rank r) :
    iter uf x hx hr + 1 ≤ iter (uf.setParent x r h_rank h_root) x hx' hr' := by
  have hold :
      ∀ m < iter uf x hx hr,
        iterFn (A (level uf x hx hr)) (m + 1) (uf.rank x) ≤ uf.rank (uf.parent x) := by
    intro m hm
    have hmin := Nat.find_min (exists_iter uf x hx hr) hm
    exact Classical.not_not.mp hmin
  unfold iter
  rw [Nat.succ_le_iff]
  rw [Nat.lt_find_iff]
  intro m hm
  rcases lt_or_eq_of_le hm with hm_lt | hm_eq
  · have hm_old := hold m hm_lt
    rw [hlevel]
    simp only [UF.setParent]
    exact not_not_intro (le_trans hm_old hpr)
  · rw [hm_eq, hlevel]
    simp only [UF.setParent]
    exact not_not_intro hextra

private theorem phi_lower_bound_of_positive_nonroot (uf : UF n) (x : Fin n)
    (hx : ¬uf.isRoot x) (hr : 1 ≤ uf.rank x)
    (hn : uf.rank (uf.parent x) < n) :
    (alpha n - level uf x hx hr - 1) * uf.rank x ≤ phi uf x := by
  have hiter_le_rank : iter uf x hx hr ≤ uf.rank x := iter_le_rank uf x hx hr
  have hlevel_lt : level uf x hx hr < alpha n := level_lt_alpha uf x hx hr hn
  have hr0 : uf.rank x ≠ 0 := by omega
  have hsub :
      (alpha n - level uf x hx hr - 1) * uf.rank x ≤
        (alpha n - level uf x hx hr) * uf.rank x - iter uf x hx hr := by
    set L := level uf x hx hr with hL
    set R := uf.rank x with hR
    set I := iter uf x hx hr with hI
    set aL := alpha n - L with haL
    have haL_pos : 1 ≤ aL := by omega
    have hIR : I ≤ R := by simpa [hR, hI] using hiter_le_rank
    have key : (aL - 1) * R + R = aL * R := by
      have : aL ≥ 1 := haL_pos
      cases haL' : aL with
      | zero => omega
      | succ a => simp [Nat.succ_mul]
    have h2 : (aL - 1) * R + I ≤ aL * R := by omega
    omega
  rw [phi]
  simp only [hx, hr0, dite_false]
  exact hsub

/-- **Weak decrease**: redirecting `x` to a higher-rank target `r` does not
increase `phi(x)`. The proof case-splits on whether `level` stays the same
(then `iter` grows, decreasing `phi`) or increases (then the `(α−level)`
coefficient shrinks enough to compensate). -/
private theorem phi_setParent_self_le (uf : UF n) (x r : Fin n)
    (hx : ¬uf.isRoot x) (hr : 1 ≤ uf.rank x)
    (h_rank : uf.rank x < uf.rank r) (h_root : uf.rootOf x = r)
    (hpr : uf.rank (uf.parent x) ≤ uf.rank r)
    (hnr : uf.rank r < n) :
    phi (uf.setParent x r h_rank h_root) x ≤ phi uf x := by
  have hne : x ≠ r := by
    intro h
    subst h
    omega
  have hx' : ¬(uf.setParent x r h_rank h_root).isRoot x := by
    rw [UF.isRoot, UF.setParent]
    simpa using hne.symm
  have hr' : 1 ≤ (uf.setParent x r h_rank h_root).rank x := by
    simpa [UF.setParent] using hr
  have hr0 : uf.rank x ≠ 0 := by omega
  have hr0' : (uf.setParent x r h_rank h_root).rank x ≠ 0 := by
    simpa [UF.setParent] using hr0
  have hlevel_le := level_le_of_setParent_self uf x r hx hr h_rank h_root hpr hx' hr'
  have hold_lt : uf.rank (uf.parent x) < n := lt_of_le_of_lt hpr hnr
  simp only [phi, hx, hx', hr0, hr0', dite_false]
  by_cases hlevel_eq :
      level (uf.setParent x r h_rank h_root) x hx' hr' = level uf x hx hr
  · have hiter_le :=
      iter_le_of_setParent_self_same_level uf x r hx hr h_rank h_root hpr hx' hr' hlevel_eq
    calc
      (alpha n - level (uf.setParent x r h_rank h_root) x hx' hr') *
            (uf.setParent x r h_rank h_root).rank x -
          iter (uf.setParent x r h_rank h_root) x hx' hr'
        = (alpha n - level uf x hx hr) * uf.rank x -
            iter (uf.setParent x r h_rank h_root) x hx' hr' := by
            rw [hlevel_eq]
            simp [UF.setParent]
      _ ≤ (alpha n - level uf x hx hr) * uf.rank x - iter uf x hx hr :=
        Nat.sub_le_sub_left hiter_le _
  · have hlevel_gt : level uf x hx hr + 1 ≤
        level (uf.setParent x r h_rank h_root) x hx' hr' := by
      omega
    have hiter'_ge : 1 ≤ iter (uf.setParent x r h_rank h_root) x hx' hr' := by
      exact one_le_iter (uf.setParent x r h_rank h_root) x hx' hr'
    have hphi_lb :
        (alpha n - level uf x hx hr - 1) * uf.rank x ≤
          (alpha n - level uf x hx hr) * uf.rank x - iter uf x hx hr := by
      simpa [phi, hx, hr0] using phi_lower_bound_of_positive_nonroot uf x hx hr hold_lt
    have h_alpha_sub :
        alpha n - level (uf.setParent x r h_rank h_root) x hx' hr' ≤
          alpha n - level uf x hx hr - 1 := by
      omega
    calc
      (alpha n - level (uf.setParent x r h_rank h_root) x hx' hr') *
            (uf.setParent x r h_rank h_root).rank x -
          iter (uf.setParent x r h_rank h_root) x hx' hr'
        ≤ (alpha n - level (uf.setParent x r h_rank h_root) x hx' hr') *
            (uf.setParent x r h_rank h_root).rank x := Nat.sub_le _ _
      _ ≤ (alpha n - level uf x hx hr - 1) *
            (uf.setParent x r h_rank h_root).rank x :=
          Nat.mul_le_mul_right _ h_alpha_sub
      _ = (alpha n - level uf x hx hr - 1) * uf.rank x := by
          simp [UF.setParent]
      _ ≤ (alpha n - level uf x hx hr) * uf.rank x - iter uf x hx hr := hphi_lb

/-- **Strict decrease**: under the `hextra` condition (the next iterate of `A`
at the current level fits inside `rank(r)`), `phi(x)` drops by **at least 1**.
Either the level stays and `iter` increases by ≥ 1, or the level jumps and the
coefficient drops by ≥ 1. Either way, `phi_after + 1 ≤ phi_before`.

The `hextra` condition is provided by `hextra_of_mem_interiorLevels` when a
deeper node on the find path shares the same level as `x`. -/
private theorem phi_setParent_self_drop (uf : UF n) (x r : Fin n)
    (hx : ¬uf.isRoot x) (hr : 1 ≤ uf.rank x)
    (h_rank : uf.rank x < uf.rank r) (h_root : uf.rootOf x = r)
    (hpr : uf.rank (uf.parent x) ≤ uf.rank r)
    (hnr : uf.rank r < n)
    (hextra :
      iterFn (A (level uf x hx hr)) (iter uf x hx hr + 1) (uf.rank x) ≤ uf.rank r) :
    phi (uf.setParent x r h_rank h_root) x + 1 ≤ phi uf x := by
  have hne : x ≠ r := by
    intro h
    subst h
    omega
  have hx' : ¬(uf.setParent x r h_rank h_root).isRoot x := by
    rw [UF.isRoot, UF.setParent]
    simpa using hne.symm
  have hr' : 1 ≤ (uf.setParent x r h_rank h_root).rank x := by
    simpa [UF.setParent] using hr
  have hr0 : uf.rank x ≠ 0 := by omega
  have hr0' : (uf.setParent x r h_rank h_root).rank x ≠ 0 := by
    simpa [UF.setParent] using hr0
  have hlevel_le := level_le_of_setParent_self uf x r hx hr h_rank h_root hpr hx' hr'
  have hold_lt : uf.rank (uf.parent x) < n := lt_of_le_of_lt hpr hnr
  simp only [phi, hx, hx', hr0, hr0', dite_false]
  by_cases hlevel_eq :
      level (uf.setParent x r h_rank h_root) x hx' hr' = level uf x hx hr
  · have hiter_succ :=
      iter_succ_le_of_setParent_self_same_level
        uf x r hx hr h_rank h_root hpr hx' hr' hlevel_eq hextra
    have hbase_nontrunc :
        iter uf x hx hr + 1 ≤ (alpha n - level uf x hx hr) * uf.rank x := by
      have hiter'_le_rank :
          iter (uf.setParent x r h_rank h_root) x hx' hr' ≤
            (uf.setParent x r h_rank h_root).rank x := by
        exact iter_le_rank (uf.setParent x r h_rank h_root) x hx' hr'
      have hiter_succ_rank : iter uf x hx hr + 1 ≤ uf.rank x := by
        calc
          iter uf x hx hr + 1 ≤ iter (uf.setParent x r h_rank h_root) x hx' hr' := hiter_succ
          _ ≤ (uf.setParent x r h_rank h_root).rank x := hiter'_le_rank
          _ = uf.rank x := by simp [UF.setParent]
      have hcoeff : 1 ≤ alpha n - level uf x hx hr := by
        have hlt := level_lt_alpha uf x hx hr hold_lt
        omega
      calc
        iter uf x hx hr + 1 ≤ uf.rank x := hiter_succ_rank
        _ = 1 * uf.rank x := by simp
        _ ≤ (alpha n - level uf x hx hr) * uf.rank x :=
          Nat.mul_le_mul_right _ hcoeff
    have hsub :
        (alpha n - level (uf.setParent x r h_rank h_root) x hx' hr') *
              (uf.setParent x r h_rank h_root).rank x -
            iter (uf.setParent x r h_rank h_root) x hx' hr' + 1
          ≤ (alpha n - level uf x hx hr) * uf.rank x - iter uf x hx hr := by
      rw [hlevel_eq]
      simp only [UF.setParent]
      set B := (alpha n - level uf x hx hr) * uf.rank x
      have htmp : B - iter (uf.setParent x r h_rank h_root) x hx' hr' + 1 ≤
          B - (iter uf x hx hr + 1) + 1 := by
        exact Nat.add_le_add_right (Nat.sub_le_sub_left hiter_succ B) 1
      have htmp2 : B - (iter uf x hx hr + 1) + 1 = B - iter uf x hx hr := by
        omega
      exact htmp.trans_eq htmp2
    exact hsub
  · have hlevel_gt : level uf x hx hr + 1 ≤
        level (uf.setParent x r h_rank h_root) x hx' hr' := by
      omega
    have hiter'_ge : 1 ≤ iter (uf.setParent x r h_rank h_root) x hx' hr' := by
      exact one_le_iter (uf.setParent x r h_rank h_root) x hx' hr'
    have hphi_lb :
        (alpha n - level uf x hx hr - 1) * uf.rank x ≤
          (alpha n - level uf x hx hr) * uf.rank x - iter uf x hx hr := by
      simpa [phi, hx, hr0] using phi_lower_bound_of_positive_nonroot uf x hx hr hold_lt
    have h_alpha_sub :
        alpha n - level (uf.setParent x r h_rank h_root) x hx' hr' ≤
          alpha n - level uf x hx hr - 1 := by
      have hsub :=
        Nat.sub_le_sub_left hlevel_gt (alpha n)
      omega
    have hupper :
        (alpha n - level (uf.setParent x r h_rank h_root) x hx' hr') *
              (uf.setParent x r h_rank h_root).rank x -
            iter (uf.setParent x r h_rank h_root) x hx' hr' + 1
          ≤ (alpha n - level uf x hx hr - 1) * uf.rank x := by
      set B := (alpha n - level (uf.setParent x r h_rank h_root) x hx' hr') *
        (uf.setParent x r h_rank h_root).rank x
      have hcoeff : 1 ≤ alpha n - level (uf.setParent x r h_rank h_root) x hx' hr' := by
        have hlt :=
          level_lt_alpha (uf.setParent x r h_rank h_root) x hx' hr'
            (by simpa [UF.setParent] using hnr)
        omega
      have hB_pos : 1 ≤ B := by
        dsimp [B]
        calc
          1 = 1 * 1 := by simp
          _ ≤ (alpha n - level (uf.setParent x r h_rank h_root) x hx' hr') *
                (uf.setParent x r h_rank h_root).rank x :=
            Nat.mul_le_mul hcoeff hr'
      have :
          B - iter (uf.setParent x r h_rank h_root) x hx' hr' + 1 ≤ B := by
        have htmp :
            B - iter (uf.setParent x r h_rank h_root) x hx' hr' + 1 ≤ B - 1 + 1 := by
          exact Nat.add_le_add_right
            (Nat.sub_le_sub_left hiter'_ge B) 1
        have htmp2 : B - 1 + 1 = B := Nat.sub_add_cancel hB_pos
        exact htmp.trans_eq htmp2
      calc
        (alpha n - level (uf.setParent x r h_rank h_root) x hx' hr') *
              (uf.setParent x r h_rank h_root).rank x -
            iter (uf.setParent x r h_rank h_root) x hx' hr' + 1
          = B - iter (uf.setParent x r h_rank h_root) x hx' hr' + 1 := by rfl
        _ ≤ B := this
        _ ≤ (alpha n - level uf x hx hr - 1) *
              (uf.setParent x r h_rank h_root).rank x := by
          dsimp [B]
          exact Nat.mul_le_mul_right _ h_alpha_sub
        _ = (alpha n - level uf x hx hr - 1) * uf.rank x := by
            simp [UF.setParent]
    exact le_trans hupper hphi_lb

/-! ### Stage 3a: Potential increase of link

Linking two roots can increase Φ by at most `alpha(n)`. We first establish
helper lemmas about `phi` for roots and non-roots, then prove `link_Phi_le`
by case-splitting on the rank comparison. -/

/-- Helper: phi of a root is alpha(n) * rank. -/
theorem phi_root (uf : UF n) (x : Fin n) (hx : uf.isRoot x) :
    phi uf x = alpha n * uf.rank x := by
  simp [phi, hx]

/-- Helper: phi of a non-root with rank 0 is 0. -/
theorem phi_nonroot_rank_zero (uf : UF n) (x : Fin n) (hx : ¬uf.isRoot x)
    (hr : uf.rank x = 0) :
    phi uf x = 0 := by
  simp [phi, hx, hr]

/-- Helper: phi of any node is at most alpha(n) * rank(x). -/
theorem phi_le_alpha_mul_rank (uf : UF n) (x : Fin n) :
    phi uf x ≤ alpha n * uf.rank x := by
  unfold phi
  split
  · exact le_refl _
  · rename_i hx
    split
    · rename_i hr; rw [hr]; simp
    · rename_i hr
      have hr' : 1 ≤ uf.rank x := by omega
      -- (alpha n - level) * rank x - iter ≤ (alpha n - level) * rank x ≤ alpha n * rank x
      calc (alpha n - level uf x hx hr') * uf.rank x - iter uf x hx hr'
          ≤ (alpha n - level uf x hx hr') * uf.rank x := Nat.sub_le _ _
        _ ≤ alpha n * uf.rank x := Nat.mul_le_mul_right _ (Nat.sub_le _ _)

/-- link preserves parent of nodes other than the attached root (case 1: rx < ry). -/
private theorem link_parent_case1 (uf : UF n) (rx ry : Fin n)
    (hx : uf.isRoot rx) (_hy : uf.isRoot ry) (hne : rx ≠ ry)
    (h : uf.rank rx < uf.rank ry) (z : Fin n) (hz : z ≠ rx) :
    (link uf rx ry hx hne).parent z = uf.parent z := by
  simp [link, h, hz]

/-- link preserves parent of nodes other than the attached root (case 2: ry < rx). -/
private theorem link_parent_case2 (uf : UF n) (rx ry : Fin n)
    (hx : uf.isRoot rx) (_hy : uf.isRoot ry) (hne : rx ≠ ry)
    (h1 : ¬uf.rank rx < uf.rank ry) (h2 : uf.rank ry < uf.rank rx)
    (z : Fin n) (hz : z ≠ ry) :
    (link uf rx ry hx hne).parent z = uf.parent z := by
  simp [link, h1, h2, hz]

/-- link preserves parent of nodes other than ry (case 3: equal ranks). -/
private theorem link_parent_case3 (uf : UF n) (rx ry : Fin n)
    (hx : uf.isRoot rx) (_hy : uf.isRoot ry) (hne : rx ≠ ry)
    (h1 : ¬uf.rank rx < uf.rank ry) (h2 : ¬uf.rank ry < uf.rank rx)
    (z : Fin n) (hz : z ≠ ry) :
    (link uf rx ry hx hne).parent z = uf.parent z := by
  simp [link, h1, h2, hz]

/-- link preserves rank (cases 1 and 2). -/
private theorem link_rank_eq_of_ne_rank (uf : UF n) (rx ry : Fin n)
    (hx : uf.isRoot rx) (_hy : uf.isRoot ry) (hne : rx ≠ ry)
    (hrank : uf.rank rx ≠ uf.rank ry) :
    (link uf rx ry hx hne).rank = uf.rank := by
  unfold link
  by_cases h : uf.rank rx < uf.rank ry
  · simp [h]
  · have h2 : uf.rank ry < uf.rank rx := by omega
    simp [h, h2]

/-- link rank in case 3: rx gets rank + 1, others unchanged. -/
private theorem link_rank_case3 (uf : UF n) (rx ry : Fin n)
    (hx : uf.isRoot rx) (_hy : uf.isRoot ry) (hne : rx ≠ ry)
    (h1 : ¬uf.rank rx < uf.rank ry) (h2 : ¬uf.rank ry < uf.rank rx)
    (z : Fin n) :
    (link uf rx ry hx hne).rank z =
      if z = rx then uf.rank rx + 1 else uf.rank z := by
  simp [link, h1, h2]

/-- link preserves isRoot for all nodes except the attached one (case 1). -/
private theorem link_isRoot_case1 (uf : UF n) (rx ry : Fin n)
    (hx : uf.isRoot rx) (_hy : uf.isRoot ry) (hne : rx ≠ ry)
    (h : uf.rank rx < uf.rank ry) (z : Fin n) (hz : z ≠ rx) :
    (link uf rx ry hx hne).isRoot z ↔ uf.isRoot z := by
  simp [link, h, UF.isRoot, hz]

/-- In case 1, rx is not a root after link. -/
private theorem link_not_isRoot_case1 (uf : UF n) (rx ry : Fin n)
    (hx : uf.isRoot rx) (_hy : uf.isRoot ry) (hne : rx ≠ ry)
    (h : uf.rank rx < uf.rank ry) :
    ¬(link uf rx ry hx hne).isRoot rx := by
  simp only [link, h, UF.isRoot, ↓reduceDIte]
  exact fun h => absurd h.symm hne

/-- In case 2, ry is not a root after link. -/
private theorem link_not_isRoot_case2 (uf : UF n) (rx ry : Fin n)
    (hx : uf.isRoot rx) (_hy : uf.isRoot ry) (hne : rx ≠ ry)
    (h1 : ¬uf.rank rx < uf.rank ry) (h2 : uf.rank ry < uf.rank rx) :
    ¬(link uf rx ry hx hne).isRoot ry := by
  simp [link, h1, h2, UF.isRoot, hne]

/-- In case 3, ry is not a root after link. -/
private theorem link_not_isRoot_case3 (uf : UF n) (rx ry : Fin n)
    (hx : uf.isRoot rx) (_hy : uf.isRoot ry) (hne : rx ≠ ry)
    (h1 : ¬uf.rank rx < uf.rank ry) (h2 : ¬uf.rank ry < uf.rank rx) :
    ¬(link uf rx ry hx hne).isRoot ry := by
  simp [link, h1, h2, UF.isRoot, hne]

/-- In case 3, rx is still a root after link. -/
private theorem link_isRoot_rx_case3 (uf : UF n) (rx ry : Fin n)
    (hx : uf.isRoot rx) (_hy : uf.isRoot ry) (hne : rx ≠ ry)
    (h1 : ¬uf.rank rx < uf.rank ry) (h2 : ¬uf.rank ry < uf.rank rx) :
    (link uf rx ry hx hne).isRoot rx := by
  simp only [link, h1, h2, UF.isRoot, hne, ↓reduceDIte, ↓reduceIte]
  exact hx

/-- When parent-rank weakly increases and everything else stays the same,
    phi doesn't increase (for non-root nodes). -/
theorem phi_le_of_parent_rank_le (uf uf' : UF n) (z : Fin n)
    (hp : uf'.parent z = uf.parent z)
    (hr : uf'.rank z = uf.rank z)
    (hrp : uf.rank (uf.parent z) ≤ uf'.rank (uf'.parent z))
    (hroot : ¬uf.isRoot z)
    (hn : uf.rank (uf.parent z) < n) :
    phi uf' z ≤ phi uf z := by
  have hroot_iff : uf'.isRoot z ↔ uf.isRoot z := by
    simp [UF.isRoot, hp]
  have hroot' : ¬uf'.isRoot z := mt hroot_iff.mp hroot
  unfold phi
  simp only [hroot, hroot', dite_false]
  by_cases hrz : uf.rank z = 0
  · have hrz' : uf'.rank z = 0 := by rw [hr]; exact hrz
    simp [hrz, hrz']
  · have hrz' : uf'.rank z ≠ 0 := by rw [hr]; exact hrz
    simp only [hrz, hrz', dite_false]
    have hr' : 1 ≤ uf.rank z := by omega
    have hr'' : 1 ≤ uf'.rank z := by omega
    -- Need: (alpha - level') * rank' - iter' ≤ (alpha - level) * rank - iter
    -- where level' ≥ level (parent rank increased) and iter' adjusted accordingly
    -- Key: rank' = rank (by hr)
    -- level' ≥ level because
    -- {k : A k (rank z) ≤ new_parent_rank} ⊇ {k : A k (rank z) ≤ old_parent_rank}
    -- So Nat.find for level' (first k that fails) ≥ Nat.find for level (first k that fails)
    -- Hence level' = Nat.find' - 1 ≥ Nat.find - 1 = level
    -- Key conversion: the parent-rank in uf' is ≥ that in uf
    -- So if A k (rank z) ≤ old_parent_rank, then also ≤ new_parent_rank
    have hconv : ∀ k, (¬A k (uf'.rank z) ≤ uf'.rank (uf'.parent z)) →
                      (¬A k (uf.rank z) ≤ uf.rank (uf.parent z)) := by
      intro k hk h
      apply hk
      rw [hr]
      calc A k (uf.rank z) ≤ uf.rank (uf.parent z) := h
        _ ≤ uf'.rank (uf'.parent z) := hrp
    have hfind_le : Nat.find (exists_level uf z hroot hr') ≤
                    Nat.find (exists_level uf' z hroot' hr'') := by
      exact Nat.find_mono hconv
    have hlevel_le : level uf z hroot hr' ≤ level uf' z hroot' hr'' := by
      unfold level; omega
    -- Now case split: level' = level or level' > level
    by_cases hlev_eq : level uf' z hroot' hr'' = level uf z hroot hr'
    · -- Same level: iter' ≥ iter since more iterations fit in the higher parent rank
      -- iter defined via Nat.find on: ¬(iterFn (A level) (i+1) (rank z) ≤ parent_rank)
      -- When parent_rank increases, more i's satisfy the condition, so Nat.find increases
      have hconv_iter : ∀ i,
          (¬iterFn (A (level uf' z hroot' hr'')) (i + 1) (uf'.rank z) ≤ uf'.rank (uf'.parent z)) →
          (¬iterFn (A (level uf z hroot hr')) (i + 1) (uf.rank z) ≤ uf.rank (uf.parent z)) := by
        intro i hi h
        apply hi
        rw [hlev_eq, hr]
        exact le_trans h hrp
      have hiter_le : iter uf z hroot hr' ≤ iter uf' z hroot' hr'' := by
        unfold iter
        exact Nat.find_mono hconv_iter
      -- phi' = (alpha - level') * rank' - iter' = (alpha - level) * rank - iter'
      -- phi  = (alpha - level) * rank - iter
      -- Since iter' ≥ iter, phi' ≤ phi
      -- Use the fact that (a*b - c) ≤ (a*b - d) when d ≤ c
      have h1 : (alpha n - level uf' z hroot' hr'') * uf'.rank z =
                (alpha n - level uf z hroot hr') * uf.rank z := by
        rw [hlev_eq, hr]
      calc (alpha n - level uf' z hroot' hr'') * uf'.rank z - iter uf' z hroot' hr''
          = (alpha n - level uf z hroot hr') * uf.rank z - iter uf' z hroot' hr'' := by rw [h1]
        _ ≤ (alpha n - level uf z hroot hr') * uf.rank z - iter uf z hroot hr' :=
            Nat.sub_le_sub_left hiter_le _
    · -- level' > level, i.e., level' ≥ level + 1
      have hlev_gt : level uf z hroot hr' + 1 ≤ level uf' z hroot' hr'' := by omega
      -- phi' = (alpha - level') * rank - iter'
      -- phi  = (alpha - level) * rank - iter
      -- (alpha - level') ≤ alpha - level - 1
      -- iter' ≥ 1 (one_le_iter), iter ≤ rank (iter_le_rank)
      -- phi' ≤ (alpha - level - 1) * rank - 1
      -- phi  ≥ (alpha - level) * rank - rank = (alpha - level - 1) * rank
      -- So phi' ≤ (alpha - level - 1) * rank - 1 < (alpha - level - 1) * rank ≤ phi
      have hiter'_ge : 1 ≤ iter uf' z hroot' hr'' := one_le_iter uf' z hroot' hr''
      have hiter_le_rank : iter uf z hroot hr' ≤ uf.rank z := iter_le_rank uf z hroot hr'
      have hlevel_lt : level uf z hroot hr' < alpha n := level_lt_alpha uf z hroot hr' hn
      -- phi(uf, z) = (alpha - L) * R - I where I ≤ R
      -- So phi(uf, z) ≥ (alpha - L) * R - R = (alpha - L - 1) * R
      have hphi_lb : (alpha n - level uf z hroot hr' - 1) * uf.rank z ≤
          (alpha n - level uf z hroot hr') * uf.rank z - iter uf z hroot hr' := by
        -- (a-1)*R ≤ a*R - I when I ≤ R and a ≥ 1
        -- (a-1)*R + I ≤ (a-1)*R + R = a*R  (since I ≤ R)
        -- So (a-1)*R ≤ a*R - I
        set L := level uf z hroot hr' with hL
        set R := uf.rank z with hR
        set I := iter uf z hroot hr' with hI
        set aL := alpha n - L with haL
        have haL_pos : 1 ≤ aL := by omega
        have hIR : I ≤ R := hiter_le_rank
        -- aL * R = (aL - 1) * R + R
        have key : (aL - 1) * R + R = aL * R := by
          have : aL ≥ 1 := haL_pos
          cases haL : aL with
          | zero => omega
          | succ a => simp [Nat.succ_mul]
        -- (aL - 1) * R + I ≤ (aL - 1) * R + R = aL * R
        have h2 : (aL - 1) * R + I ≤ aL * R := by omega
        omega
      -- phi(uf', z) = (alpha - L') * R' - I' where L' ≥ L+1, R' = R, I' ≥ 1
      -- (alpha - L') ≤ alpha - L - 1
      have h_alpha_sub :
          alpha n - level uf' z hroot' hr'' ≤
            alpha n - level uf z hroot hr' - 1 := by
        omega
      calc (alpha n - level uf' z hroot' hr'') * uf'.rank z - iter uf' z hroot' hr''
          ≤ (alpha n - level uf' z hroot' hr'') * uf'.rank z := Nat.sub_le _ _
        _ ≤ (alpha n - level uf z hroot hr' - 1) * uf'.rank z :=
            Nat.mul_le_mul_right _ h_alpha_sub
        _ = (alpha n - level uf z hroot hr' - 1) * uf.rank z := by rw [hr]
        _ ≤ (alpha n - level uf z hroot hr') * uf.rank z - iter uf z hroot hr' := hphi_lb

/-! ### Stage 3b: Phi decomposition and phi stability

To reason about the global potential Φ after `setParent` or `link`, we need:
- `phi_eq_of_same_data`: phi(z) is determined entirely by `rank(z)`,
  `rank(parent(z))`, `parent(z)`, and `isRoot(z)`. If two UF states agree on
  these for node `z`, then `phi` is identical.
- `Phi_setParent`: the global potential splits as
  `Φ(setParent) = Φ(uf) − phi(uf,x) + phi(setParent,x)`, since `setParent`
  only changes the parent of `x` and rank is untouched.
- `phi_setParent_eq_of_ne`: for `z ≠ x`, phi(z) is unchanged by `setParent x`.

These lemmas are used both by `link_Phi_le` and by `find_Phi_le_budget`. -/

private theorem level_eq_of_same_edge_data (uf uf' : UF n) (z : Fin n)
    (_hp : uf'.parent z = uf.parent z)
    (hr : uf'.rank z = uf.rank z)
    (hrp : uf'.rank (uf'.parent z) = uf.rank (uf.parent z))
    (hz : ¬uf.isRoot z) (hz' : ¬uf'.isRoot z)
    (hrz : 1 ≤ uf.rank z) (hrz' : 1 ≤ uf'.rank z) :
    level uf' z hz' hrz' = level uf z hz hrz := by
  have hconv : ∀ k, A k (uf'.rank z) ≤ uf'.rank (uf'.parent z) ↔
      A k (uf.rank z) ≤ uf.rank (uf.parent z) := by
    intro k
    constructor
    · intro h
      rw [hr, hrp] at h
      exact h
    · intro h
      rw [← hr, ← hrp] at h
      exact h
  unfold level
  congr 1
  apply le_antisymm
  · apply Nat.find_mono
    intro k hk
    exact mt (hconv k).mp hk
  · apply Nat.find_mono
    intro k hk
    exact mt (hconv k).mpr hk

private theorem iter_eq_of_same_edge_data (uf uf' : UF n) (z : Fin n)
    (hp : uf'.parent z = uf.parent z)
    (hr : uf'.rank z = uf.rank z)
    (hrp : uf'.rank (uf'.parent z) = uf.rank (uf.parent z))
    (hz : ¬uf.isRoot z) (hz' : ¬uf'.isRoot z)
    (hrz : 1 ≤ uf.rank z) (hrz' : 1 ≤ uf'.rank z) :
    iter uf' z hz' hrz' = iter uf z hz hrz := by
  have hlevel :
      level uf' z hz' hrz' = level uf z hz hrz :=
    level_eq_of_same_edge_data uf uf' z hp hr hrp hz hz' hrz hrz'
  have hconv : ∀ i,
      iterFn (A (level uf' z hz' hrz')) (i + 1) (uf'.rank z) ≤
          uf'.rank (uf'.parent z) ↔
        iterFn (A (level uf z hz hrz)) (i + 1) (uf.rank z) ≤
          uf.rank (uf.parent z) := by
    intro i
    constructor
    · intro h
      rw [hlevel, hr, hrp] at h
      exact h
    · intro h
      rw [← hlevel, ← hr, ← hrp] at h
      exact h
  unfold iter
  apply le_antisymm
  · apply Nat.find_mono
    intro i hi
    exact mt (hconv i).mp hi
  · apply Nat.find_mono
    intro i hi
    exact mt (hconv i).mpr hi

/-- Two UFs that agree on rank z, rank (parent z), parent z, and isRoot z
    give the same phi at z. -/
private theorem phi_eq_of_same_data (uf uf' : UF n) (z : Fin n)
    (hp : uf'.parent z = uf.parent z)
    (hr : uf'.rank z = uf.rank z)
    (hrp : uf'.rank (uf'.parent z) = uf.rank (uf.parent z)) :
    phi uf' z = phi uf z := by
  have hroot : uf'.isRoot z ↔ uf.isRoot z := by
    simp [UF.isRoot, hp]
  unfold phi
  by_cases hz : uf.isRoot z
  · -- z is root in both
    have hz' := hroot.mpr hz
    simp [hz', hz, hr]
  · -- z is not root in both
    have hz' : ¬uf'.isRoot z := mt hroot.mp hz
    simp only [hz', hz, dite_false]
    by_cases hrz : uf.rank z = 0
    · have hrz' : uf'.rank z = 0 := by rw [hr, hrz]
      simp [hrz', hrz]
    · have hrz' : uf'.rank z ≠ 0 := by rw [hr]; exact hrz
      simp only [hrz', hrz, dite_false]
      have hr' : 1 ≤ uf.rank z := by omega
      have hr'' : 1 ≤ uf'.rank z := by omega
      have hlevel :=
        level_eq_of_same_edge_data uf uf' z hp hr hrp hz hz' hr' hr''
      have hiter :=
        iter_eq_of_same_edge_data uf uf' z hp hr hrp hz hz' hr' hr''
      simp only [hr, hlevel, hiter]

private theorem phi_setParent_eq_of_ne (uf : UF n) (x r z : Fin n)
    (h_rank : uf.rank x < uf.rank r) (h_root : uf.rootOf x = r) (hzx : z ≠ x) :
    phi (uf.setParent x r h_rank h_root) z = phi uf z := by
  have hp : (uf.setParent x r h_rank h_root).parent z = uf.parent z := by
    simp [UF.setParent, hzx]
  have hr : (uf.setParent x r h_rank h_root).rank z = uf.rank z := by
    simp [UF.setParent]
  have hrp : (uf.setParent x r h_rank h_root).rank ((uf.setParent x r h_rank h_root).parent z) =
      uf.rank (uf.parent z) := by
    rw [hp]
    simp [UF.setParent]
  exact phi_eq_of_same_data uf (uf.setParent x r h_rank h_root) z hp hr hrp

private theorem Phi_setParent (uf : UF n) (x r : Fin n)
    (h_rank : uf.rank x < uf.rank r) (h_root : uf.rootOf x = r) :
    Phi (uf.setParent x r h_rank h_root) =
      Phi uf - phi uf x + phi (uf.setParent x r h_rank h_root) x := by
  unfold Phi
  have hx_mem : x ∈ Finset.univ := Finset.mem_univ x
  rw [← Finset.add_sum_erase Finset.univ (phi (uf.setParent x r h_rank h_root)) hx_mem]
  rw [← Finset.add_sum_erase Finset.univ (phi uf) hx_mem]
  have hrest :
      ∑ z ∈ Finset.univ.erase x, phi (uf.setParent x r h_rank h_root) z =
      ∑ z ∈ Finset.univ.erase x, phi uf z := by
    apply Finset.sum_congr rfl
    intro z hz
    exact phi_setParent_eq_of_ne uf x r z h_rank h_root (Finset.ne_of_mem_erase hz)
  rw [hrest]
  omega

/-! ### Stage 3c: The findBudget decomposition

The cost of `find(x)` is the length of the path from `x` to its root. We
classify each node on the path into one of four categories:

1. **Root** (base case): no cost.
2. **Rank-0 node**: always costs 1, accounted for by `zeroBudget ≤ 1`.
3. **Child of root** (rank ≥ 1, parent is root): costs 1, accounted for by
   `rootChildBudget ≤ 1`.
4. **Interior node** (rank ≥ 1, parent is not root):
   - If `level(x)` is a *new* level not yet seen deeper on the path: costs 1,
     accounted for by `interiorLevels.card ≤ alpha(n)`.
   - If `level(x)` is *already present* in `interiorLevels(parent(x))`: the
     cost of 1 is paid by a ≥ 1 drop in `phi(x)` from `phi_setParent_self_drop`.

The sum `findBudget = interiorLevels.card + zeroBudget + rootChildBudget` is
therefore an upper bound on the unpaid cost. Since
`findBudget ≤ alpha(n) + 1 + 1 = alpha(n) + 2`, the amortized cost of find
is at most `alpha(n) + 2`.

The decomposition lemmas (`findBudget_root`, `findBudget_rank_zero`,
`findBudget_parent_root`, `findBudget_same_level`, `findBudget_new_level`)
show how `findBudget(x)` relates to `findBudget(parent(x))` in each case. -/

private theorem parent_rank_le_root_rank (uf : UF n) (x : Fin n)
    (hx : ¬uf.isRoot x) :
    uf.rank (uf.parent x) ≤ uf.rank (uf.rootOf x) := by
  by_cases hp : uf.isRoot (uf.parent x)
  · rw [← UF.rootOf_parent uf x hx, UF.rootOf_root uf (uf.parent x) hp]
  · have hlt : uf.rank (uf.parent x) < uf.rank (uf.rootOf (uf.parent x)) :=
      rank_lt_rootOf uf (uf.parent x) hp
    rw [UF.rootOf_parent uf x hx] at hlt
    exact Nat.le_of_lt hlt

private def zeroBudget (uf : UF n) (x : Fin n) : Nat :=
  if _hx : uf.isRoot x then
    0
  else if uf.rank x = 0 then
    1
  else
    zeroBudget uf (uf.parent x)
termination_by uf.rankMax - uf.rank x
decreasing_by
  all_goals
    have h1 := uf.rank_lt x (by rwa [UF.isRoot] at _hx)
    have h2 := uf.rank_le_max (uf.parent x)
    omega

private def rootChildBudget (uf : UF n) (x : Fin n) : Nat :=
  if _hx : uf.isRoot x then
    0
  else if uf.rank x = 0 then
    rootChildBudget uf (uf.parent x)
  else if _hp : uf.isRoot (uf.parent x) then
    1
  else
    rootChildBudget uf (uf.parent x)
termination_by uf.rankMax - uf.rank x
decreasing_by
  all_goals
    have h1 := uf.rank_lt x (by rwa [UF.isRoot] at _hx)
    have h2 := uf.rank_le_max (uf.parent x)
    omega

private noncomputable def interiorLevels (uf : UF n) (x : Fin n) : Finset ℕ :=
  if hx : uf.isRoot x then
    ∅
  else if hr0 : uf.rank x = 0 then
    interiorLevels uf (uf.parent x)
  else
    have hr : 1 ≤ uf.rank x := by omega
    if hp : uf.isRoot (uf.parent x) then
      interiorLevels uf (uf.parent x)
    else
      insert (level uf x hx hr) (interiorLevels uf (uf.parent x))
termination_by uf.rankMax - uf.rank x
decreasing_by
  all_goals
    have h1 := uf.rank_lt x (by rwa [UF.isRoot] at hx)
    have h2 := uf.rank_le_max (uf.parent x)
    omega

private noncomputable def findBudget (uf : UF n) (x : Fin n) : Nat :=
  (interiorLevels uf x).card + zeroBudget uf x + rootChildBudget uf x

private theorem zeroBudget_eq_zero_of_pos (uf : UF n) (x : Fin n)
    (hx : ¬uf.isRoot x) (hr : 1 ≤ uf.rank x) :
    zeroBudget uf x = 0 := by
  unfold zeroBudget
  simp only [hx, show ¬uf.rank x = 0 by omega, ↓reduceDIte]
  have hparent_pos : 1 ≤ uf.rank (uf.parent x) := by
    have hlt := uf.rank_lt x (by rwa [UF.isRoot] at hx)
    omega
  by_cases hp : uf.isRoot (uf.parent x)
  · simp [zeroBudget, hp]
  · exact zeroBudget_eq_zero_of_pos uf (uf.parent x) hp hparent_pos
termination_by uf.rankMax - uf.rank x
decreasing_by
  all_goals
    have h1 := uf.rank_lt x (by rwa [UF.isRoot] at hx)
    have h2 := uf.rank_le_max (uf.parent x)
    omega

private theorem zeroBudget_le_one (uf : UF n) (x : Fin n) :
    zeroBudget uf x ≤ 1 := by
  by_cases hx : uf.isRoot x
  · unfold zeroBudget
    simp [hx]
  · unfold zeroBudget
    simp [hx]
    by_cases hr0 : uf.rank x = 0
    · simp [hr0]
    · simp [hr0, zeroBudget_le_one uf (uf.parent x)]
termination_by uf.rankMax - uf.rank x
decreasing_by
  all_goals
    have h1 := uf.rank_lt x (by rwa [UF.isRoot] at hx)
    have h2 := uf.rank_le_max (uf.parent x)
    omega

private theorem rootChildBudget_le_one (uf : UF n) (x : Fin n) :
    rootChildBudget uf x ≤ 1 := by
  by_cases hx : uf.isRoot x
  · unfold rootChildBudget
    simp [hx]
  · unfold rootChildBudget
    simp [hx]
    by_cases hr0 : uf.rank x = 0
    · simp [hr0, rootChildBudget_le_one uf (uf.parent x)]
    · simp [hr0]
      by_cases hp : uf.isRoot (uf.parent x)
      · simp [hp]
      · simp [hp, rootChildBudget_le_one uf (uf.parent x)]
termination_by uf.rankMax - uf.rank x
decreasing_by
  all_goals
    have h1 := uf.rank_lt x (by rwa [UF.isRoot] at hx)
    have h2 := uf.rank_le_max (uf.parent x)
    omega

private theorem mem_interiorLevels_witness (uf : UF n) (x : Fin n) {k : ℕ}
    (hk : k ∈ interiorLevels uf x) :
    ∃ y, ∃ hy : ¬uf.isRoot y, ∃ hr : 1 ≤ uf.rank y,
      ¬uf.isRoot (uf.parent y) ∧
      level uf y hy hr = k ∧
      uf.rank x ≤ uf.rank y ∧
      uf.rank (uf.parent y) ≤ uf.rank (uf.rootOf x) := by
  by_cases hx : uf.isRoot x
  · simp [interiorLevels, hx] at hk
  · by_cases hr0 : uf.rank x = 0
    · unfold interiorLevels at hk
      have hk' : k ∈ interiorLevels uf (uf.parent x) := by
        simpa [hx, hr0] using hk
      rcases mem_interiorLevels_witness uf (uf.parent x) hk' with
        ⟨y, hy, hr, hyp, hlevel, hxy, hyroot⟩
      refine ⟨y, hy, hr, hyp, hlevel, ?_, ?_⟩
      · omega
      · rw [← UF.rootOf_parent uf x hx]
        exact hyroot
    · have hr : 1 ≤ uf.rank x := by omega
      by_cases hp : uf.isRoot (uf.parent x)
      · unfold interiorLevels at hk
        have hk' : k ∈ interiorLevels uf (uf.parent x) := by
          simpa [hx, hr0, hp] using hk
        have : False := by
          unfold interiorLevels at hk'
          simp [hp] at hk'
        exact this.elim
      · have hk' :
          k = level uf x hx hr ∨ k ∈ interiorLevels uf (uf.parent x) := by
          unfold interiorLevels at hk
          simpa [hx, hr0, hp] using hk
        rcases hk' with rfl | hk'
        · refine ⟨x, hx, hr, hp, rfl, le_rfl, ?_⟩
          exact parent_rank_le_root_rank uf x hx
        · rcases mem_interiorLevels_witness uf (uf.parent x) hk' with
            ⟨y, hy, hry, hyp, hlevel, hxy, hyroot⟩
          refine ⟨y, hy, hry, hyp, hlevel, ?_, ?_⟩
          · have hlt := uf.rank_lt x (by rwa [UF.isRoot] at hx)
            exact le_trans (Nat.le_of_lt hlt) hxy
          · rw [← UF.rootOf_parent uf x hx]
            exact hyroot
termination_by uf.rankMax - uf.rank x
decreasing_by
  all_goals
    have h1 := uf.rank_lt x (by rwa [UF.isRoot] at hx)
    have h2 := uf.rank_le_max (uf.parent x)
    omega

private theorem mem_interiorLevels_lt_alpha (uf : UF n) (x : Fin n)
    (hn : ∀ y, uf.rank y < n) {k : ℕ} (hk : k ∈ interiorLevels uf x) :
    k < alpha n := by
  rcases mem_interiorLevels_witness uf x hk with
    ⟨y, hy, hr, hyp, hlevel, _, _⟩
  rw [← hlevel]
  exact level_lt_alpha uf y hy hr (hn (uf.parent y))

private theorem interiorLevels_card_le_alpha (uf : UF n) (x : Fin n)
    (hn : ∀ y, uf.rank y < n) :
    (interiorLevels uf x).card ≤ alpha n := by
  calc
    (interiorLevels uf x).card ≤ (Finset.range (alpha n)).card := by
      exact Finset.card_le_card (by
        intro k hk
        exact Finset.mem_range.mpr (mem_interiorLevels_lt_alpha uf x hn hk))
    _ = alpha n := Finset.card_range (alpha n)

private theorem hextra_of_mem_interiorLevels (uf : UF n) (x : Fin n)
    (hx : ¬uf.isRoot x) (hr : 1 ≤ uf.rank x)
    (_hp : ¬uf.isRoot (uf.parent x))
    (hk : level uf x hx hr ∈ interiorLevels uf (uf.parent x)) :
    iterFn (A (level uf x hx hr)) (iter uf x hx hr + 1) (uf.rank x) ≤
      uf.rank (uf.rootOf (uf.parent x)) := by
  rcases mem_interiorLevels_witness uf (uf.parent x) hk with
    ⟨y, hy, hry, hyp, hlevel, hxy, hyroot⟩
  calc
    iterFn (A (level uf x hx hr)) (iter uf x hx hr + 1) (uf.rank x)
      = A (level uf x hx hr)
          (iterFn (A (level uf x hx hr)) (iter uf x hx hr) (uf.rank x)) := by
            simp [iterFn_succ]
    _ ≤ A (level uf x hx hr) (uf.rank (uf.parent x)) :=
      (A_strictMono_right _).monotone (iter_value_le_parent uf x hx hr)
    _ ≤ A (level uf x hx hr) (uf.rank y) :=
      (A_strictMono_right _).monotone hxy
    _ ≤ uf.rank (uf.parent y) := by
      have hkyle : level uf x hx hr ≤ level uf y hy hry := by
        rw [hlevel]
      exact A_le_parent_of_le_level uf y hy hry (k := level uf x hx hr) hkyle
    _ ≤ uf.rank (uf.rootOf (uf.parent x)) := hyroot

private theorem findBudget_root (uf : UF n) (x : Fin n)
    (hx : uf.isRoot x) :
    findBudget uf x = 0 := by
  unfold findBudget
  unfold interiorLevels zeroBudget rootChildBudget
  simp [hx]

private theorem findBudget_rank_zero (uf : UF n) (x : Fin n)
    (hx : ¬uf.isRoot x) (hr0 : uf.rank x = 0) :
    findBudget uf x = findBudget uf (uf.parent x) + 1 := by
  have hparent_pos : 1 ≤ uf.rank (uf.parent x) := by
    have hlt := uf.rank_lt x (by rwa [UF.isRoot] at hx)
    omega
  by_cases hp : uf.isRoot (uf.parent x)
  · have hparent0 : findBudget uf (uf.parent x) = 0 := findBudget_root uf (uf.parent x) hp
    have hinter : interiorLevels uf (uf.parent x) = ∅ := by
      unfold interiorLevels
      simp [hp]
    have hrootchild : rootChildBudget uf (uf.parent x) = 0 := by
      unfold rootChildBudget
      simp [hp]
    rw [hparent0]
    unfold findBudget
    unfold interiorLevels zeroBudget rootChildBudget
    simp [hx, hr0, hinter, hrootchild]
  · have hzparent := zeroBudget_eq_zero_of_pos uf (uf.parent x) hp hparent_pos
    conv_lhs => unfold findBudget interiorLevels zeroBudget rootChildBudget
    rw [findBudget, hzparent]
    simp [hx, hr0]
    omega

private theorem findBudget_parent_root (uf : UF n) (x : Fin n)
    (hx : ¬uf.isRoot x) (hr : 1 ≤ uf.rank x)
    (hp : uf.isRoot (uf.parent x)) :
    findBudget uf x = findBudget uf (uf.parent x) + 1 := by
  have hr0 : uf.rank x ≠ 0 := by omega
  have hroot : findBudget uf (uf.parent x) = 0 := findBudget_root uf (uf.parent x) hp
  have hinter : interiorLevels uf (uf.parent x) = ∅ := by
    unfold interiorLevels
    simp [hp]
  have hzero : zeroBudget uf (uf.parent x) = 0 := by
    unfold zeroBudget
    simp [hp]
  rw [hroot]
  unfold findBudget
  unfold interiorLevels zeroBudget rootChildBudget
  simp [hx, hr0, hp, hinter, hzero]

private theorem findBudget_same_level (uf : UF n) (x : Fin n)
    (hx : ¬uf.isRoot x) (hr : 1 ≤ uf.rank x)
    (hp : ¬uf.isRoot (uf.parent x))
    (hk : level uf x hx hr ∈ interiorLevels uf (uf.parent x)) :
    findBudget uf x = findBudget uf (uf.parent x) := by
  have hr0 : uf.rank x ≠ 0 := by omega
  have hparent_pos : 1 ≤ uf.rank (uf.parent x) := by
    have hlt := uf.rank_lt x (by rwa [UF.isRoot] at hx)
    omega
  have hz := zeroBudget_eq_zero_of_pos uf x hx hr
  have hzparent := zeroBudget_eq_zero_of_pos uf (uf.parent x) hp hparent_pos
  conv_lhs => unfold findBudget interiorLevels zeroBudget rootChildBudget
  rw [findBudget, hzparent]
  simp [hx, hr0, hp, hk]

private theorem findBudget_new_level (uf : UF n) (x : Fin n)
    (hx : ¬uf.isRoot x) (hr : 1 ≤ uf.rank x)
    (hp : ¬uf.isRoot (uf.parent x))
    (hk : level uf x hx hr ∉ interiorLevels uf (uf.parent x)) :
    findBudget uf x = findBudget uf (uf.parent x) + 1 := by
  have hr0 : uf.rank x ≠ 0 := by omega
  have hparent_pos : 1 ≤ uf.rank (uf.parent x) := by
    have hlt := uf.rank_lt x (by rwa [UF.isRoot] at hx)
    omega
  have hz := zeroBudget_eq_zero_of_pos uf x hx hr
  have hzparent := zeroBudget_eq_zero_of_pos uf (uf.parent x) hp hparent_pos
  conv_lhs => unfold findBudget interiorLevels zeroBudget rootChildBudget
  rw [findBudget, hzparent]
  simp [hx, hr0, hp, hk]
  omega

private theorem findBudget_le_alpha_add_two (uf : UF n) (x : Fin n)
    (hn : ∀ y, uf.rank y < n) :
    findBudget uf x ≤ alpha n + 2 := by
  unfold findBudget
  have hcard := interiorLevels_card_le_alpha uf x hn
  have hzero := zeroBudget_le_one uf x
  have hroot := rootChildBudget_le_one uf x
  omega

/-! ### Stage 4: Proof of find_amortized

The core argument: `find_time + Φ_after ≤ Φ_before + findBudget(x)`, proved by
well-founded induction matching `find`'s recursion on `rankMax − rank(x)`.

Two helper lemmas extract `find`'s recursive equations:
- `find_time_step`: time = 1 + time of recursive call on parent
- `find_ret2_step`: result UF = setParent of recursive result

The inductive step uses `Phi_setParent` to split Φ, then `phi_eq_of_same_data`
(phi of `x` is the same before and after `find(parent(x))`, since
`find_preserves_parent_of_lt_rank` keeps `x`'s parent intact), and finally the
appropriate findBudget decomposition + phi bound for each node category. -/

/-- Helper: find's time decomposes as 1 + recursive time. -/
private theorem find_time_step (uf : UF n) (x : Fin n) (hx : uf.parent x ≠ x) :
    (find uf x).time = 1 + (find uf (uf.parent x)).time := by
  unfold find; conv_lhs => unfold findAux; simp [hx]

/-- Helper: find's result is setParent of the recursive result. -/
private theorem find_ret2_step (uf : UF n) (x : Fin n) (hx : uf.parent x ≠ x)
    (h : ⟪find uf (uf.parent x)⟫.2.rank x <
         ⟪find uf (uf.parent x)⟫.2.rank ⟪find uf (uf.parent x)⟫.1)
    (hr : ⟪find uf (uf.parent x)⟫.2.rootOf x = ⟪find uf (uf.parent x)⟫.1) :
    ⟪find uf x⟫.2 = ⟪find uf (uf.parent x)⟫.2.setParent x
      ⟪find uf (uf.parent x)⟫.1 h hr := by
  unfold find; conv_lhs => unfold findAux; simp [hx]

/-- The amortized cost of find is bounded by the findBudget.

This is the core inductive proof: each step of find costs 1 unit, but
path compression decreases the potential. The findBudget accounts for
the steps not covered by potential decrease. -/
private theorem find_Phi_le_budget (uf : UF n) (x : Fin n)
    (hn : ∀ y, uf.rank y < n) :
    (find uf x).time + Phi ⟪find uf x⟫.2 ≤ Phi uf + findBudget uf x := by
  by_cases hx_root : uf.isRoot x
  · -- Base: x is root. time = 0, result = uf, budget = 0.
    have hpx : uf.parent x = x := hx_root
    have htime : (find uf x).time = 0 := by unfold find findAux; simp [hpx]
    have hret : ⟪find uf x⟫.2 = uf := by
      show (find uf x).ret.2 = uf; unfold find findAux; simp [hpx]
    rw [htime, hret, findBudget_root uf x hx_root]; omega
  · -- Recursive: x is not root
    have hx : uf.parent x ≠ x := by rwa [UF.isRoot] at hx_root
    -- Abbreviations for the recursive find result
    set uf' := ⟪find uf (uf.parent x)⟫.2 with huf'_def
    set root := ⟪find uf (uf.parent x)⟫.1 with hroot_def
    -- Key properties of find on parent(x)
    have h_rank_eq : uf'.rank = uf.rank := find_ret_rank_eq uf (uf.parent x)
    have hroot_eq : root = uf.rootOf x := by
      rw [hroot_def, find_ret_rootOf_eq, UF.rootOf_parent uf x hx]
    have h_parent_pres : uf'.parent x = uf.parent x :=
      find_preserves_parent_of_lt_rank uf (uf.parent x) x (uf.rank_lt x hx)
    -- Rank condition for setParent
    have h_rank : uf'.rank x < uf'.rank root := by
      simp only [h_rank_eq, hroot_eq]; exact rank_lt_rootOf uf x hx
    have h_root_uf' : uf'.rootOf x = root := by
      rw [huf'_def, find_preserves_rootOf uf (uf.parent x) x, hroot_eq]
    -- Time and result equations
    rw [find_time_step uf x hx, find_ret2_step uf x hx h_rank h_root_uf']
    -- Inductive hypothesis
    have ih : (find uf (uf.parent x)).time + Phi uf' ≤
              Phi uf + findBudget uf (uf.parent x) :=
      find_Phi_le_budget uf (uf.parent x) hn
    -- Phi decomposition: Phi(setParent) = Phi(uf') - phi(uf',x) + phi(setParent,x)
    rw [Phi_setParent uf' x root h_rank h_root_uf']
    -- phi(uf', x) = phi(uf, x) since parent and rank of x are preserved
    have hrp : uf'.rank (uf'.parent x) = uf.rank (uf.parent x) := by
      rw [h_parent_pres]; exact congrFun h_rank_eq (uf.parent x)
    have hphi_eq : phi uf' x = phi uf x :=
      phi_eq_of_same_data uf uf' x h_parent_pres (congrFun h_rank_eq x) hrp
    -- phi(uf', x) is a summand of Phi(uf'), so phi(uf', x) ≤ Phi(uf')
    have hphi_le_Phi : phi uf' x ≤ Phi uf' :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ x)
    -- x is not root in uf' (parent preserved)
    have hx_not_root' : ¬uf'.isRoot x := by rwa [UF.isRoot, h_parent_pres]
    -- Parent rank ≤ root rank in uf'
    have hparent_le : uf'.rank (uf'.parent x) ≤ uf'.rank root := by
      rw [h_parent_pres, h_rank_eq, hroot_eq]
      exact parent_rank_le_root_rank uf x hx
    have hnr : uf'.rank root < n := by rw [h_rank_eq, hroot_eq]; exact hn _
    -- Case split on rank(x)
    by_cases hr0 : uf.rank x = 0
    · -- Rank 0: budget increases by 1, phi stays 0
      rw [findBudget_rank_zero uf x hx_root hr0]
      have hphi0 : phi uf x = 0 := phi_nonroot_rank_zero uf x hx_root hr0
      have hphi0' : phi (uf'.setParent x root h_rank h_root_uf') x = 0 := by
        apply phi_nonroot_rank_zero
        · simp only [UF.isRoot, UF.setParent]
          exact fun h => absurd (h ▸ h_rank) (Nat.lt_irrefl _)
        · change uf'.rank x = 0
          rw [congrFun h_rank_eq x]; exact hr0
      rw [hphi_eq, hphi0, hphi0']; omega
    · -- Rank ≥ 1
      have hr : 1 ≤ uf.rank x := by omega
      have hr' : 1 ≤ uf'.rank x := by rw [congrFun h_rank_eq x]; exact hr
      -- phi doesn't increase with path compression
      have hphi_le :=
        phi_setParent_self_le uf' x root hx_not_root' hr' h_rank h_root_uf' hparent_le hnr
      by_cases hp : uf.isRoot (uf.parent x)
      · -- Parent is root: budget increases by 1
        rw [findBudget_parent_root uf x hx_root hr hp, hphi_eq]; omega
      · -- Parent is not root: check if level(x) ∈ interiorLevels(parent x)
        by_cases hk : level uf x hx_root hr ∈ interiorLevels uf (uf.parent x)
        · -- Same level: budget unchanged, phi drops by ≥ 1
          rw [findBudget_same_level uf x hx_root hr hp hk]
          -- The hextra condition: iteration value fits in root's rank
          have hextra := hextra_of_mem_interiorLevels uf x hx_root hr hp hk
          -- Translate level/iter from uf to uf' (same edge data)
          have hlevel := level_eq_of_same_edge_data uf uf' x h_parent_pres
            (congrFun h_rank_eq x) hrp hx_root hx_not_root' hr hr'
          have hiter := iter_eq_of_same_edge_data uf uf' x h_parent_pres
            (congrFun h_rank_eq x) hrp hx_root hx_not_root' hr hr'
          have hextra' : iterFn (A (level uf' x hx_not_root' hr'))
              (iter uf' x hx_not_root' hr' + 1) (uf'.rank x) ≤ uf'.rank root := by
            rw [hlevel, hiter, congrFun h_rank_eq x, h_rank_eq, hroot_eq]
            rwa [UF.rootOf_parent uf x hx] at hextra
          have hphi_drop :=
            phi_setParent_self_drop uf' x root hx_not_root' hr' h_rank h_root_uf'
              hparent_le hnr hextra'
          rw [hphi_eq]; omega
        · -- New level: budget increases by 1
          rw [findBudget_new_level uf x hx_root hr hp hk, hphi_eq]; omega
termination_by uf.rankMax - uf.rank x
decreasing_by
  have h1 := uf.rank_lt x (by rwa [UF.isRoot] at hx_root)
  have h2 := uf.rank_le_max (uf.parent x)
  omega

/-- **Key lemma**: The amortized cost of find is at most alpha(n) + 2. -/
theorem find_amortized (uf : UF n) (x : Fin n)
    (hn : ∀ y, uf.rank y < n) :
    (find uf x).time + Phi ⟪find uf x⟫.2 ≤ Phi uf + alpha n + 2 :=
  (find_Phi_le_budget uf x hn).trans
    (Nat.add_le_add_left (findBudget_le_alpha_add_two uf x hn) _)

/-- The potential increase from linking two roots is at most alpha(n).

  Strategy: Case split on rank comparison. In cases 1 and 2, Phi doesn't increase.
  In case 3, it increases by at most alpha(n). Use Finset.sum_le_sum and
  phi_eq_of_same_data for unchanged nodes, phi_le_alpha_mul_rank for changed nodes. -/
theorem link_Phi_le (uf : UF n) (rx ry : Fin n)
    (hx : uf.isRoot rx) (hy : uf.isRoot ry) (hne : rx ≠ ry)
    (hn : ∀ y, uf.rank y < n) :
    Phi (link uf rx ry hx hne) ≤ Phi uf + alpha n := by
  set uf' := link uf rx ry hx hne with huf'
  unfold Phi
  -- Case split on rank comparison
  by_cases h1 : uf.rank rx < uf.rank ry
  · -- Case 1: rank rx < rank ry. rx attaches under ry. Phi doesn't increase.
    suffices h : ∑ x : Fin n, phi uf' x ≤ ∑ x : Fin n, phi uf x by omega
    apply Finset.sum_le_sum
    intro z _
    by_cases hzrx : z = rx
    · -- z = rx: was root with phi = alpha(n) * rank(rx), now non-root
      subst hzrx
      have : uf'.rank z = uf.rank z := by
        simp [huf', link, h1]
      calc phi uf' z ≤ alpha n * uf'.rank z := phi_le_alpha_mul_rank uf' z
        _ = alpha n * uf.rank z := by rw [this]
        _ = phi uf z := (phi_root uf z hx).symm
    · -- z ≠ rx: parent, rank, isRoot all unchanged
      have hp : uf'.parent z = uf.parent z := by
        simp [huf', link, h1, hzrx]
      have hr : uf'.rank z = uf.rank z := by
        simp [huf', link, h1]
      have hrp : uf'.rank (uf'.parent z) = uf.rank (uf.parent z) := by
        rw [hp]; simp [huf', link, h1]
      exact le_of_eq (phi_eq_of_same_data uf uf' z hp hr hrp)
  · by_cases h2 : uf.rank ry < uf.rank rx
    · -- Case 2: rank ry < rank rx. ry attaches under rx. Phi doesn't increase.
      suffices h : ∑ x : Fin n, phi uf' x ≤ ∑ x : Fin n, phi uf x by omega
      apply Finset.sum_le_sum
      intro z _
      by_cases hzry : z = ry
      · -- z = ry: was root, now non-root
        subst hzry
        have : uf'.rank z = uf.rank z := by
          simp [huf', link, h1, h2]
        calc phi uf' z ≤ alpha n * uf'.rank z := phi_le_alpha_mul_rank uf' z
          _ = alpha n * uf.rank z := by rw [this]
          _ = phi uf z := (phi_root uf z hy).symm
      · -- z ≠ ry: unchanged
        have hp : uf'.parent z = uf.parent z := by
          simp [huf', link, h1, h2, hzry]
        have hr : uf'.rank z = uf.rank z := by
          simp [huf', link, h1, h2]
        have hrp : uf'.rank (uf'.parent z) = uf.rank (uf.parent z) := by
          rw [hp]; simp [huf', link, h1, h2]
        exact le_of_eq (phi_eq_of_same_data uf uf' z hp hr hrp)
    · -- Case 3: rank rx = rank ry. ry attaches under rx, rx rank increases by 1.
      have heq : uf.rank rx = uf.rank ry := by omega
      -- Strategy: ∑ phi(uf',z) = phi(uf',rx) + ∑_{z≠rx} phi(uf',z)
      -- phi(uf',rx) = alpha(n)*(rank(rx)+1) = phi(uf,rx) + alpha(n)
      -- For z ≠ rx: phi(uf',z) ≤ phi(uf,z)
      -- So total ≤ phi(uf,rx) + alpha(n) + ∑_{z≠rx} phi(uf,z) = Phi(uf) + alpha(n)

      -- First, split sum at rx using Finset.add_sum_erase
      have hrx_mem : rx ∈ Finset.univ := Finset.mem_univ rx
      rw [← Finset.add_sum_erase Finset.univ (phi uf') hrx_mem]
      rw [← Finset.add_sum_erase Finset.univ (phi uf) hrx_mem]
      -- phi(uf', rx) = alpha(n) * (rank(rx) + 1) = phi(uf, rx) + alpha(n)
      have hrx_root' : uf'.isRoot rx := link_isRoot_rx_case3 uf rx ry hx hy hne h1 h2
      have hrx_rank' : uf'.rank rx = uf.rank rx + 1 := by
        simp [huf', link, h1, h2]
      have hphi_rx' : phi uf' rx = alpha n * (uf.rank rx + 1) := by
        rw [phi_root uf' rx hrx_root', hrx_rank']
      have hphi_rx : phi uf rx = alpha n * uf.rank rx := phi_root uf rx hx
      have hphi_rx_diff : phi uf' rx = phi uf rx + alpha n := by
        rw [hphi_rx', hphi_rx, Nat.mul_add, Nat.mul_one]
      -- For z ≠ rx: phi(uf', z) ≤ phi(uf, z)
      suffices hrest : ∑ x ∈ Finset.univ.erase rx, phi uf' x ≤
          ∑ x ∈ Finset.univ.erase rx, phi uf x by
        omega
      apply Finset.sum_le_sum
      intro z hz
      have hzrx : z ≠ rx := Finset.ne_of_mem_erase hz
      have hr : uf'.rank z = uf.rank z := by
        simp [huf', link, h1, h2, hzrx]
      by_cases hzry : z = ry
      · -- z = ry: was root, now non-root
        subst hzry
        calc phi uf' z ≤ alpha n * uf'.rank z := phi_le_alpha_mul_rank uf' z
          _ = alpha n * uf.rank z := by rw [hr]
          _ = phi uf z := (phi_root uf z hy).symm
      · -- z ≠ rx, z ≠ ry: parent preserved
        have hp : uf'.parent z = uf.parent z := by
          simp [huf', link, h1, h2, hzry]
        have hrp_ge : uf.rank (uf.parent z) ≤ uf'.rank (uf'.parent z) := by
          rw [hp]
          -- uf'.rank (uf.parent z) uses the rank function from case 3:
          -- if uf.parent z = rx then uf.rank rx + 1 else uf.rank (uf.parent z)
          change uf.rank (uf.parent z) ≤ (link uf rx ry hx hne).rank (uf.parent z)
          simp only [link, h1, h2]
          by_cases hprx : uf.parent z = rx
          · simp [hprx]
          · simp [hprx]
        by_cases hroot_z : uf.isRoot z
        · -- z is a root in uf, still root in uf'
          have hroot_z' : uf'.isRoot z := by
            change uf'.parent z = z; rw [hp]; exact hroot_z
          rw [phi_root uf' z hroot_z', phi_root uf z hroot_z, hr]
        · -- z is non-root in uf
          have hroot_z' : ¬uf'.isRoot z := by
            change ¬(uf'.parent z = z); rw [hp]; exact hroot_z
          by_cases hprx : uf.parent z = rx
          · -- parent(z) = rx: parent-rank increases, use phi_le_of_parent_rank_le
            have hn_par : uf.rank (uf.parent z) < n := hn (uf.parent z)
            exact phi_le_of_parent_rank_le uf uf' z hp hr hrp_ge hroot_z hn_par
          · -- parent(z) ≠ rx: parent-rank unchanged, use phi_eq_of_same_data
            have hrp : uf'.rank (uf'.parent z) = uf.rank (uf.parent z) := by
              rw [hp]
              simp only [huf', link, h1, h2]
              simp [hprx]
            exact le_of_eq (phi_eq_of_same_data uf uf' z hp hr hrp)

/-! ### Stage 5a: Amortized cost of union

Union performs two finds and one link. Its amortized cost is bounded by
`2 × (alpha(n) + 2) + alpha(n) = 3 · alpha(n) + 4`. -/

/-- The amortized cost of union is at most 3 * alpha(n) + 4. -/
theorem union_amortized (uf : UF n) (x y : Fin n)
    (hn : ∀ z, uf.rank z < n) :
    (union uf x y).time + Phi ⟪union uf x y⟫ ≤ Phi uf + 3 * alpha n + 4 := by
  -- Abbreviations
  let uf₁ := ⟪find uf x⟫.2
  let rx := ⟪find uf x⟫.1
  let uf₂ := ⟪find uf₁ y⟫.2
  let ry := ⟪find uf₁ y⟫.1
  -- hn propagates
  have hn₁ : ∀ z, uf₁.rank z < n := fun z => find_ret_rank_eq uf x ▸ hn z
  have hn₂ : ∀ z, uf₂.rank z < n := fun z => find_ret_rank_eq uf₁ y ▸ hn₁ z
  -- find_amortized bounds
  have hf₁ : (find uf x).time + Phi uf₁ ≤ Phi uf + alpha n + 2 := find_amortized uf x hn
  have hf₂ : (find uf₁ y).time + Phi uf₂ ≤ Phi uf₁ + alpha n + 2 := find_amortized uf₁ y hn₁
  -- Key: union is defined as
  -- ⟨if rx = ry then uf₂ else link uf₂ rx ry ..., find₁.time + find₂.time⟩
  -- We proceed by cases on rx = ry
  by_cases hne : rx = ry
  · -- rx = ry: result is uf₂
    -- (union uf x y) = ⟨uf₂, time₁ + time₂⟩ when rx = ry
    have htime : (union uf x y).time = (find uf x).time + (find uf₁ y).time := by
      show (union uf x y).time = (find uf x).time + (find uf₁ y).time
      unfold union
      exact dif_pos hne ▸ rfl
    have hret : ⟪union uf x y⟫ = uf₂ := by
      show (union uf x y).ret = uf₂
      unfold union
      exact dif_pos hne ▸ rfl
    rw [htime, hret]
    have := Nat.add_le_add hf₁ hf₂
    omega
  · -- rx ≠ ry: result is link uf₂ rx ry
    have htime : (union uf x y).time = (find uf x).time + (find uf₁ y).time := by
      show (union uf x y).time = (find uf x).time + (find uf₁ y).time
      unfold union
      exact dif_neg hne ▸ rfl
    rw [htime]
    have hret : ⟪union uf x y⟫ = link uf₂ rx ry
        (find_preserves_roots uf₁ y rx (find_ret_isRoot uf x))
        hne := by
      show (union uf x y).ret = link uf₂ rx ry _ hne
      unfold union
      exact dif_neg hne ▸ rfl
    rw [hret]
    have hlink := link_Phi_le uf₂ rx ry
      (find_preserves_roots uf₁ y rx (find_ret_isRoot uf x))
      (find_ret_isRoot uf₁ y) hne hn₂
    have := Nat.add_le_add hf₁ hf₂
    omega

/-! ### Stage 5b: Telescoping helpers

These lemmas establish that `runOps` (a sequence of find/union operations)
distributes over list append in both the result state and the time cost.
The key telescoping argument (`runOps_amortized_from_init`) sums the per-step
amortized bounds: since each step contributes `≤ 3·alpha(n) + 4` amortized cost,
`m` steps contribute `≤ m · (3·alpha(n) + 4)` total. -/

/-- `runOps` distributes over list append: running `ops₁ ++ ops₂` is the same as
running `ops₁` then running `ops₂` from the resulting state. -/
private theorem runOps_append (uf : UF n) (ops₁ ops₂ : List (Op n)) :
    ⟪runOps uf (ops₁ ++ ops₂)⟫ = ⟪runOps ⟪runOps uf ops₁⟫ ops₂⟫ := by
  induction ops₁ generalizing uf with
  | nil => simp [runOps]
  | cons op rest ih =>
    simp only [List.cons_append, runOps_cons, ret_bind]
    exact ih ⟪runOp uf op⟫

/-- Time of `runOps` distributes over list append. -/
private theorem runOps_time_append (uf : UF n) (ops₁ ops₂ : List (Op n)) :
    (runOps uf (ops₁ ++ ops₂)).time =
      (runOps uf ops₁).time + (runOps ⟪runOps uf ops₁⟫ ops₂).time := by
  induction ops₁ generalizing uf with
  | nil => simp [runOps]
  | cons op rest ih =>
    simp only [List.cons_append, runOps_cons, time_bind, ret_bind]
    rw [ih ⟪runOp uf op⟫]
    omega

/-- The amortized cost of a single `runOp` is at most `3 * alpha n + 4`. -/
private theorem runOp_amortized (uf : UF n) (op : Op n)
    (hn : ∀ z, uf.rank z < n) :
    (runOp uf op).time + Phi ⟪runOp uf op⟫ ≤ Phi uf + (3 * alpha n + 4) := by
  cases op with
  | find x =>
    -- runOp uf (.find x) = (find uf x) >>= fun (_, uf') => pure uf'
    -- time = (find uf x).time, ret = ⟪find uf x⟫.2
    change (find uf x >>= fun p => pure p.2).time +
         Phi (find uf x >>= fun p => pure p.2).ret ≤ Phi uf + (3 * alpha n + 4)
    simp only [time_bind, time_pure, Nat.add_zero, ret_bind, ret_pure]
    have := find_amortized uf x hn
    omega
  | union x y =>
    -- runOp uf (.union x y) = union uf x y
    change (union uf x y).time + Phi ⟪union uf x y⟫ ≤ Phi uf + (3 * alpha n + 4)
    have := union_amortized uf x y hn
    omega

/-- The amortized telescoping lemma: for any state reachable from `init` via `done`,
the total time of the remaining operations `todo` plus the final potential is bounded
by the current potential plus `todo.length * (3 * alpha n + 4)`. -/
private theorem runOps_amortized_from_init (n : ℕ) (hn : 2 ≤ n)
    (done : List (Op n)) (todo : List (Op n)) :
    let uf := ⟪runOps (UF.init n) done⟫
    (runOps uf todo).time + Phi ⟪runOps uf todo⟫ ≤
      Phi uf + todo.length * (3 * alpha n + 4) := by
  induction todo generalizing done with
  | nil =>
    simp [runOps]
  | cons op rest ih =>
    set uf := ⟪runOps (UF.init n) done⟫ with huf_def
    -- rank bound for the current state
    have hrank : ∀ z, uf.rank z < n := fun z => by
      rw [huf_def]; exact rank_lt_of_runOps n hn done z
    -- Unfold one step
    change (runOps uf (op :: rest)).time + Phi ⟪runOps uf (op :: rest)⟫ ≤
         Phi uf + (rest.length + 1) * (3 * alpha n + 4)
    simp only [runOps_cons, time_bind, ret_bind]
    set uf' := ⟪runOp uf op⟫ with huf'_def
    -- uf' is reachable from init via (done ++ [op])
    have huf'_reach : uf' = ⟪runOps (UF.init n) (done ++ [op])⟫ := by
      rw [huf'_def, runOps_append]
      simp only [runOps_cons, ret_bind, runOps_nil, ret_pure]
      rfl
    -- Apply IH with done' = done ++ [op]
    have ih_inst := ih (done ++ [op])
    rw [← huf'_reach] at ih_inst
    -- ih_inst : (runOps uf' rest).time + Phi ⟪runOps uf' rest⟫ ≤
    --           Phi uf' + rest.length * (3 * alpha n + 4)
    -- Single step bound
    have hstep := runOp_amortized uf op hrank
    -- hstep : (runOp uf op).time + Phi ⟪runOp uf op⟫ ≤ Phi uf + (3 * alpha n + 4)
    -- Rewrite to use uf'
    change (runOp uf op).time + Phi uf' ≤ Phi uf + (3 * alpha n + 4) at hstep
    -- Now combine the two inequalities:
    -- ih_inst: (runOps uf' rest).time + Phi ⟪runOps uf' rest⟫ ≤ Phi uf' + rest.length * bound
    -- hstep:   (runOp uf op).time + Phi uf' ≤ Phi uf + bound
    -- Goal:    (runOp uf op).time + (runOps uf' rest).time + Phi ⟪runOps uf' rest⟫ ≤
    --          Phi uf + (rest.length + 1) * bound
    -- From ih_inst: time_rest + Phi_final ≤ Phi_uf' + rest.length * bound
    -- So: time_op + time_rest + Phi_final ≤ time_op + Phi_uf' + rest.length * bound
    -- From hstep: time_op + Phi_uf' ≤ Phi_uf + bound
    -- So: time_op + time_rest + Phi_final ≤ Phi_uf + bound + rest.length * bound
    --                                     = Phi_uf + (rest.length + 1) * bound
    -- Simplify the `let` in ih_inst
    simp only at ih_inst
    -- Rewrite the (rest.length + 1) * B in the goal using Nat.add_mul
    have hexpand : (rest.length + 1) * (3 * alpha n + 4) =
        rest.length * (3 * alpha n + 4) + (3 * alpha n + 4) := by
      rw [Nat.add_mul, Nat.one_mul]
    rw [hexpand]
    -- Goal: time_op + time_rest + Phi_final ≤ Phi_uf + rest.length * B + B
    -- hstep:   time_op + Phi_uf' ≤ Phi_uf + B
    -- ih_inst: time_rest + Phi_final ≤ Phi_uf' + rest.length * B
    -- Combine via Nat.add_le_add then omega for linear cancellation
    have combined := Nat.add_le_add hstep ih_inst
    omega

/-! ### Stage 5c: Main theorem

The final step: since `Φ_init = 0` (all nodes are roots with rank 0) and
`Φ_final ≥ 0` (Φ is a sum of ℕ values), the total actual cost is bounded by
the total amortized cost. -/

/-- **Main theorem**: m operations on n elements cost at most m * (3 * alpha(n) + 4).

This is O(m * alpha(n)), the inverse-Ackermann amortized bound for union-find
with path compression and union by rank. -/
theorem union_find_amortized (n : ℕ) (hn : 2 ≤ n) (ops : List (Op n)) :
    (runOps (UF.init n) ops).time ≤ ops.length * (3 * alpha n + 4) := by
  -- Use the amortized lemma with empty prefix (done = [])
  have h := runOps_amortized_from_init n hn [] ops
  simp only [runOps_nil, ret_pure] at h
  -- h : (runOps (init n) ops).time + Phi ⟪runOps (init n) ops⟫ ≤
  --      Phi (init n) + ops.length * (3 * alpha n + 4)
  have h_init : Phi (UF.init n) = 0 := Phi_init
  rw [h_init] at h
  -- h : time + Phi_final ≤ 0 + ops.length * bound
  -- Since Phi_final ≥ 0 (ℕ): time ≤ ops.length * bound
  omega

end Cslib.Algorithms.Lean.UnionFind
