/-
Copyright (c) 2026 Juan Bono. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Bono
-/

import Cslib.Algorithms.Lean.UnionFind.Operations

namespace CslibTests

set_option linter.style.nativeDecide false

open Cslib.Algorithms.Lean.UnionFind
open Cslib.Algorithms.Lean.TimeM

/-!
# Union-Find Tests

Verified examples exercising the Union-Find implementation on concrete inputs.

## Test scenarios
- Initialization: every element is its own root with rank 0
- Single union: merging two elements into one equivalence class
- Multiple unions: building and merging distinct classes
- Find: returns a root, preserves equivalence classes
- Rank behavior: union-by-rank bookkeeping
- Idempotent union: re-unioning already-connected elements
- Operation sequences via `runOps`
-/

/-! ### Test states on 5 elements -/

/-- Fresh UF: all singletons. -/
private def uf₀ : UF 5 := UF.init 5

/-- After union(0, 1): {0,1}, {2}, {3}, {4}. -/
private def uf₁ : UF 5 := ⟪union uf₀ 0 1⟫

/-- After union(2, 3): {0,1}, {2,3}, {4}. -/
private def uf₂ : UF 5 := ⟪union uf₁ 2 3⟫

/-- After union(0, 2): {0,1,2,3}, {4}. -/
private def uf₃ : UF 5 := ⟪union uf₂ 0 2⟫

/-! ### Initialization -/

example : uf₀.isRoot 0 := by native_decide
example : uf₀.isRoot 1 := by native_decide
example : uf₀.isRoot 4 := by native_decide

example : uf₀.rootOf 0 = 0 := by native_decide
example : uf₀.rootOf 3 = 3 := by native_decide

example : uf₀.rank 0 = 0 := by native_decide
example : uf₀.rank 4 = 0 := by native_decide

/-! ### Single union: union(0, 1) -/

-- 0 and 1 now share the same root
example : uf₁.rootOf 0 = uf₁.rootOf 1 := by native_decide

-- The other elements remain in their own classes
example : uf₁.rootOf 2 = 2 := by native_decide
example : uf₁.rootOf 3 = 3 := by native_decide
example : uf₁.rootOf 4 = 4 := by native_decide

-- 0 is still separate from 2
example : uf₁.rootOf 0 ≠ uf₁.rootOf 2 := by native_decide

/-! ### Two disjoint unions: {0,1} and {2,3} -/

-- Each pair shares a root
example : uf₂.rootOf 0 = uf₂.rootOf 1 := by native_decide
example : uf₂.rootOf 2 = uf₂.rootOf 3 := by native_decide

-- The two classes are still disjoint
example : uf₂.rootOf 0 ≠ uf₂.rootOf 2 := by native_decide

-- 4 is still a singleton
example : uf₂.rootOf 4 = 4 := by native_decide

/-! ### Merging two classes: union(0, 2) joins {0,1} and {2,3} -/

-- All four elements now share the same root
example : uf₃.rootOf 0 = uf₃.rootOf 1 := by native_decide
example : uf₃.rootOf 0 = uf₃.rootOf 2 := by native_decide
example : uf₃.rootOf 0 = uf₃.rootOf 3 := by native_decide

-- 4 is still separate
example : uf₃.rootOf 0 ≠ uf₃.rootOf 4 := by native_decide

/-! ### Find returns a root and preserves rootOf -/

-- find on a root returns that root
example : (⟪find uf₀ 0⟫).1 = 0 := by native_decide

-- find on a non-root returns its root
example : (⟪find uf₁ 1⟫).1 = uf₁.rootOf 1 := by native_decide

-- find preserves rootOf for other elements
example : (⟪find uf₂ 2⟫).2.rootOf 0 = uf₂.rootOf 0 := by native_decide
example : (⟪find uf₂ 2⟫).2.rootOf 3 = uf₂.rootOf 3 := by native_decide
example : (⟪find uf₂ 0⟫).2.rootOf 4 = uf₂.rootOf 4 := by native_decide

-- find preserves ranks (checked pointwise since function equality is not decidable)
example : (⟪find uf₁ 1⟫).2.rank 0 = uf₁.rank 0 := by native_decide
example : (⟪find uf₁ 1⟫).2.rank 1 = uf₁.rank 1 := by native_decide

/-! ### Rank behavior (union by rank) -/

-- After unioning two rank-0 elements, the winner gets rank 1
example : uf₁.rank 0 = 1 := by native_decide
example : uf₁.rank 1 = 0 := by native_decide

-- After two equal-rank unions, both winners have rank 1
example : uf₂.rank 0 = 1 := by native_decide
example : uf₂.rank 2 = 1 := by native_decide

-- After merging two rank-1 roots, the winner gets rank 2
example : uf₃.rank 0 = 2 := by native_decide

/-! ### Idempotent union: re-unioning already-connected elements -/

private def uf_idem : UF 5 := ⟪union uf₁ 0 1⟫

-- Roots are unchanged
example : uf_idem.rootOf 0 = uf₁.rootOf 0 := by native_decide
example : uf_idem.rootOf 1 = uf₁.rootOf 1 := by native_decide

-- Rank is unchanged (no spurious increment)
example : uf_idem.rank 0 = uf₁.rank 0 := by native_decide

/-! ### Operation sequences via runOps -/

private def ops₁ : List (Op 5) := [.union 0 1, .union 2 3, .union 0 2, .find 3]
private def uf_ops₁ : UF 5 := ⟪runOps (UF.init 5) ops₁⟫

-- After the sequence, 0 and 3 share a root
example : uf_ops₁.rootOf 0 = uf_ops₁.rootOf 3 := by native_decide

-- 4 is still isolated
example : uf_ops₁.rootOf 0 ≠ uf_ops₁.rootOf 4 := by native_decide

-- Applying the same ops gives the same result as the manual chain
example : uf_ops₁.rootOf 0 = uf₃.rootOf 0 := by native_decide
example : uf_ops₁.rootOf 4 = uf₃.rootOf 4 := by native_decide

/-! ### Time cost accounting -/

-- find on a root costs 0 ticks
example : (find uf₀ 0).time = 0 := by native_decide

-- find on a depth-1 node costs 1 tick (one parent-pointer follow)
example : (find uf₁ 1).time = 1 := by native_decide

end CslibTests
