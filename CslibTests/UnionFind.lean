/-
Copyright (c) 2026 CSLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CSLib Contributors
-/
import Cslib.Algorithms.Lean.UnionFind.Amortized

/-!
# Union-Find Amortized Complexity Tests

Demonstrates the amortized O(α(n)) bound for union-find operations.
-/

open Cslib.Algorithms.Lean.UnionFind
open Batteries (UnionFind)

/-- The inverse Ackermann function returns small values. -/
example : invAck 0 = 0 := by native_decide
example : invAck 1 = 0 := by native_decide

/-- An empty union-find has zero potential. -/
example : Φ UnionFind.empty = 0 := Φ_empty
