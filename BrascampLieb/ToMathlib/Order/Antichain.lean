/-
Copyright (c) 2025 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey and Numina team
-/
import Mathlib.Order.Antichain

variable {P : Type*} [PartialOrder P]

/-- The empty set is an antichain. -/
lemma IsAntichain_empty : IsAntichain (· ≤ ·) (∅ : Set P) := by
  simp [IsAntichain]
