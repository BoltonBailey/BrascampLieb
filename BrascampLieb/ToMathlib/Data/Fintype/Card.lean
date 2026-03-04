/-
Copyright (c) 2025 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey and Numina team
-/

import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Basic

/-- The cardinality of a finite type is the cardinality of the image of an injective map from it. -/
lemma Fintype.card_eq_finsetCard_of_inj {α β} [Fintype α] (f : α ↪ β) :
    Fintype.card α = (Finset.univ.map f).card := by
  classical
  rw [Fintype.card, Finset.card_map, Finset.card_univ]
