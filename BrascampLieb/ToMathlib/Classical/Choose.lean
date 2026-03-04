/-
Copyright (c) 2025 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey and Numina team
-/
import Mathlib.Logic.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Defs

universe u

variable {P : Type u}

namespace Classical

/-- If a nonempty set is a subset of a finset, then the chosen element belongs to the finset. -/
lemma choose_mem_of_finset_subset {S : Set P} {hS : S.Nonempty} (S' : Finset P)
    (hSS' : S ⊆ SetLike.coe S') : (hS.choose : P) ∈ S' := by
  convert hSS' hS.choose_spec

/-- A variant of choose_spec that applies a implication. -/
lemma choose_spec_of {α : Sort u} {p q : α → Prop} (h : ∃ (x : α), p x)
    (hpq : ∀ x, p x → q x) :
    q (choose h) := hpq _ (choose_spec h)

/-- A variant of choose_spec that applies a biconditional. -/
lemma choose_spec_iff {α : Sort u} {p q : α → Prop} (h : ∃ (x : α), p x)
    (hpq : ∀ x, p x ↔ q x) :
    q (choose h) :=
  (hpq _).mp (choose_spec h)

end Classical
