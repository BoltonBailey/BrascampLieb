import Mathlib.Order.SetNotation
import Mathlib.Data.Set.Basic

-- Note: similar lemmas could be added
theorem inter_sUnion {α} {A : Set α} (I : Set (Set α)) :
    A ∩ ⋃₀ I = ⋃ i ∈ I, A ∩ i := by
  ext x
  simp
