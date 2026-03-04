import Mathlib.Topology.Connected.Basic

open Set

lemma connectedComponentIn_eq_of_nonempty_inter {α : Type*} [TopologicalSpace α] {s : Set α}
    {x y : α} (h : (connectedComponentIn s x ∩ connectedComponentIn s y).Nonempty) :
    connectedComponentIn s x = connectedComponentIn s y := by
  obtain ⟨z, hzx, hzy⟩ := h
  rw [connectedComponentIn_eq hzy, connectedComponentIn_eq hzx]

/--
The set of connected components of a set `s` in a topological space `α`.
-/
def connectedComponentsIn {α : Type*} [TopologicalSpace α] (s : Set α) : Set (Set α) :=
    {C | ∃ x ∈ s, C = connectedComponentIn s x}

theorem connectedComponentsIn_pairwiseDisjoint {α : Type*} [TopologicalSpace α]
    {s : Set α} : (connectedComponentsIn s).PairwiseDisjoint id := by
  rintro i1 ⟨x, hx_in, rfl⟩ i2 ⟨y, hy_in, rfl⟩ hneq i_inter inter_1 inter_2
  simp_all only [ne_eq, id_eq, le_eq_subset, bot_eq_empty, subset_empty_iff]
  contrapose! hneq
  obtain ⟨z, hz⟩ := hneq
  exact connectedComponentIn_eq_of_nonempty_inter ⟨z, inter_1 hz, inter_2 hz⟩
