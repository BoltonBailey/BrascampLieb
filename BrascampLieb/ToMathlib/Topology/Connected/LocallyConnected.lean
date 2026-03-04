import Mathlib.Topology.Bases
import Mathlib.Topology.Connected.LocallyConnected
import BrascampLieb.ToMathlib.Topology.Connected.Basic

open Set

-- Note: this theorem is needed in a blueprint, but is also suitable for mathlib.
theorem IsOpen.countable_connectedComponentsIn' {α : Type*}
    [TopologicalSpace α] [LocallyConnectedSpace α] [TopologicalSpace.SeparableSpace α]
    {s : Set α} (s_open : IsOpen s) :
    Countable (connectedComponentsIn s) := by
  apply Set.PairwiseDisjoint.countable_of_isOpen (α := α) (s := id)
  · exact connectedComponentsIn_pairwiseDisjoint
  · rintro _ ⟨_, _, rfl⟩
    exact s_open.connectedComponentIn
  · rintro _ ⟨x, hx_in, rfl⟩
    use x, mem_connectedComponentIn hx_in
