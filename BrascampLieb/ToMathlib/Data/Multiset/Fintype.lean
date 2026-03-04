import Mathlib.Data.Multiset.Fintype

@[to_additive]
lemma Multiset.prod_map_eq_prod_toType {α β : Type*} [DecidableEq α] [CommMonoid β]
    (s : Multiset α) (f : α → β) :
    (s.map f).prod = ∏ a : s.ToType, f a := by
  congr 1
  simp
