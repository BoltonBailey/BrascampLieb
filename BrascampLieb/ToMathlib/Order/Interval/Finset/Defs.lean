import Mathlib.Order.Interval.Finset.Defs

lemma Finset.Iio_union_Ioi {ι} [Fintype ι] [LinearOrder ι] [LocallyFiniteOrderBot ι]
    [LocallyFiniteOrderTop ι] [DecidableEq ι] (i : ι) :
    (Finset.Iio i) ∪ (Finset.Ioi i) = Finset.univ \ {i} := by grind
