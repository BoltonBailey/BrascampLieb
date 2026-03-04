import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

open MeasureTheory

lemma ProbabilityMeasure.apply_compl {Z : Type*} [MeasurableSpace Z]
    (μ : ProbabilityMeasure Z) (A : Set Z) (A_mble : MeasurableSet A) :
    μ Aᶜ = 1 - μ A := by
  suffices μ.toMeasure Aᶜ = 1 - μ.toMeasure A by
    simp [ProbabilityMeasure.coeFn_def, this]
  simp [measure_compl A_mble]
