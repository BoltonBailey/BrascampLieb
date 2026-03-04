import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Data.Matrix.Mul

/-- Eigenspace of a matrix and a scalar `r` consists all vectors in `R^n` such that
  `A • v = r • v`. -/
@[simp]
def Matrix.eigenspace {R n : Type*} [CommRing R] [Fintype n] (A : Matrix n n R)
    (r : R) : Submodule R (n → R) where
  carrier := {v : n → R | A.mulVec v = r • v}
  add_mem' := by simp +contextual [mulVec_add]
  zero_mem' := by simp
  smul_mem' := by simp +contextual [mulVec_smul, ← SemigroupAction.mul_smul, mul_comm]

/-- A scalar `μ` is an eigenvalue for a matrix `A` if there are nonzero vectors `x`
  such that `A • x = μ • x`. -/
def Matrix.HasEigenValue {R n : Type*} [CommRing R] [Fintype n] (A : Matrix n n R) (r : R) :
  Prop := A.eigenspace r ≠ ⊥
