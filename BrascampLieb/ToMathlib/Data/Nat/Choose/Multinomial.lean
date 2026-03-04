import Mathlib.Data.Nat.Cast.Field
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Rat.Star
import Mathlib.Tactic.Qify

namespace Nat

/--
Alternative form of expressing binomial coefficients, more conducive to positivity proofs
since it avoids natural number subtraction.

Note: Possibly a better name would be `binom` or `binomial`,
but this would cause a clash with theorem names in Mathlib.Data.Nat.Choose.Multinomial,
which use the "binomial" terminology,
(even though there is currently no `binomial` definition in Mathlib).

Perhaps the best course of action would be to rename the theorems in
Mathlib.Data.Nat.Choose.Multinomial to something else and then add this as `binomial` later.
-/
def binom (a b : ℕ) : ℕ := Nat.choose (a + b) a

@[simp]
lemma binom_eq_choose (a b : ℕ) : binom a b = Nat.choose (a + b) a := rfl

lemma binom_symm (a b : ℕ) : binom a b = binom b a := by
  simpa [add_comm] using choose_symm_add

theorem binom_pos (a b : ℕ) : 0 < binom a b := Nat.choose_pos (le_add_right a b)

theorem binom_eq_factorial_div_factorial (a b : ℕ) : binom a b =
    (a + b)! / (a ! * b !) := by simp [choose_eq_factorial_div_factorial]

theorem Rat.binom_eq_factorial_div_factorial (a b : ℕ) :
    (binom a b : ℚ) = (a + b)! / (a ! * b !) := by
  rw [← Nat.cast_mul, ← Nat.cast_div (factorial_mul_factorial_dvd_factorial_add a b)
    (by simp [factorial_ne_zero])]
  exact congr_arg _ <| Nat.binom_eq_factorial_div_factorial _ _

theorem binom_eq_multinomial (a b : ℕ) :
    binom a b = Nat.multinomial (Finset.univ) ![a, b] := by
  simp [multinomial_univ_two, choose_eq_factorial_div_factorial]

section PositivityExtension

open Lean Meta Mathlib Meta Positivity Qq in
/-- The `positivity` extension which identifies expressions of the form `binom a b`. -/
@[positivity binom (_ : ℕ) (_ : ℕ)]
def evalBinom : PositivityExt where eval {u α} _zα _pα e := do
  match u, α, e with
  | 0, ~q(ℕ), ~q(binom $a $b) =>
    assertInstancesCommute
    return .positive q(binom_pos $a $b)
  | _, _, _ => throwError "not binom"

end PositivityExtension

lemma add_one_mul_choose_add_one_self (m : ℕ) : (m + 1) * (binom (m + 1) m) =
    (2 * m + 1) * (binom m m) := by
  qify [Rat.binom_eq_factorial_div_factorial]
  simpa [factorial_succ, show (m + 1 + m)! = (2 * m + 1)! by ring_nf, show (m + m)! = (2 * m)! by
    ring_nf] using by field_simp
