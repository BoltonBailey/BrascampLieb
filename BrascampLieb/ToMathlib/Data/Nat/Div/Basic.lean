import Mathlib.Algebra.GroupWithZero.Divisibility
import Mathlib.Algebra.GroupWithZero.Nat

namespace Nat

lemma dvd_div_of_mul_dvd_left (a b c : ℕ) (habc : a * b ∣ c) : a ∣ c / b := by
  if hb : b = 0 then simp_all else
  obtain ⟨x, hx⟩ := habc
  exact ⟨x, hx ▸ mul_right_comm a b x ▸ by grind [Nat.mul_div_cancel]⟩
