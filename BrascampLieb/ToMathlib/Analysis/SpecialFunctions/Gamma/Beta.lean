
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import BrascampLieb.ToMathlib.Data.Nat.Choose.Multinomial

open Nat

/--
Theorem expressing the Beta Integral in terms of the Gamma function.
-/
theorem Complex.betaIntegral_eq_Gamma {s t : ℂ} (hs : 0 < re s) (ht : 0 < re t) :
    betaIntegral s t = Gamma s * Gamma t / Gamma (s + t) := Gamma_mul_Gamma_eq_betaIntegral hs ht ▸
  (mul_div_cancel_left₀ _ <| Gamma_ne_zero <| fun n h ↦ by
  linarith [(congr(re $h) : s.re + t.re = - (n : ℝ))]).symm

/--
Theorem expressing the Beta Integral on Naturals in terms of the factorial function.
-/
lemma Complex.betaIntegral_eq_factorial_mul_div (s t : ℕ) (hs : 0 < s) (ht : 0 < t) :
    Complex.betaIntegral (s : ℂ) (t : ℂ) = ((s - 1) !) * (t - 1) ! / (s + t - 1) ! :=
  @Complex.betaIntegral_eq_Gamma s t (by simpa) (by simpa) ▸ by
    simp_all [← Complex.Gamma_nat_eq_factorial]

lemma Complex.betaIntegral_eq_div_binom (s t : ℕ) (hs : 0 < s) (ht : 0 < t) :
    Complex.betaIntegral (s : ℂ) (t : ℂ) = (s + t) / (s * t * Nat.binom s t) :=
  Complex.betaIntegral_eq_factorial_mul_div s t hs ht ▸ by
  suffices ((s - 1)! * (t - 1)! / (s + t - 1)! : ℚ) = (↑s + ↑t) / (↑s * ↑t * ↑(s.binom t)) by
    simpa using congr(Rat.cast (K := ℂ) $this)
  rw [Rat.binom_eq_factorial_div_factorial, eq_div_iff (by positivity), ← mul_assoc,
    div_mul_eq_mul_div, mul_assoc, mul_comm ((t - 1)! : ℚ), ← mul_assoc, ← mul_assoc, ← cast_mul,
    mul_comm _ s]
  nth_rw 1 [← Nat.sub_add_cancel hs, ← factorial_succ, Nat.sub_add_cancel hs, mul_assoc, ← cast_mul,
    ← Nat.sub_add_cancel ht, ← factorial_succ, Nat.sub_add_cancel ht, _root_.div_mul_div_comm]
  field_simp
  rw [← @Nat.sub_add_cancel (s + t) 1 (by grind), factorial_succ, Nat.sub_add_cancel (by grind)]
  grind
