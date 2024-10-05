import Mathlib.Data.Nat.Prime

import Mathlib.Data.Nat.Factorial.Basic

-- Open the natural numbers namespace
open Nat

theorem infinitely_many_primes : ∀ N, ∃ p, p ≥ N ∧ Prime p := by
  intro N
  let M := (factorial N) + 1
  have hM : M > 1 := by
    apply Nat.succ_lt_succ
    apply factorial_pos
  have h_prime_divisor : ∃ p, p ∣ M ∧ Prime p := Nat.exists_prime_and_dvd hM
  rcases h_prime_divisor with ⟨p, hpM, hp_prime⟩
  use p
  constructor
  · by_contradiction h
    have h1 : p ≤ N := le_of_not_ge h
    have h2 : p ∣ factorial N := Nat.Prime.dvd_factorial hp_prime h1
    have h3 : p ∣ 1 := Nat.dvd_of_dvd_add_right h2 hpM
    have h4 : p = 1 := Nat.Prime.eq_one_of_dvd_one hp_prime h3
    exact Nat.Prime.ne_one hp_prime h4
  · exact hp_prime
