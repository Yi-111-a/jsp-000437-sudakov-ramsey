import Mathlib

namespace JSP437

/-- Crude arithmetic bound used for the Ramsey edge-count estimate:
`2m ≤ 2 ^ (250 * √m)` for all `m : ℕ` (with `Nat.sqrt`). -/
theorem two_mul_le_two_pow_250_mul_sqrt (m : ℕ) :
    2 * m ≤ 2 ^ (250 * m.sqrt) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · -- For `m ≥ 1` we have `s := m.sqrt ≥ 1`.
    have hs1 : 1 ≤ m.sqrt := Nat.sqrt_pos.2 hm
    -- `m < (s + 1)^2`.
    have h1 : m < (m.sqrt + 1) ^ 2 := Nat.lt_succ_sqrt' m
    -- `s + 1 ≤ 2 ^ (s + 1)` since `n < 2 ^ n`.
    have h2 : m.sqrt + 1 ≤ 2 ^ (m.sqrt + 1) :=
      (Nat.lt_two_pow_self : m.sqrt + 1 < 2 ^ (m.sqrt + 1)).le
    -- `(s + 1)^2 ≤ (2 ^ (s + 1))^2`.
    have h3 : (m.sqrt + 1) ^ 2 ≤ (2 ^ (m.sqrt + 1)) ^ 2 :=
      pow_le_pow_left' h2 2
    -- `(2 ^ (s + 1))^2 = 2 ^ (2s + 2)`.
    have hpow : (2 ^ (m.sqrt + 1)) ^ 2 = 2 ^ (2 * m.sqrt + 2) := by
      rw [← pow_mul]
      congr 1
      ring
    -- `2 * 2 ^ (2s + 2) = 2 ^ (2s + 3)`.
    have step : 2 * 2 ^ (2 * m.sqrt + 2) = 2 ^ (2 * m.sqrt + 3) := by
      calc 2 * 2 ^ (2 * m.sqrt + 2) = 2 ^ 1 * 2 ^ (2 * m.sqrt + 2) := by
            rw [pow_one]
        _ = 2 ^ (1 + (2 * m.sqrt + 2)) := by rw [← pow_add]
        _ = 2 ^ (2 * m.sqrt + 3) := by congr 1; omega
    -- Assemble the chain; `2s + 3 ≤ 250s` for `s ≥ 1`.
    calc 2 * m ≤ 2 * ((m.sqrt + 1) ^ 2) := Nat.mul_le_mul_left 2 h1.le
      _ ≤ 2 * ((2 ^ (m.sqrt + 1)) ^ 2) := Nat.mul_le_mul_left 2 h3
      _ = 2 * 2 ^ (2 * m.sqrt + 2) := by rw [hpow]
      _ = 2 ^ (2 * m.sqrt + 3) := step
      _ ≤ 2 ^ (250 * m.sqrt) := pow_le_pow_right' (by norm_num) (by omega)

end JSP437
