import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic

/-! The harmonic-number calculation for the first magic coefficient of a
generalized parking-function polytope, in arbitrary dimension. -/

namespace ParkingMagicFirst

def harmonic : Nat → ℚ
  | 0 => 0
  | n + 1 => harmonic n + 1 / ((n : ℚ) + 1)

private theorem harmonic_succ (n : Nat) :
    harmonic (n + 1) = harmonic n + 1 / ((n : ℚ) + 1) := rfl

theorem harmonic_mono : Monotone harmonic := by
  apply monotone_nat_of_le_succ
  intro n
  change harmonic n ≤ harmonic n + 1 / ((n : ℚ) + 1)
  have h : 0 ≤ (1 : ℚ) / ((n : ℚ) + 1) := by positivity
  linarith

def difference (f : Nat → ℚ) : Nat → Nat → ℚ
  | 0, m => f m
  | k + 1, m => difference f k m - difference f k (m + 1)

theorem difference_expansion (f : Nat → ℚ) (k m : Nat) :
    difference f k m =
      ∑ i ∈ Finset.range (k + 1), (-1 : ℚ)^i * (k.choose i : ℚ) * f (m+i) := by
  induction k generalizing m with
  | zero => simp [difference]
  | succ k ih =>
    let a := fun i : Nat => (-1 : ℚ)^i * (k.choose i : ℚ) * f (m+i)
    let b := fun i : Nat => (-1 : ℚ)^i * (k.choose i : ℚ) * f (m+1+i)
    let c := fun i : Nat => (-1 : ℚ)^i * ((k+1).choose i : ℚ) * f (m+i)
    have a0 : a 0 = f m := by simp [a]
    have aend : a (k+1) = 0 := by simp [a, Nat.choose_eq_zero_of_lt (Nat.lt_succ_self k)]
    have c0 : c 0 = f m := by simp [c]
    have shifted : ∑ i ∈ Finset.range (k+1), a (i+1) =
        (∑ i ∈ Finset.range (k+1), a i) - f m := by
      rw [Finset.sum_range_succ (fun i => a (i+1)) k, aend, add_zero,
        Finset.sum_range_succ' a k, a0, add_sub_cancel_right]
    rw [difference, ih m, ih (m+1)]
    change (∑ i ∈ Finset.range (k+1), a i) - (∑ i ∈ Finset.range (k+1), b i) =
      ∑ i ∈ Finset.range (k+2), c i
    rw [Finset.sum_range_succ' c (k+1), c0]
    have split : ∑ i ∈ Finset.range (k+1), c (i+1) =
        ∑ i ∈ Finset.range (k+1), (a (i+1) - b i) := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [a, b, c, Nat.choose_succ_succ', Nat.cast_add, pow_succ,
        show m+1+i = m+(i+1) by omega]
      ring
    rw [split, Finset.sum_sub_distrib, shifted]
    ring

private def beta (m k : Nat) : ℚ :=
  (m.factorial : ℚ) * (k.factorial : ℚ) / ((m + k + 1).factorial : ℚ)

private theorem beta_succ_left (m k : Nat) :
    beta (m + 1) k = beta m k * ((m : ℚ) + 1) / ((m : ℚ) + k + 2) := by
  unfold beta
  rw [show m + 1 + k + 1 = (m + k + 1) + 1 by omega,
    Nat.factorial_succ (m + k + 1), Nat.factorial_succ m]
  push_cast
  have h : ((m + k + 1).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  field_simp; ring

private theorem beta_succ_right (m k : Nat) :
    beta m (k + 1) = beta m k * ((k : ℚ) + 1) / ((m : ℚ) + k + 2) := by
  unfold beta
  rw [show m + (k + 1) + 1 = (m + k + 1) + 1 by omega,
    Nat.factorial_succ (m + k + 1), Nat.factorial_succ k]
  push_cast
  have h : ((m + k + 1).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  field_simp; ring

/-- `g(m)` stands for `(1 + H_(m+1))/(m+1)`. -/
def g (m : Nat) : ℚ := (1 + harmonic (m+1)) / ((m : ℚ) + 1)

theorem harmonic_difference (m k : Nat) :
    difference g k m = beta m k * (1 + harmonic (m+k+1) - harmonic k) := by
  induction k generalizing m with
  | zero =>
    simp only [difference, g, beta, Nat.factorial_zero, Nat.cast_one, mul_one, Nat.add_zero,
      harmonic, sub_zero, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add]
    have h : (m.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    field_simp; ring
  | succ k ih =>
    rw [difference, ih m, ih (m+1), beta_succ_left, beta_succ_right]
    rw [show m + 1 + k + 1 = (m + k + 1) + 1 by omega,
      show m + (k + 1) + 1 = (m + k + 1) + 1 by omega]
    rw [harmonic_succ (m+k+1), harmonic_succ k]
    push_cast
    have hk : ((k : ℚ) + 1) ≠ 0 := by positivity
    have hmk : ((m : ℚ) + k + 2) ≠ 0 := by positivity
    field_simp; ring

theorem harmonic_difference_pos (m k : Nat) : 0 < difference g k m := by
  rw [harmonic_difference]
  have increasing : harmonic k ≤ harmonic (m+k+1) := harmonic_mono (by omega)
  have beta_pos : 0 < beta m k := by
    unfold beta
    positivity
  exact mul_pos beta_pos (by linarith)

/-- Cancel the factorials in the weight of parameter `j = m + 2` in
dimension `n = m + k + 2`. -/
theorem parameter_weight (m k : Nat) :
    ((m+k+2).choose (m+2) : ℚ) * ((m : ℚ)+2) * ((m : ℚ)+1) * difference g (k+1) m =
      ((k : ℚ)+1) * (1 + harmonic (m+k+2) - harmonic (k+1)) := by
  have choose_factorials := Nat.choose_mul_factorial_mul_factorial
    (n := m+k+2) (k := m+2) (by omega)
  rw [show m+k+2-(m+2) = k by omega] at choose_factorials
  have choose_factorials_q :
      ((m+k+2).choose (m+2) : ℚ) * ((m+2).factorial : ℚ) * (k.factorial : ℚ) =
        ((m+k+2).factorial : ℚ) := by exact_mod_cast choose_factorials
  have factorial_m : ((m+2).factorial : ℚ) =
      ((m : ℚ)+2) * ((m : ℚ)+1) * (m.factorial : ℚ) := by
    rw [Nat.factorial_succ (m+1), Nat.factorial_succ m]
    push_cast
    ring
  have factor : ((m+k+2).choose (m+2) : ℚ) * ((m : ℚ)+2) * ((m : ℚ)+1) *
      beta m (k+1) = (k : ℚ)+1 := by
    unfold beta
    rw [show m+(k+1)+1 = m+k+2 by omega, Nat.factorial_succ k, Nat.cast_mul,
      Nat.cast_add, Nat.cast_one]
    calc
      _ = ((k : ℚ)+1) *
          (((m+k+2).choose (m+2) : ℚ) * ((m+2).factorial : ℚ) * (k.factorial : ℚ)) /
            ((m+k+2).factorial : ℚ) := by rw [factorial_m]; ring
      _ = _ := by
        rw [choose_factorials_q, mul_div_cancel_right₀]
        exact_mod_cast Nat.factorial_ne_zero _
  rw [harmonic_difference, show m+(k+1)+1 = m+k+2 by omega, ← mul_assoc, factor]

/-- Positivity of the closed form for the first magic coefficient,
where the variables `x` are the nonnegative shifts of the parking parameters. -/
theorem first_magic_pos (n : Nat) (hn : 3 ≤ n) (x : Nat → ℚ) (hx : ∀ j, 0 ≤ x j) :
    0 < (n : ℚ) * (3 * n - 7) / 4 + n * x 1 +
      ∑ j ∈ Finset.Icc 2 n,
        (↑(n-j+1) : ℚ) * (1 + harmonic n - harmonic (n-j+1)) * x j := by
  have hc : (3 : ℚ) ≤ n := by exact_mod_cast hn
  have constant_pos : 0 < (n : ℚ) * (3 * n - 7) / 4 :=
    div_pos (mul_pos (by linarith) (by linarith)) (by norm_num)
  have sum_nonneg : 0 ≤ ∑ j ∈ Finset.Icc 2 n,
      (↑(n-j+1) : ℚ) * (1 + harmonic n - harmonic (n-j+1)) * x j := by
    apply Finset.sum_nonneg
    intro j hj
    have h : n-j+1 ≤ n := by have := (Finset.mem_Icc.mp hj).1; omega
    have hm := harmonic_mono h
    exact mul_nonneg (mul_nonneg (by positivity) (by linarith)) (hx j)
  exact add_pos_of_pos_of_nonneg
    (add_pos_of_pos_of_nonneg constant_pos (mul_nonneg (by positivity) (hx 1))) sum_nonneg

#print axioms harmonic_difference
#print axioms difference_expansion
#print axioms parameter_weight
#print axioms first_magic_pos

end ParkingMagicFirst
