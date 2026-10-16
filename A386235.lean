import Mathlib.Tactic
import Mathlib.Data.Int.Interval
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
Formalization of the arithmetic and analytic steps for OEIS A386235.
The complete asymptotic theorem and an explicit error bound are proved below.
All proof terms are checked by Lean; no sorry or extra axioms are used.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace A386235

open Finset

/-- Eliminate p using the equation p + q + r = n. -/
theorem eliminate_p (n m p q r : ℤ) (hsum : p + q + r = n) :
    p + 11 * q + 13 * r = m ^ 2 ↔ n + 10 * q + 12 * r = m ^ 2 := by
  constructor <;> intro h <;> linarith

/-- A square root and n must have the same parity. -/
theorem root_parity (n m p q r : ℤ) (hsum : p + q + r = n)
    (hsq : p + 11 * q + 13 * r = m ^ 2) : m % 2 = n % 2 := by
  have h := (eliminate_p n m p q r hsum).mp hsq
  have hm : m ^ 2 % 2 = m % 2 := by
    have hm' : m % 2 = 0 ∨ m % 2 = 1 := by omega
    rcases hm' with hm' | hm' <;> simp [pow_two, Int.mul_emod, hm']
  omega

/-- Solutions of the linear Diophantine equation at one square-root slice. -/
def pairs (n s : ℤ) : Finset (ℤ × ℤ) :=
  ((Icc 0 n).product (Icc 0 n)).filter
    (fun qr => qr.1 + qr.2 ≤ n ∧ 5 * qr.1 + 6 * qr.2 = s)

theorem pairs_card_interval (n s : ℤ) :
    (pairs n s).card = (Icc ((s + 5) / 6) (min n (s / 5))).card := by
  apply Finset.card_bij (fun qr _ => qr.1 + qr.2)
  · intro qr h
    simp only [pairs, mem_filter, Finset.product_eq_sprod, mem_product, mem_Icc] at h
    simp only [mem_Icc, le_min_iff]
    omega
  · intro qr hqr uv huv heq
    simp only [pairs, mem_filter, Finset.product_eq_sprod, mem_product, mem_Icc] at hqr huv
    apply Prod.ext <;> dsimp at * <;> omega
  · intro t ht
    simp only [mem_Icc, le_min_iff] at ht
    refine ⟨(6 * t - s, s - 5 * t), ?_, ?_⟩
    · simp only [pairs, mem_filter, Finset.product_eq_sprod, mem_product, mem_Icc, Prod.fst, Prod.snd]
      omega
    · dsimp
      omega

/-- Exact cardinality, including empty slices and all endpoint cases. -/
theorem pairs_card (n s : ℤ) :
    (pairs n s).card = (min n (s / 5) + 1 - (s + 5) / 6).toNat := by
  rw [pairs_card_interval, Int.card_Icc]

/-- Recover p, q, r from an admissible integer t. -/
theorem recover_triple (n s t : ℤ)
    (ht : (s + 5) / 6 ≤ t ∧ t ≤ min n (s / 5)) :
    0 ≤ n - t ∧ 0 ≤ 6 * t - s ∧ 0 ≤ s - 5 * t ∧
    (n - t) + (6 * t - s) + (s - 5 * t) = n ∧
    (n - t) + 11 * (6 * t - s) + 13 * (s - 5 * t) = n + 2 * s := by
  have ht' : t ≤ n ∧ t ≤ s / 5 := le_min_iff.mp ht.2
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  constructor <;> ring

/-- The original positive triples at a prescribed square root. -/
def positiveTriples (n m : ℤ) : Finset (ℤ × ℤ × ℤ) :=
  ((Icc 1 n).product ((Icc 1 n).product (Icc 1 n))).filter
    (fun v => v.1 + v.2.1 + v.2.2 = n ∧
      v.1 + 11 * v.2.1 + 13 * v.2.2 = m ^ 2)

/-- Shift every coordinate down by one, a genuine cardinality-preserving bijection. -/
theorem positive_slice_card (n m s : ℤ) (hrel : m ^ 2 = n + 22 + 2 * s) :
    (positiveTriples n m).card = (pairs (n - 3) s).card := by
  apply Finset.card_bij (fun v _ => (v.2.1 - 1, v.2.2 - 1))
  · intro v hv
    simp only [positiveTriples, mem_filter, Finset.product_eq_sprod, mem_product, mem_Icc] at hv
    simp only [pairs, mem_filter, Finset.product_eq_sprod, mem_product, mem_Icc, Prod.fst, Prod.snd]
    omega
  · intro v hv w hw heq
    simp only [positiveTriples, mem_filter, Finset.product_eq_sprod, mem_product, mem_Icc] at hv hw
    have hq := congrArg Prod.fst heq
    have hr := congrArg Prod.snd heq
    dsimp at hq hr
    apply Prod.ext
    · omega
    · apply Prod.ext <;> omega
  · intro qr hqr
    simp only [pairs, mem_filter, Finset.product_eq_sprod, mem_product, mem_Icc] at hqr
    refine ⟨(n - qr.1 - qr.2 - 2, qr.1 + 1, qr.2 + 1), ?_, ?_⟩
    · simp only [positiveTriples, mem_filter, Finset.product_eq_sprod, mem_product, mem_Icc, Prod.fst, Prod.snd]
      omega
    · ext <;> dsimp <;> omega

/-- Exact formula for a positive slice; no asymptotic assumptions are used. -/
theorem positive_slice_formula (n m : ℤ) (hpar : m % 2 = n % 2) :
    (positiveTriples n m).card =
      (min (n - 3) (((m ^ 2 - n - 22) / 2) / 5) + 1 -
        (((m ^ 2 - n - 22) / 2) + 5) / 6).toNat := by
  have hm : m ^ 2 % 2 = m % 2 := by
    have hm' : m % 2 = 0 ∨ m % 2 = 1 := by omega
    rcases hm' with hm' | hm' <;> simp [pow_two, Int.mul_emod, hm']
  have hrel : m ^ 2 = n + 22 + 2 * ((m ^ 2 - n - 22) / 2) := by omega
  rw [positive_slice_card n m ((m ^ 2 - n - 22) / 2) hrel, pairs_card]

/-- The exact lower and upper square-root endpoints for positive triples. -/
theorem positive_root_range (n m : ℤ) (v : ℤ × ℤ × ℤ)
    (hv : v ∈ positiveTriples n m) :
    n + 22 ≤ m ^ 2 ∧ m ^ 2 ≤ 13 * n - 14 ∧ m % 2 = n % 2 := by
  simp only [positiveTriples, mem_filter, Finset.product_eq_sprod, mem_product, mem_Icc] at hv
  have hpar := root_parity n m v.1 v.2.1 v.2.2 hv.2.1 hv.2.2
  omega

/-- Nonnegative square roots are unique, so adding a square-root witness adds no multiplicity. -/
theorem root_unique (m k : ℤ) (hm : 0 ≤ m) (hk : 0 ≤ k) (h : m ^ 2 = k ^ 2) :
    m = k := by
  nlinarith

/-- Direct enumeration of the original problem, with its unique nonnegative root. -/
def a (n : ℕ) : ℕ :=
  ∑ m ∈ Icc (0 : ℤ) (13 * n), (positiveTriples n m).card

def roots (n : ℕ) : Finset ℤ :=
  (Icc (0 : ℤ) (13 * n)).filter
    (fun m => (n : ℤ) + 22 ≤ m ^ 2 ∧ m ^ 2 ≤ 13 * n - 14 ∧ m % 2 = (n : ℤ) % 2)

/-- Nonnegative roots cannot lie beyond the finite range used in a(n). -/
theorem positive_root_bound (n : ℕ) (m : ℤ) (hm : 0 ≤ m)
    (v : ℤ × ℤ × ℤ) (hv : v ∈ positiveTriples n m) : m ≤ 13 * n := by
  have hr := positive_root_range n m v hv
  have hn : (0 : ℤ) ≤ n := Int.natCast_nonneg n
  nlinarith

theorem a_eq_sum_slices (n : ℕ) :
    a n = ∑ m ∈ roots n, (positiveTriples n m).card := by
  unfold a
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro m hm hnot
  have hz : positiveTriples n m = ∅ := by
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro v hv
    apply hnot
    exact mem_filter.mpr ⟨hm, positive_root_range n m v hv⟩
  rw [hz, card_empty]

/-- The entire exact finite-sum formula, derived from the original positive triples. -/
theorem a_eq_exact_sum (n : ℕ) :
    a n = ∑ m ∈ roots n,
      (min ((n : ℤ) - 3) (((m ^ 2 - n - 22) / 2) / 5) + 1 -
        (((m ^ 2 - n - 22) / 2) + 5) / 6).toNat := by
  calc
    a n = ∑ m ∈ roots n, (positiveTriples n m).card := a_eq_sum_slices n
    _ = _ := by
      apply Finset.sum_congr rfl
      intro m hm
      exact positive_slice_formula n m (mem_filter.mp hm).2.2.2

/-- The exact real cardinality on the entire feasible range. -/
theorem pairs_card_real (n s : ℤ) (_hn : 0 ≤ n) (hs : 0 ≤ s) (hsn : s ≤ 6 * n) :
    ((pairs n s).card : ℝ) =
      (min n (s / 5) : ℤ) + 1 - ((s + 5) / 6 : ℤ) := by
  rw [pairs_card_interval]
  have h : (s + 5) / 6 ≤ min n (s / 5) + 1 := by omega
  exact_mod_cast Int.card_Icc_of_le ((s + 5) / 6) (min n (s / 5)) h

/-- Each lower slice differs from its continuous approximation by at most one. -/
theorem lower_rounding_error (n s : ℤ) (hn : 0 ≤ n) (hs : 0 ≤ s)
    (hsn : s ≤ 5 * n) :
    |((pairs n s).card : ℝ) - (s : ℝ) / 30| ≤ 1 := by
  have hsn' : s ≤ 6 * n := by omega
  have hmin : min n (s / 5) = s / 5 := min_eq_right (by omega)
  rw [pairs_card_real n s hn hs hsn', hmin]
  have hf₁ : (5 : ℝ) * (s / 5 : ℤ) ≤ (s : ℝ) := by exact_mod_cast (show 5 * (s / 5) ≤ s by omega)
  have hf₂ : (s : ℝ) < 5 * (s / 5 : ℤ) + 5 := by exact_mod_cast (show s < 5 * (s / 5) + 5 by omega)
  have hc₁ : (s : ℝ) ≤ 6 * ((s + 5) / 6 : ℤ) := by exact_mod_cast (show s ≤ 6 * ((s + 5) / 6) by omega)
  have hc₂ : (6 : ℝ) * ((s + 5) / 6 : ℤ) < (s : ℝ) + 6 := by exact_mod_cast (show 6 * ((s + 5) / 6) < s + 6 by omega)
  rw [abs_le]
  constructor <;> linarith

/-- Each upper slice differs from its continuous approximation by at most one. -/
theorem upper_rounding_error (n s : ℤ) (hn : 0 ≤ n)
    (hns : 5 * n ≤ s) (hsn : s ≤ 6 * n) :
    |((pairs n s).card : ℝ) - ((n : ℝ) - (s : ℝ) / 6)| ≤ 1 := by
  have hs : 0 ≤ s := by omega
  have hmin : min n (s / 5) = n := min_eq_left (by omega)
  rw [pairs_card_real n s hn hs hsn, hmin]
  have hc₁ : (s : ℝ) ≤ 6 * ((s + 5) / 6 : ℤ) := by exact_mod_cast (show s ≤ 6 * ((s + 5) / 6) by omega)
  have hc₂ : (6 : ℝ) * ((s + 5) / 6 : ℤ) < (s : ℝ) + 6 := by exact_mod_cast (show 6 * ((s + 5) / 6) < s + 6 by omega)
  rw [abs_le]
  constructor <;> linarith

/-- The continuous approximation appropriate for positive triples. -/
noncomputable def positiveWeight (n : ℕ) (m : ℤ) : ℝ :=
  if m ^ 2 ≤ 11 * (n : ℤ) - 8 then
    ((m : ℝ) ^ 2 - n - 22) / 60
  else
    (13 * (n : ℝ) - 14 - (m : ℝ) ^ 2) / 12

theorem positive_slice_rounding_error (n : ℕ) (m : ℤ) (hm : m ∈ roots n) :
    |((positiveTriples n m).card : ℝ) - positiveWeight n m| ≤ 1 := by
  obtain ⟨_, hlow, hhigh, hpar⟩ := mem_filter.mp hm
  let s : ℤ := (m ^ 2 - n - 22) / 2
  have hm2 : m ^ 2 % 2 = m % 2 := by
    have hm' : m % 2 = 0 ∨ m % 2 = 1 := by omega
    rcases hm' with hm' | hm' <;> simp [pow_two, Int.mul_emod, hm']
  have hrel : m ^ 2 = n + 22 + 2 * s := by dsimp [s]; omega
  have hn : 0 ≤ (n : ℤ) - 3 := by omega
  have hs : 0 ≤ s := by omega
  have hsn : s ≤ 6 * ((n : ℤ) - 3) := by omega
  have hrelR : (m : ℝ) ^ 2 = (n : ℝ) + 22 + 2 * (s : ℝ) := by
    exact_mod_cast hrel
  rw [positive_slice_card n m s hrel]
  by_cases hb : m ^ 2 ≤ 11 * (n : ℤ) - 8
  · have hs5 : s ≤ 5 * ((n : ℤ) - 3) := by omega
    have hv := lower_rounding_error ((n : ℤ) - 3) s hn hs hs5
    have heq : (s : ℝ) / 30 = ((m : ℝ) ^ 2 - n - 22) / 60 := by linarith
    simpa only [positiveWeight, if_pos hb, heq] using hv
  · have hs5 : 5 * ((n : ℤ) - 3) ≤ s := by omega
    have hv := upper_rounding_error ((n : ℤ) - 3) s hn hs5 hsn
    have heq : (((n : ℤ) - 3 : ℤ) : ℝ) - (s : ℝ) / 6 =
        (13 * (n : ℝ) - 14 - (m : ℝ) ^ 2) / 12 := by
      push_cast
      linarith
    simpa only [positiveWeight, if_neg hb, heq] using hv

/-- All rounding errors have been summed; no quadrature estimate is assumed. -/
theorem total_rounding_error (n : ℕ) :
    |(a n : ℝ) - ∑ m ∈ roots n, positiveWeight n m| ≤ (roots n).card := by
  have ha : (a n : ℝ) = ∑ m ∈ roots n, ((positiveTriples n m).card : ℝ) := by
    exact_mod_cast a_eq_sum_slices n
  rw [ha, ← Finset.sum_sub_distrib]
  calc
    |∑ m ∈ roots n, (((positiveTriples n m).card : ℝ) - positiveWeight n m)|
        ≤ ∑ m ∈ roots n, |((positiveTriples n m).card : ℝ) - positiveWeight n m| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _m ∈ roots n, (1 : ℝ) :=
      Finset.sum_le_sum (fun m hm => positive_slice_rounding_error n m hm)
    _ = (roots n).card := by simp

/-- A square-root bound on the number of slices (parity need not be used). -/
theorem roots_card_le (n : ℕ) :
    ((roots n).card : ℝ) ≤ Real.sqrt (13 * (n : ℝ)) + 1 := by
  let R : ℝ := Real.sqrt (13 * (n : ℝ))
  have hR : 0 ≤ R := Real.sqrt_nonneg _
  have hfloor : (0 : ℤ) ≤ ⌊R⌋ := Int.floor_nonneg.mpr hR
  have hsub : roots n ⊆ Icc (0 : ℤ) ⌊R⌋ := by
    intro m hm
    obtain ⟨hmrange, _hlow, hhigh, _hpar⟩ := mem_filter.mp hm
    have hm0 : (0 : ℤ) ≤ m := (mem_Icc.mp hmrange).1
    have hsqi : m ^ 2 ≤ 13 * (n : ℤ) := by omega
    have hsqr : (m : ℝ) ^ 2 ≤ 13 * (n : ℝ) := by exact_mod_cast hsqi
    exact mem_Icc.mpr ⟨hm0, Int.le_floor.mpr (Real.le_sqrt_of_sq_le hsqr)⟩
  have hc : ((Icc (0 : ℤ) ⌊R⌋).card : ℝ) = (⌊R⌋ : ℝ) + 1 := by
    have hh := Int.card_Icc_of_le (0 : ℤ) ⌊R⌋ (by omega)
    simp only [sub_zero] at hh
    exact_mod_cast hh
  have hcard : ((roots n).card : ℝ) ≤ ((Icc (0 : ℤ) ⌊R⌋).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  calc
    ((roots n).card : ℝ) ≤ ((Icc (0 : ℤ) ⌊R⌋).card : ℝ) := hcard
    _ = (⌊R⌋ : ℝ) + 1 := hc
    _ ≤ R + 1 := add_le_add_right (Int.floor_le R) 1

/-- An explicit global square-root bound for the complete rounding contribution. -/
theorem total_rounding_error_sqrt (n : ℕ) :
    |(a n : ℝ) - ∑ m ∈ roots n, positiveWeight n m| ≤
      Real.sqrt (13 * (n : ℝ)) + 1 :=
  (total_rounding_error n).trans (roots_card_le n)

/-- A small original-problem instance checked by kernel reduction. -/
theorem a_three : a 3 = 1 := by
  rw [a_eq_exact_sum]
  decide

theorem a_twelve : a 12 = 2 := by
  rw [a_eq_exact_sum]
  decide

noncomputable def K : ℝ :=
  (1 - 66 * Real.sqrt 11 + 65 * Real.sqrt 13) / 180

/-- The target proposition; proved below by `full_asymptotic`. -/
def FullAsymptoticStatement : Prop :=
  Asymptotics.IsBigO Filter.atTop
    (fun n : ℕ => (a n : ℝ) - K * (n : ℝ) * Real.sqrt (n : ℝ))
    (fun n : ℕ => Real.sqrt (n : ℝ))

theorem K_pos : 0 < K := by
  have h11 : Real.sqrt 11 ^ 2 = 11 := Real.sq_sqrt (by norm_num)
  have h13 : Real.sqrt 13 ^ 2 = 13 := Real.sq_sqrt (by norm_num)
  have h11p := Real.sqrt_nonneg (11 : ℝ)
  have h13p := Real.sqrt_nonneg (13 : ℝ)
  have h11b : Real.sqrt 11 < 10 / 3 := by nlinarith
  have h13b : (18 : ℝ) / 5 < Real.sqrt 13 := by nlinarith
  dsimp [K]
  linarith

/-- The leading constant is the value of the two elementary integrals. -/
theorem leading_integral :
    (∫ u in (1 : ℝ)..(Real.sqrt 11), (u ^ 2 - 1) / 120) +
    (∫ u in (Real.sqrt 11)..(Real.sqrt 13), (13 - u ^ 2) / 24) = K := by
  have h11 : Real.sqrt 11 ^ 2 = 11 := Real.sq_sqrt (by norm_num)
  have h13 : Real.sqrt 13 ^ 2 = 13 := Real.sq_sqrt (by norm_num)
  have h11c : Real.sqrt 11 ^ 3 = 11 * Real.sqrt 11 := by
    calc
      _ = Real.sqrt 11 ^ 2 * Real.sqrt 11 := by ring
      _ = _ := by rw [h11]
  have h13c : Real.sqrt 13 ^ 3 = 13 * Real.sqrt 13 := by
    calc
      _ = Real.sqrt 13 ^ 2 * Real.sqrt 13 := by ring
      _ = _ := by rw [h13]
  simp only [intervalIntegral.integral_div]
  rw [intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop) (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop) (by apply Continuous.intervalIntegrable; fun_prop)]
  simp only [integral_pow, intervalIntegral.integral_const]
  norm_num only [Nat.reduceAdd, one_pow, h11c, h13c]
  dsimp [K]
  ring

/-- Exact midpoint error for a quadratic on a length-two interval. -/
theorem quadratic_midpoint_error (a b c m : ℝ) :
    (∫ x in (m - 1)..(m + 1), a * x ^ 2 + b * x + c) / 2 -
      (a * m ^ 2 + b * m + c) = a / 3 := by
  rw [intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop) (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop) (by apply Continuous.intervalIntegrable; fun_prop)]
  rw [intervalIntegral.integral_const_mul b (fun x : ℝ => x)]
  simp only [intervalIntegral.integral_const_mul, integral_pow,
    integral_id, intervalIntegral.integral_const, smul_eq_mul]
  norm_num only [Nat.reduceAdd]
  ring

end A386235

namespace A386235
open Finset

/-- Exact polynomial sum on an arithmetic progression with spacing two. -/
theorem progression_sum (L : ℕ) (R e : ℝ) :
    (∑ k ∈ range L, (R ^ 2 - (2 * (k : ℝ) + e) ^ 2)) =
      L * R ^ 2 - (2 / 3 * (L : ℝ) * (L - 1) * (2 * L - 1) +
        2 * e * L * (L - 1) + L * e ^ 2) := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [sum_range_succ, ih]
    push_cast
    ring

/-- The endpoint discrepancy is at most linear in the radius. -/
theorem progression_error (L : ℕ) (R e : ℝ) (hR : 0 ≤ R) (he : e = 0 ∨ e = 1)
    (hd0 : 0 ≤ 2 * (L : ℝ) + e - R)
    (hd2 : 2 * (L : ℝ) + e - R ≤ 2) :
    |(∑ k ∈ range L, (R ^ 2 - (2 * (k : ℝ) + e) ^ 2)) -
      (R ^ 3 / 3 + (1 - e) * R ^ 2 / 2)| ≤ R + 1 := by
  let d := 2 * (L : ℝ) + e - R
  have hpoly :
      (∑ k ∈ range L, (R ^ 2 - (2 * (k : ℝ) + e) ^ 2)) -
        (R ^ 3 / 3 + (1 - e) * R ^ 2 / 2) =
      R * (-d ^ 2 / 2 + d - 1 / 3) - d * (d - 1) * (d - 2) / 6 +
        e * (e - 1) * (e - 2) / 6 := by
    rw [progression_sum]
    dsimp [d]
    ring
  have hde0 : 0 ≤ d := hd0
  have hde2 : d ≤ 2 := hd2
  have hez : e * (e - 1) * (e - 2) = 0 := by
    rcases he with rfl | rfl <;> norm_num
  have hc : |-d ^ 2 / 2 + d - 1 / 3| ≤ 1 := by
    rw [abs_le]
    constructor <;> nlinarith [mul_nonneg hde0 (sub_nonneg.mpr hde2), sq_nonneg (d - 1)]
  have hd : |d| ≤ 2 := by rw [abs_le]; constructor <;> linarith
  have hd1 : |d - 1| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have hd2' : |d - 2| ≤ 2 := by rw [abs_le]; constructor <;> linarith
  have hp : |d * (d - 1) * (d - 2)| ≤ 4 := by
    rw [abs_mul, abs_mul]
    calc
      |d| * |d - 1| * |d - 2| ≤ 2 * 1 * 2 := by gcongr
      _ = 4 := by norm_num
  rw [hpoly, hez, zero_div, add_zero]
  calc
    _ ≤ |R * (-d ^ 2 / 2 + d - 1 / 3)| + |d * (d - 1) * (d - 2) / 6| := abs_sub _ _
    _ = R * |-d ^ 2 / 2 + d - 1 / 3| + |d * (d - 1) * (d - 2)| / 6 := by
      rw [abs_mul, abs_of_nonneg hR, abs_div]
      norm_num
    _ ≤ R * 1 + 4 / 6 := by gcongr
    _ ≤ R + 1 := by linarith

noncomputable def capSum (N : ℕ) (x e : ℝ) : ℝ :=
  ∑ k ∈ range N, max (x - (2 * (k : ℝ) + e) ^ 2) 0

/-- A uniform estimate for the sum of a truncated quadratic along one parity class. -/
theorem capSum_error (N : ℕ) (x e : ℝ) (hx : 1 ≤ x)
    (he : e = 0 ∨ e = 1) (hN : Real.sqrt x < 2 * (N : ℝ) + e) :
    |capSum N x e - (x * Real.sqrt x / 3 + (1 - e) * x / 2)| ≤
      Real.sqrt x + 1 := by
  let R := Real.sqrt x
  let y := (R - e) / 2
  let L : ℕ := ⌊y⌋₊ + 1
  have hR : 0 ≤ R := Real.sqrt_nonneg _
  have hRsq : R ^ 2 = x := Real.sq_sqrt (by linarith)
  have he0 : 0 ≤ e := by rcases he with rfl | rfl <;> norm_num
  have he1 : e ≤ 1 := by rcases he with rfl | rfl <;> norm_num
  have hR1 : 1 ≤ R := by nlinarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hf := Nat.floor_le hy
  have hg := Nat.lt_floor_add_one y
  have hL0 : 0 ≤ 2 * (L : ℝ) + e - R := by
    dsimp [L, y] at *
    push_cast
    linarith
  have hL2 : 2 * (L : ℝ) + e - R ≤ 2 := by
    dsimp [L, y] at *
    push_cast
    linarith
  have hLN : L ≤ N := by
    have hyN : y < (N : ℝ) := by dsimp [y, R]; linarith
    have hh := (Nat.floor_lt hy).mpr hyN
    dsimp [L]
    omega
  have hsum : capSum N x e = ∑ k ∈ range L, (R ^ 2 - (2 * (k : ℝ) + e) ^ 2) := by
    unfold capSum
    have hrestrict :
        (∑ k ∈ range L, max (x - (2 * (k : ℝ) + e) ^ 2) 0) =
        ∑ k ∈ range N, max (x - (2 * (k : ℝ) + e) ^ 2) 0 := by
      apply Finset.sum_subset (Finset.range_mono hLN)
      intro k _hk hknot
      have hk : L ≤ k := by simpa only [mem_range, not_lt] using hknot
      have hkr : (L : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      have hrk : R ≤ 2 * (k : ℝ) + e := by linarith
      exact max_eq_right (by nlinarith)
    rw [← hrestrict]
    apply Finset.sum_congr rfl
    intro k hk
    have hkle : k ≤ ⌊y⌋₊ := by simpa only [mem_range, L, Nat.lt_succ_iff] using hk
    have hky : (k : ℝ) ≤ y := (Nat.le_floor_iff hy).mp hkle
    have hkr : 2 * (k : ℝ) + e ≤ R := by dsimp [y] at hky; linarith
    have hk0 : 0 ≤ 2 * (k : ℝ) + e := by positivity
    rw [max_eq_left (by nlinarith), hRsq]
  rw [hsum]
  have hh := progression_error L R e hR he hL0 hL2
  have hid : R ^ 3 / 3 + (1 - e) * R ^ 2 / 2 =
      x * Real.sqrt x / 3 + (1 - e) * x / 2 := by
    change R ^ 3 / 3 + (1 - e) * R ^ 2 / 2 = x * R / 3 + (1 - e) * x / 2
    rw [show R ^ 3 = R ^ 2 * R by ring, hRsq]
  simpa only [hid] using hh

noncomputable def tent (n : ℕ) (m : ℤ) : ℝ :=
  (max ((n : ℝ) + 22 - (m : ℝ) ^ 2) 0 -
    6 * max (11 * (n : ℝ) - 8 - (m : ℝ) ^ 2) 0 +
    5 * max (13 * (n : ℝ) - 14 - (m : ℝ) ^ 2) 0) / 60

theorem tent_eq_weight (n : ℕ) (m : ℤ) (hm : m ∈ roots n) :
    tent n m = positiveWeight n m := by
  obtain ⟨_, hlo, hhi, _hp⟩ := mem_filter.mp hm
  have hn : (3 : ℤ) ≤ n := by omega
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hloR : (n : ℝ) + 22 ≤ (m : ℝ) ^ 2 := by exact_mod_cast hlo
  have hhiR : (m : ℝ) ^ 2 ≤ 13 * (n : ℝ) - 14 := by exact_mod_cast hhi
  unfold tent positiveWeight
  rw [max_eq_right (by linarith : (n : ℝ) + 22 - (m : ℝ) ^ 2 ≤ 0),
    max_eq_left (by linarith : 0 ≤ 13 * (n : ℝ) - 14 - (m : ℝ) ^ 2)]
  split_ifs with hb
  · have hbR : (m : ℝ) ^ 2 ≤ 11 * (n : ℝ) - 8 := by exact_mod_cast hb
    rw [max_eq_left (by linarith : 0 ≤ 11 * (n : ℝ) - 8 - (m : ℝ) ^ 2)]
    ring
  · have hbR : 11 * (n : ℝ) - 8 ≤ (m : ℝ) ^ 2 := by exact_mod_cast (le_of_not_ge hb)
    rw [max_eq_right (by linarith : 11 * (n : ℝ) - 8 - (m : ℝ) ^ 2 ≤ 0)]
    ring

theorem tent_zero_outside (n : ℕ) (m : ℤ) (hn : 3 ≤ n)
    (hm0 : 0 ≤ m) (hp : m % 2 = (n : ℤ) % 2) (hm : m ∉ roots n) :
    tent n m = 0 := by
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  by_cases hlo : (n : ℤ) + 22 ≤ m ^ 2
  · by_cases hhi : m ^ 2 ≤ 13 * (n : ℤ) - 14
    · have hmb : m ≤ 13 * (n : ℤ) := by nlinarith
      exact False.elim (hm (mem_filter.mpr ⟨mem_Icc.mpr ⟨hm0, hmb⟩, hlo, hhi, hp⟩))
    · have hhiR : 13 * (n : ℝ) - 14 ≤ (m : ℝ) ^ 2 := by exact_mod_cast (le_of_not_ge hhi)
      unfold tent
      rw [max_eq_right (by linarith : (n : ℝ) + 22 - (m : ℝ) ^ 2 ≤ 0),
        max_eq_right (by linarith : 11 * (n : ℝ) - 8 - (m : ℝ) ^ 2 ≤ 0),
        max_eq_right (by linarith : 13 * (n : ℝ) - 14 - (m : ℝ) ^ 2 ≤ 0)]
      norm_num
  · have hloR : (m : ℝ) ^ 2 ≤ (n : ℝ) + 22 := by exact_mod_cast (le_of_not_ge hlo)
    unfold tent
    rw [max_eq_left (by linarith : 0 ≤ (n : ℝ) + 22 - (m : ℝ) ^ 2),
      max_eq_left (by linarith : 0 ≤ 11 * (n : ℝ) - 8 - (m : ℝ) ^ 2),
      max_eq_left (by linarith : 0 ≤ 13 * (n : ℝ) - 14 - (m : ℝ) ^ 2)]
    ring

/-- Extend the supported sum to a full parity progression; all added terms are zero. -/
theorem weight_sum_eq_caps (n : ℕ) (hn : 3 ≤ n) :
    (∑ m ∈ roots n, positiveWeight n m) =
      (capSum (13 * n + 1) ((n : ℝ) + 22) ((n % 2 : ℕ) : ℝ) -
        6 * capSum (13 * n + 1) (11 * (n : ℝ) - 8) ((n % 2 : ℕ) : ℝ) +
        5 * capSum (13 * n + 1) (13 * (n : ℝ) - 14) ((n % 2 : ℕ) : ℝ)) / 60 := by
  let f : ℕ → ℤ := fun k => 2 * (k : ℤ) + (n % 2 : ℕ)
  let G := (range (13 * n + 1)).image f
  have hsub : roots n ⊆ G := by
    intro m hm
    obtain ⟨hmb, _hl, _hh, hp⟩ := mem_filter.mp hm
    obtain ⟨hm0, hmN⟩ := mem_Icc.mp hmb
    have hmod : ((n % 2 : ℕ) : ℤ) = (n : ℤ) % 2 := by omega
    have hq : 0 ≤ m / 2 := by omega
    have hcast : ((m / 2).toNat : ℤ) = m / 2 := Int.toNat_of_nonneg hq
    apply mem_image.mpr
    refine ⟨(m / 2).toNat, ?_, ?_⟩
    · simp only [mem_range]
      omega
    · dsimp [f]
      omega
  have hs : (∑ m ∈ roots n, positiveWeight n m) = ∑ m ∈ G, tent n m := by
    calc
      _ = ∑ m ∈ roots n, tent n m :=
        Finset.sum_congr rfl (fun m hm => (tent_eq_weight n m hm).symm)
      _ = _ := by
        apply Finset.sum_subset hsub
        intro m hm hnot
        obtain ⟨k, _hk, rfl⟩ := mem_image.mp hm
        apply tent_zero_outside n (f k) hn
        · dsimp [f]; omega
        · dsimp [f]; omega
        · exact hnot
  rw [hs]
  have hinj : Set.InjOn f ↑(range (13 * n + 1)) := by
    intro i _hi j _hj hij
    dsimp [f] at hij
    omega
  rw [Finset.sum_image hinj]
  simp only [tent, f, Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast]
  simp only [capSum, Finset.sum_div, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Finset.mul_sum]
  rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_sub_distrib]

theorem capSum_error_bounded (n : ℕ) (x e : ℝ) (hx : 1 ≤ x)
    (hxN : x ≤ 13 * (n : ℝ)) (he : e = 0 ∨ e = 1) :
    |capSum (13 * n + 1) x e - (x * Real.sqrt x / 3 + (1 - e) * x / 2)| ≤
      Real.sqrt (13 * (n : ℝ)) + 1 := by
  have he0 : 0 ≤ e := by rcases he with rfl | rfl <;> norm_num
  have hr : Real.sqrt x ≤ 13 * (n : ℝ) + 1 := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · nlinarith [show (0 : ℝ) ≤ (n : ℝ) by positivity]
  have hN : Real.sqrt x < 2 * ((13 * n + 1 : ℕ) : ℝ) + e := by
    push_cast
    linarith [show (0 : ℝ) ≤ (n : ℝ) by positivity]
  exact (capSum_error (13 * n + 1) x e hx he hN).trans
    (add_le_add_right (Real.sqrt_le_sqrt hxN) 1)

noncomputable def J (n : ℕ) : ℝ :=
  (((n : ℝ) + 22) * Real.sqrt ((n : ℝ) + 22) -
    6 * (11 * (n : ℝ) - 8) * Real.sqrt (11 * (n : ℝ) - 8) +
    5 * (13 * (n : ℝ) - 14) * Real.sqrt (13 * (n : ℝ) - 14)) / 180

/-- Cancellation of the parity boundary terms leaves only square-root error. -/
theorem weight_sum_error (n : ℕ) (hn : 3 ≤ n) :
    |(∑ m ∈ roots n, positiveWeight n m) - J n| ≤
      Real.sqrt (13 * (n : ℝ)) + 1 := by
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have he : ((n % 2 : ℕ) : ℝ) = 0 ∨ ((n % 2 : ℕ) : ℝ) = 1 := by
    have h : n % 2 = 0 ∨ n % 2 = 1 := by omega
    exact_mod_cast h
  have hA := capSum_error_bounded n ((n : ℝ) + 22) ((n % 2 : ℕ) : ℝ)
    (by linarith) (by linarith) he
  have hB := capSum_error_bounded n (11 * (n : ℝ) - 8) ((n % 2 : ℕ) : ℝ)
    (by linarith) (by linarith) he
  have hC := capSum_error_bounded n (13 * (n : ℝ) - 14) ((n % 2 : ℕ) : ℝ)
    (by linarith) (by linarith) he
  rw [weight_sum_eq_caps n hn]
  unfold J
  rw [abs_le] at hA hB hC ⊢
  constructor <;> nlinarith [Real.sqrt_nonneg (13 * (n : ℝ))]

theorem a_sub_J_error (n : ℕ) (hn : 3 ≤ n) :
    |(a n : ℝ) - J n| ≤ 2 * Real.sqrt (13 * (n : ℝ)) + 2 := by
  have h1 := total_rounding_error_sqrt n
  have h2 := weight_sum_error n hn
  calc
    |(a n : ℝ) - J n| ≤
        |(a n : ℝ) - ∑ m ∈ roots n, positiveWeight n m| +
        |(∑ m ∈ roots n, positiveWeight n m) - J n| := abs_sub_le _ _ _
    _ ≤ 2 * Real.sqrt (13 * (n : ℝ)) + 2 := by linarith

/-- A polynomial Lipschitz bound, avoiding differentiation at the origin. -/
theorem cubic_error (u v R : ℝ) (hu0 : 0 ≤ u) (hv0 : 0 ≤ v)
    (huR : u ≤ R) (hvR : v ≤ R) :
    |u ^ 3 - v ^ 3| ≤ 2 * R * |u ^ 2 - v ^ 2| := by
  have hR : 0 ≤ R := hu0.trans huR
  have hpoly : 0 ≤ 2 * R * (u + v) - (u ^ 2 + u * v + v ^ 2) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr huR) hu0,
      mul_nonneg (sub_nonneg.mpr hvR) hv0,
      mul_nonneg (sub_nonneg.mpr huR) hv0, mul_nonneg hR hu0]
  rcases le_total u v with huv | hvu
  · have hsq : u ^ 2 ≤ v ^ 2 := by nlinarith
    have hcub : u ^ 3 ≤ v ^ 3 := pow_le_pow_left₀ hu0 huv 3
    rw [abs_of_nonpos (sub_nonpos.mpr hcub), abs_of_nonpos (sub_nonpos.mpr hsq)]
    nlinarith [mul_nonneg (sub_nonneg.mpr huv) hpoly]
  · have hsq : v ^ 2 ≤ u ^ 2 := by nlinarith
    have hcub : v ^ 3 ≤ u ^ 3 := pow_le_pow_left₀ hv0 hvu 3
    rw [abs_of_nonneg (sub_nonneg.mpr hcub), abs_of_nonneg (sub_nonneg.mpr hsq)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hvu) hpoly]

theorem sqrt_bound (n : ℕ) (x : ℝ) (hx : x ≤ 13 * (n : ℝ)) :
    Real.sqrt x ≤ 4 * Real.sqrt (n : ℝ) := by
  apply (Real.sqrt_le_iff).mpr
  constructor
  · positivity
  · have hs := Real.sq_sqrt (show (0 : ℝ) ≤ (n : ℝ) by positivity)
    nlinarith [show (0 : ℝ) ≤ (n : ℝ) by positivity]

theorem power_shift_error (n : ℕ) (x y D : ℝ)
    (hx0 : 0 ≤ x) (hy0 : 0 ≤ y) (hxN : x ≤ 13 * (n : ℝ))
    (hyN : y ≤ 13 * (n : ℝ)) (hd : |x - y| ≤ D) :
    |x * Real.sqrt x - y * Real.sqrt y| ≤ 8 * D * Real.sqrt (n : ℝ) := by
  have hh := cubic_error (Real.sqrt x) (Real.sqrt y) (4 * Real.sqrt (n : ℝ))
    (Real.sqrt_nonneg x) (Real.sqrt_nonneg y) (sqrt_bound n x hxN) (sqrt_bound n y hyN)
  have hxs : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx0
  have hys : Real.sqrt y ^ 2 = y := Real.sq_sqrt hy0
  have hxc : Real.sqrt x ^ 3 = x * Real.sqrt x := by
    rw [show Real.sqrt x ^ 3 = Real.sqrt x ^ 2 * Real.sqrt x by ring, hxs]
  have hyc : Real.sqrt y ^ 3 = y * Real.sqrt y := by
    rw [show Real.sqrt y ^ 3 = Real.sqrt y ^ 2 * Real.sqrt y by ring, hys]
  rw [hxc, hyc, hxs, hys] at hh
  nlinarith [mul_nonneg (Real.sqrt_nonneg (n : ℝ)) (sub_nonneg.mpr hd)]

theorem J_sub_main_error (n : ℕ) (hn : 3 ≤ n) :
    |J n - K * (n : ℝ) * Real.sqrt (n : ℝ)| ≤ 7 * Real.sqrt (n : ℝ) := by
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hA := power_shift_error n ((n : ℝ) + 22) (n : ℝ) 22
    (by linarith) (by positivity) (by linarith) (by linarith)
    (by rw [show (n : ℝ) + 22 - n = 22 by ring]; norm_num)
  have hB := power_shift_error n (11 * (n : ℝ) - 8) (11 * (n : ℝ)) 8
    (by linarith) (by positivity) (by linarith) (by linarith)
    (by rw [show 11 * (n : ℝ) - 8 - 11 * n = -8 by ring]; norm_num)
  have hC := power_shift_error n (13 * (n : ℝ) - 14) (13 * (n : ℝ)) 14
    (by linarith) (by positivity) (by linarith) (by linarith)
    (by rw [show 13 * (n : ℝ) - 14 - 13 * n = -14 by ring]; norm_num)
  have hmain :
      ((n : ℝ) * Real.sqrt (n : ℝ) -
        6 * (11 * (n : ℝ)) * Real.sqrt (11 * (n : ℝ)) +
        5 * (13 * (n : ℝ)) * Real.sqrt (13 * (n : ℝ))) / 180 =
      K * (n : ℝ) * Real.sqrt (n : ℝ) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 11),
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 13)]
    unfold K
    ring
  rw [← hmain]
  unfold J
  rw [abs_le] at hA hB hC ⊢
  constructor <;> nlinarith [Real.sqrt_nonneg (n : ℝ)]

/-- The complete explicit error bound for the original sequence. -/
theorem explicit_error_bound (n : ℕ) (hn : 3 ≤ n) :
    |(a n : ℝ) - K * (n : ℝ) * Real.sqrt (n : ℝ)| ≤
      20 * Real.sqrt (n : ℝ) := by
  have h1 := a_sub_J_error n hn
  have h2 := J_sub_main_error n hn
  have hroot := sqrt_bound n (13 * (n : ℝ)) le_rfl
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ (n : ℝ) by positivity)
  have hsp := Real.sqrt_nonneg (n : ℝ)
  have hs1 : 1 ≤ Real.sqrt (n : ℝ) := by nlinarith
  calc
    _ ≤ |(a n : ℝ) - J n| + |J n - K * (n : ℝ) * Real.sqrt (n : ℝ)| :=
      abs_sub_le _ _ _
    _ ≤ 20 * Real.sqrt (n : ℝ) := by linarith

/-- The full O(sqrt n) asymptotic theorem, proved without additional hypotheses. -/
theorem full_asymptotic : FullAsymptoticStatement := by
  unfold FullAsymptoticStatement
  apply Asymptotics.IsBigO.of_bound 20
  filter_upwards [Filter.eventually_ge_atTop (3 : ℕ)] with n hn
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] using
    explicit_error_bound n hn

/-- The problem stated directly: positive triples whose weighted sum is a square. -/
noncomputable def originalSolutions (n : ℕ) : Finset (ℤ × ℤ × ℤ) := by
  classical
  exact ((Icc 1 (n : ℤ)).product ((Icc 1 (n : ℤ)).product (Icc 1 (n : ℤ)))).filter
    (fun v => v.1 + v.2.1 + v.2.2 = n ∧
      ∃ m : ℤ, v.1 + 11 * v.2.1 + 13 * v.2.2 = m ^ 2)

theorem originalSolutions_eq_biUnion (n : ℕ) :
    originalSolutions n = (Icc (0 : ℤ) (13 * n)).biUnion (positiveTriples n) := by
  classical
  ext v
  constructor
  · intro hv
    obtain ⟨hbox, hsum, m, hsq⟩ := mem_filter.mp hv
    have hvp : v ∈ positiveTriples n |m| := by
      apply mem_filter.mpr
      exact ⟨hbox, hsum, by simpa only [sq_abs] using hsq⟩
    apply mem_biUnion.mpr
    exact ⟨|m|, mem_Icc.mpr ⟨abs_nonneg m, positive_root_bound n |m| (abs_nonneg m) v hvp⟩, hvp⟩
  · intro hv
    obtain ⟨m, _hm, hvm⟩ := mem_biUnion.mp hv
    obtain ⟨hbox, hsum, hsq⟩ := mem_filter.mp hvm
    exact mem_filter.mpr ⟨hbox, hsum, m, hsq⟩

/-- Root uniqueness proves that the sum defining a counts each triple exactly once. -/
theorem original_count_eq_a (n : ℕ) : (originalSolutions n).card = a n := by
  have hd : (Icc (0 : ℤ) (13 * n)).toSet.PairwiseDisjoint (positiveTriples n) := by
    intro m hm k hk hmk
    apply Finset.disjoint_left.mpr
    intro v hvm hvk
    have hsm := (mem_filter.mp hvm).2.2
    have hsk := (mem_filter.mp hvk).2.2
    exact hmk (root_unique m k (mem_Icc.mp hm).1 (mem_Icc.mp hk).1 (hsm.symm.trans hsk))
  rw [originalSolutions_eq_biUnion, Finset.card_biUnion hd]
  rfl

/-- Final theorem directly on the original set of triples, with an explicit constant. -/
theorem original_explicit_error_bound (n : ℕ) (hn : 3 ≤ n) :
    |((originalSolutions n).card : ℝ) - K * (n : ℝ) * Real.sqrt (n : ℝ)| ≤
      20 * Real.sqrt (n : ℝ) := by
  rw [original_count_eq_a]
  exact explicit_error_bound n hn

/-- Final asymptotic theorem directly on the original problem's counting function. -/
theorem original_asymptotic :
    Asymptotics.IsBigO Filter.atTop
      (fun n : ℕ => ((originalSolutions n).card : ℝ) - K * (n : ℝ) * Real.sqrt (n : ℝ))
      (fun n : ℕ => Real.sqrt (n : ℝ)) := by
  simpa only [original_count_eq_a] using full_asymptotic

end A386235

/-! Dependency audit for every theorem in this development. -/
#print axioms A386235.eliminate_p
#print axioms A386235.root_parity
#print axioms A386235.pairs_card_interval
#print axioms A386235.pairs_card
#print axioms A386235.recover_triple
#print axioms A386235.positive_slice_card
#print axioms A386235.positive_slice_formula
#print axioms A386235.positive_root_range
#print axioms A386235.root_unique
#print axioms A386235.positive_root_bound
#print axioms A386235.a_eq_sum_slices
#print axioms A386235.a_eq_exact_sum
#print axioms A386235.pairs_card_real
#print axioms A386235.lower_rounding_error
#print axioms A386235.upper_rounding_error
#print axioms A386235.positive_slice_rounding_error
#print axioms A386235.total_rounding_error
#print axioms A386235.roots_card_le
#print axioms A386235.total_rounding_error_sqrt
#print axioms A386235.a_three
#print axioms A386235.a_twelve
#print axioms A386235.K_pos
#print axioms A386235.leading_integral
#print axioms A386235.quadratic_midpoint_error
#print axioms A386235.progression_sum
#print axioms A386235.progression_error
#print axioms A386235.capSum_error
#print axioms A386235.tent_eq_weight
#print axioms A386235.tent_zero_outside
#print axioms A386235.weight_sum_eq_caps
#print axioms A386235.capSum_error_bounded
#print axioms A386235.weight_sum_error
#print axioms A386235.a_sub_J_error
#print axioms A386235.cubic_error
#print axioms A386235.sqrt_bound
#print axioms A386235.power_shift_error
#print axioms A386235.J_sub_main_error
#print axioms A386235.explicit_error_bound
#print axioms A386235.full_asymptotic
#print axioms A386235.originalSolutions_eq_biUnion
#print axioms A386235.original_count_eq_a
#print axioms A386235.original_explicit_error_bound
#print axioms A386235.original_asymptotic
