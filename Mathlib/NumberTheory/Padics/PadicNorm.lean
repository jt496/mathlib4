/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# p-adic norm

This file defines the `p`-adic norm on `ℚ`.

The `p`-adic valuation on `ℚ` is the difference of the multiplicities of `p` in the numerator and
denominator of `q`. This function obeys the standard properties of a valuation, with the appropriate
assumptions on `p`.

The valuation induces a norm on `ℚ`. This norm is a nonarchimedean absolute value.
It takes values in {0} ∪ {1/p^k | k ∈ ℤ}.

## Implementation notes

Much, but not all, of this file assumes that `p` is prime. This assumption is inferred automatically
by taking `[Fact p.Prime]` as a type class argument.

## References

* [F. Q. Gouvêa, *p-adic numbers*][gouvea1997]
* [R. Y. Lewis, *A formal proof of Hensel's lemma over the p-adic integers*][lewis2019]
* <https://en.wikipedia.org/wiki/P-adic_number>

## Tags

p-adic, p adic, padic, norm, valuation
-/


/-- If `q ≠ 0`, the `p`-adic norm of a rational `q` is `p ^ (-padicValRat p q)`.
If `q = 0`, the `p`-adic norm of `q` is `0`. -/
def padicNorm (p : ℕ) (q : ℚ) : ℚ :=
  if q = 0 then 0 else (p : ℚ) ^ (-padicValRat p q)

namespace padicNorm

open padicValRat

variable {p : ℕ}

/-- Unfolds the definition of the `p`-adic norm of `q` when `q ≠ 0`. -/
@[simp]
protected theorem eq_zpow_of_nonzero {q : ℚ} (hq : q ≠ 0) :
    padicNorm p q = (p : ℚ) ^ (-padicValRat p q) := by simp [hq, padicNorm]

/-- The `p`-adic norm is nonnegative. -/
protected theorem nonneg (q : ℚ) : 0 ≤ padicNorm p q :=
  if hq : q = 0 then by simp [hq, padicNorm]
  else by
    unfold padicNorm
    split_ifs
    apply zpow_nonneg
    exact mod_cast Nat.zero_le _

/-- The `p`-adic norm of `0` is `0`. -/
@[simp]
protected theorem zero : padicNorm p 0 = 0 := by simp [padicNorm]

/-- The `p`-adic norm of `1` is `1`. -/
protected theorem one : padicNorm p 1 = 1 := by simp [padicNorm]

/-- The `p`-adic norm of `p` is `p⁻¹` if `p > 1`.

See also `padicNorm.padicNorm_p_of_prime` for a version assuming `p` is prime. -/
theorem padicNorm_p (hp : 1 < p) : padicNorm p p = (p : ℚ)⁻¹ := by
  simp [padicNorm, (pos_of_gt hp).ne', padicValNat.self hp]

/-- The `p`-adic norm of `p` is `p⁻¹` if `p` is prime.

See also `padicNorm.padicNorm_p` for a version assuming `1 < p`. -/
@[simp]
theorem padicNorm_p_of_prime [Fact p.Prime] : padicNorm p p = (p : ℚ)⁻¹ :=
  padicNorm_p <| Nat.Prime.one_lt Fact.out

/-- The `p`-adic norm of `q` is `1` if `q` is prime and not equal to `p`. -/
theorem padicNorm_of_prime_of_ne {q : ℕ} [p_prime : Fact p.Prime] [q_prime : Fact q.Prime]
    (neq : p ≠ q) : padicNorm p q = 1 := by
  have p : padicValRat p q = 0 := mod_cast padicValNat_primes neq
  rw [padicNorm, p]
  simp [q_prime.1.ne_zero]

/-- The `p`-adic norm of `p` is less than `1` if `1 < p`.

See also `padicNorm.padicNorm_p_lt_one_of_prime` for a version assuming `p` is prime. -/
theorem padicNorm_p_lt_one (hp : 1 < p) : padicNorm p p < 1 := by
  rw [padicNorm_p hp, inv_lt_one_iff₀]
  exact mod_cast Or.inr hp

/-- The `p`-adic norm of `p` is less than `1` if `p` is prime.

See also `padicNorm.padicNorm_p_lt_one` for a version assuming `1 < p`. -/
theorem padicNorm_p_lt_one_of_prime [Fact p.Prime] : padicNorm p p < 1 :=
  padicNorm_p_lt_one <| Nat.Prime.one_lt Fact.out

/-- `padicNorm p q` takes discrete values `p ^ -z` for `z : ℤ`. -/
protected theorem values_discrete {q : ℚ} (hq : q ≠ 0) : ∃ z : ℤ, padicNorm p q = (p : ℚ) ^ (-z) :=
  ⟨padicValRat p q, by simp [padicNorm, hq]⟩

/-- `padicNorm p` is symmetric. -/
@[simp]
protected theorem neg (q : ℚ) : padicNorm p (-q) = padicNorm p q :=
  if hq : q = 0 then by simp [hq] else by simp [padicNorm, hq]

variable [hp : Fact p.Prime]

/-- If `q ≠ 0`, then `padicNorm p q ≠ 0`. -/
protected theorem nonzero {q : ℚ} (hq : q ≠ 0) : padicNorm p q ≠ 0 := by
  rw [padicNorm.eq_zpow_of_nonzero hq]
  apply zpow_ne_zero
  exact mod_cast ne_of_gt hp.1.pos

/-- If the `p`-adic norm of `q` is 0, then `q` is `0`. -/
theorem zero_of_padicNorm_eq_zero {q : ℚ} (h : padicNorm p q = 0) : q = 0 := by
  apply by_contradiction; intro hq
  unfold padicNorm at h; rw [if_neg hq] at h
  apply absurd h
  apply zpow_ne_zero
  exact mod_cast hp.1.ne_zero

/-- The `p`-adic norm is multiplicative. -/
@[simp]
protected theorem mul (q r : ℚ) : padicNorm p (q * r) = padicNorm p q * padicNorm p r :=
  if hq : q = 0 then by simp [hq]
  else
    if hr : r = 0 then by simp [hr]
    else by
      have : (p : ℚ) ≠ 0 := by simp [hp.1.ne_zero]
      simp [padicNorm, *, padicValRat.mul, zpow_add₀ this, mul_comm]

/-- The `p`-adic norm respects division. -/
@[simp]
protected theorem div (q r : ℚ) : padicNorm p (q / r) = padicNorm p q / padicNorm p r :=
  if hr : r = 0 then by simp [hr]
  else eq_div_of_mul_eq (padicNorm.nonzero hr) (by rw [← padicNorm.mul, div_mul_cancel₀ _ hr])

/-- The `p`-adic norm of an integer is at most `1`. -/
protected theorem of_int (z : ℤ) : padicNorm p z ≤ 1 := by
  obtain rfl | hz := eq_or_ne z 0
  · simp
  · rw [padicNorm, if_neg (mod_cast hz)]
    exact zpow_le_one_of_nonpos₀ (mod_cast hp.1.one_le) (by simp)

private theorem nonarchimedean_aux {q r : ℚ} (h : padicValRat p q ≤ padicValRat p r) :
    padicNorm p (q + r) ≤ max (padicNorm p q) (padicNorm p r) :=
  have hnqp : padicNorm p q ≥ 0 := padicNorm.nonneg _
  have hnrp : padicNorm p r ≥ 0 := padicNorm.nonneg _
  if hq : q = 0 then by simp [hq, max_eq_right hnrp]
  else
    if hr : r = 0 then by simp [hr, max_eq_left hnqp]
    else
      if hqr : q + r = 0 then le_trans (by simpa [hqr] using hnqp) (le_max_left _ _)
      else by
        unfold padicNorm; split_ifs
        apply le_max_iff.2
        left
        apply zpow_le_zpow_right₀
        · exact mod_cast le_of_lt hp.1.one_lt
        · apply neg_le_neg
          have : padicValRat p q = min (padicValRat p q) (padicValRat p r) := (min_eq_left h).symm
          rw [this]
          exact min_le_padicValRat_add hqr

/-- The `p`-adic norm is nonarchimedean: the norm of `p + q` is at most the max of the norm of `p`
and the norm of `q`. -/
protected theorem nonarchimedean {q r : ℚ} :
    padicNorm p (q + r) ≤ max (padicNorm p q) (padicNorm p r) := by
  wlog hle : padicValRat p q ≤ padicValRat p r generalizing q r
  · rw [add_comm, max_comm]
    exact this (le_of_not_ge hle)
  exact nonarchimedean_aux hle

/-- The `p`-adic norm respects the triangle inequality: the norm of `p + q` is at most the norm of
`p` plus the norm of `q`. -/
theorem triangle_ineq (q r : ℚ) : padicNorm p (q + r) ≤ padicNorm p q + padicNorm p r :=
  calc
    padicNorm p (q + r) ≤ max (padicNorm p q) (padicNorm p r) := padicNorm.nonarchimedean
    _ ≤ padicNorm p q + padicNorm p r :=
      max_le_add_of_nonneg (padicNorm.nonneg _) (padicNorm.nonneg _)

/-- The `p`-adic norm of a difference is at most the max of each component. Restates the archimedean
property of the `p`-adic norm. -/
protected theorem sub {q r : ℚ} : padicNorm p (q - r) ≤ max (padicNorm p q) (padicNorm p r) := by
  rw [sub_eq_add_neg, ← padicNorm.neg r]
  exact padicNorm.nonarchimedean

/-- If the `p`-adic norms of `q` and `r` are different, then the norm of `q + r` is equal to the max
of the norms of `q` and `r`. -/
theorem add_eq_max_of_ne {q r : ℚ} (hne : padicNorm p q ≠ padicNorm p r) :
    padicNorm p (q + r) = max (padicNorm p q) (padicNorm p r) := by
  wlog hlt : padicNorm p r < padicNorm p q
  · rw [add_comm, max_comm]
    exact this hne.symm (hne.lt_or_gt.resolve_right hlt)
  have : padicNorm p q ≤ max (padicNorm p (q + r)) (padicNorm p r) :=
    calc
      padicNorm p q = padicNorm p (q + r + (-r)) := by ring_nf
      _ ≤ max (padicNorm p (q + r)) (padicNorm p (-r)) := padicNorm.nonarchimedean
      _ = max (padicNorm p (q + r)) (padicNorm p r) := by simp
  have hnge : padicNorm p r ≤ padicNorm p (q + r) := by
    apply le_of_not_gt
    intro hgt
    rw [max_eq_right_of_lt hgt] at this
    exact not_lt_of_ge this hlt
  have : padicNorm p q ≤ padicNorm p (q + r) := by rwa [max_eq_left hnge] at this
  apply _root_.le_antisymm
  · apply padicNorm.nonarchimedean
  · rwa [max_eq_left_of_lt hlt]

/-- The `p`-adic norm is an absolute value: positive-definite and multiplicative, satisfying the
triangle inequality. -/
instance : IsAbsoluteValue (padicNorm p) where
  abv_nonneg' := padicNorm.nonneg
  abv_eq_zero' := ⟨zero_of_padicNorm_eq_zero, fun hx ↦ by simp [hx]⟩
  abv_add' := padicNorm.triangle_ineq
  abv_mul' := padicNorm.mul

theorem dvd_iff_norm_le {n : ℕ} {z : ℤ} : ↑(p ^ n) ∣ z ↔ padicNorm p z ≤ (p : ℚ) ^ (-n : ℤ) := by
  unfold padicNorm; split_ifs with hz
  · norm_cast at hz
    simp [hz]
  · rw [zpow_le_zpow_iff_right₀, neg_le_neg_iff, padicValRat.of_int,
      padicValInt.of_ne_one_ne_zero hp.1.ne_one _]
    · norm_cast
      rw [← FiniteMultiplicity.pow_dvd_iff_le_multiplicity]
      · norm_cast
      · apply Int.finiteMultiplicity_iff.2 ⟨by simp [hp.out.ne_one], mod_cast hz⟩
    · exact_mod_cast hz
    · exact_mod_cast hp.out.one_lt

/-- The `p`-adic norm of an integer `m` is one iff `p` doesn't divide `m`. -/
theorem int_eq_one_iff (m : ℤ) : padicNorm p m = 1 ↔ ¬(p : ℤ) ∣ m := by
  nth_rw 2 [← pow_one p]
  simp only [dvd_iff_norm_le, Nat.cast_one, zpow_neg, zpow_one, not_le]
  constructor
  · intro h
    rw [h, inv_lt_one₀] <;> norm_cast
    · exact Nat.Prime.one_lt Fact.out
    · exact Nat.Prime.pos Fact.out
  · simp only [padicNorm]
    split_ifs
    · rw [inv_lt_zero, ← Nat.cast_zero, Nat.cast_lt]
      intro h
      exact (Nat.not_lt_zero p h).elim
    · have : 1 < (p : ℚ) := by norm_cast; exact Nat.Prime.one_lt (Fact.out : Nat.Prime p)
      rw [← zpow_neg_one, zpow_lt_zpow_iff_right₀ this]
      have : 0 ≤ padicValRat p m := by simp only [of_int, Nat.cast_nonneg]
      intro h
      rw [← zpow_zero (p : ℚ), zpow_right_inj₀] <;> linarith

theorem int_lt_one_iff (m : ℤ) : padicNorm p m < 1 ↔ (p : ℤ) ∣ m := by
  rw [← not_iff_not, ← int_eq_one_iff, eq_iff_le_not_lt]
  simp only [padicNorm.of_int, true_and]

theorem of_nat (m : ℕ) : padicNorm p m ≤ 1 :=
  padicNorm.of_int (m : ℤ)

/-- The `p`-adic norm of a natural `m` is one iff `p` doesn't divide `m`. -/
theorem nat_eq_one_iff (m : ℕ) : padicNorm p m = 1 ↔ ¬p ∣ m := by
  rw [← Int.natCast_dvd_natCast, ← int_eq_one_iff, Int.cast_natCast]

theorem nat_lt_one_iff (m : ℕ) : padicNorm p m < 1 ↔ p ∣ m := by
  rw [← Int.natCast_dvd_natCast, ← int_lt_one_iff, Int.cast_natCast]

/-- If a rational is not a p-adic integer, it is not an integer. -/
theorem not_int_of_not_padic_int (p : ℕ) {a : ℚ} [hp : Fact (Nat.Prime p)]
    (H : 1 < padicNorm p a) : ¬ a.isInt := by
  contrapose! H
  rw [Rat.eq_num_of_isInt H]
  apply padicNorm.of_int

theorem sum_lt {α : Type*} {F : α → ℚ} {t : ℚ} {s : Finset α} :
    s.Nonempty → (∀ i ∈ s, padicNorm p (F i) < t) → padicNorm p (∑ i ∈ s, F i) < t := by
  classical
    refine s.induction_on (by rintro ⟨-, ⟨⟩⟩) ?_
    rintro a S haS IH - ht
    by_cases hs : S.Nonempty
    · rw [Finset.sum_insert haS]
      exact
        lt_of_le_of_lt padicNorm.nonarchimedean
          (max_lt (ht a (Finset.mem_insert_self a S))
            (IH hs fun b hb ↦ ht b (Finset.mem_insert_of_mem hb)))
    · simp_all

theorem sum_le {α : Type*} {F : α → ℚ} {t : ℚ} {s : Finset α} :
    s.Nonempty → (∀ i ∈ s, padicNorm p (F i) ≤ t) → padicNorm p (∑ i ∈ s, F i) ≤ t := by
  classical
    refine s.induction_on (by rintro ⟨-, ⟨⟩⟩) ?_
    rintro a S haS IH - ht
    by_cases hs : S.Nonempty
    · rw [Finset.sum_insert haS]
      exact
        padicNorm.nonarchimedean.trans
          (max_le (ht a (Finset.mem_insert_self a S))
            (IH hs fun b hb ↦ ht b (Finset.mem_insert_of_mem hb)))
    · simp_all

theorem sum_lt' {α : Type*} {F : α → ℚ} {t : ℚ} {s : Finset α}
    (hF : ∀ i ∈ s, padicNorm p (F i) < t) (ht : 0 < t) : padicNorm p (∑ i ∈ s, F i) < t := by
  obtain rfl | hs := Finset.eq_empty_or_nonempty s
  · simp [ht]
  · exact sum_lt hs hF

theorem sum_le' {α : Type*} {F : α → ℚ} {t : ℚ} {s : Finset α}
    (hF : ∀ i ∈ s, padicNorm p (F i) ≤ t) (ht : 0 ≤ t) : padicNorm p (∑ i ∈ s, F i) ≤ t := by
  obtain rfl | hs := Finset.eq_empty_or_nonempty s
  · simp [ht]
  · exact sum_le hs hF

end padicNorm
