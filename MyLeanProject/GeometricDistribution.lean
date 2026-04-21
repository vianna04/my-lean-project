/-
Copyright (c) 2024 Josha Dekker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josha Dekker
-/
module

public import Mathlib.Probability.ProbabilityMassFunction.Basic
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Integrals
public import Mathlib.Analysis.SpecificLimits.Normed

/-! # Geometric distributions over ℕ

Define the geometric measure over the natural numbers

## Main definitions
* `geometricPMFReal`: the function `p n ↦ (1-p) ^ n * p`
  for `n ∈ ℕ`, which is the probability density function of a geometric distribution with
  success probability `p ∈ (0,1]`.
* `geometricPMF`: `ℝ≥0∞`-valued pmf,
  `geometricPMF p = ENNReal.ofReal (geometricPMFReal p)`.
* `geometricMeasure`: a geometric measure on `ℕ`, parametrized by its success probability `p`.
-/

@[expose] public section

open scoped ENNReal NNReal

open MeasureTheory Real Set Filter Topology

namespace ProbabilityTheory

variable {p : ℝ}

section GeometricPMF

/-- The pmf of the geometric distribution depending on its success probability. -/
noncomputable
def geometricPMFReal (p : ℝ) (n : ℕ) : ℝ := (1 - p) ^ n * p

lemma geometricPMFRealSum (hp_pos : 0 < p) (hp_le_one : p ≤ 1) :
    HasSum (fun n ↦ geometricPMFReal p n) 1 := by
  unfold geometricPMFReal
  have := hasSum_geometric_of_lt_one (sub_nonneg.mpr hp_le_one) (sub_lt_self 1 hp_pos)
  apply (hasSum_mul_right_iff (hp_pos.ne')).mpr at this
  simp only [sub_sub_cancel] at this
  rw [inv_mul_eq_div, div_self hp_pos.ne'] at this
  exact this

/-- The geometric pmf is positive for all natural numbers -/
lemma geometricPMFReal_pos {n : ℕ} (hp_pos : 0 < p) (hp_lt_one : p < 1) :
    0 < geometricPMFReal p n := by
  rw [geometricPMFReal]
  positivity [sub_pos.mpr hp_lt_one]

lemma geometricPMFReal_nonneg {n : ℕ} (hp_pos : 0 < p) (hp_le_one : p ≤ 1) :
    0 ≤ geometricPMFReal p n := by
  rw [geometricPMFReal]
  positivity [sub_nonneg.mpr hp_le_one]

/-- Geometric distribution with success probability `p`. -/
noncomputable
def geometricPMF (hp_pos : 0 < p) (hp_le_one : p ≤ 1) : PMF ℕ :=
  ⟨fun n ↦ ENNReal.ofReal (geometricPMFReal p n), by
    apply ENNReal.hasSum_coe.mpr
    rw [← toNNReal_one]
    exact (geometricPMFRealSum hp_pos hp_le_one).toNNReal
      (fun n ↦ geometricPMFReal_nonneg hp_pos hp_le_one)⟩

/-- The geometric pmf is measurable. -/
@[fun_prop]
lemma measurable_geometricPMFReal : Measurable (geometricPMFReal p) := by
  fun_prop

@[fun_prop]
lemma stronglyMeasurable_geometricPMFReal : StronglyMeasurable (geometricPMFReal p) :=
  stronglyMeasurable_iff_measurable.mpr measurable_geometricPMFReal

end GeometricPMF

/-- Measure defined by the geometric distribution -/
noncomputable
def geometricMeasure (hp_pos : 0 < p) (hp_le_one : p ≤ 1) : Measure ℕ :=
  (geometricPMF hp_pos hp_le_one).toMeasure

lemma isProbabilityMeasure_geometricMeasure (hp_pos : 0 < p) (hp_le_one : p ≤ 1) :
    IsProbabilityMeasure (geometricMeasure hp_pos hp_le_one) :=
  PMF.toMeasure.isProbabilityMeasure (geometricPMF hp_pos hp_le_one)

@[deprecated (since := "2025-08-28")] alias isProbabilityMeasureGeometric :=
  isProbabilityMeasure_geometricMeasure

section MeanVariance

lemma hasSum_geometric_mul_nat (hp_pos : 0 < p) (hp_lt_one : p < 1) :
    HasSum (fun n : ℕ => geometricPMFReal p n * n) ((1 - p) / p) := by
  have := (hasSum_coe_mul_geometric_of_norm_lt_one (by
    rw [Real.norm_of_nonneg (sub_nonneg.mpr hp_lt_one.le)]; linarith : ‖1 - p‖ < 1)).mul_right p
  simp only [sub_sub_cancel, geometricPMFReal] at this ⊢
  convert this using 1 <;> first | (ext; ring) | field_simp

theorem geometricMeasure_mean (hp_pos : 0 < p) (hp_lt_one : p < 1) :
    ∫ n : ℕ, (n : ℝ) ∂geometricMeasure hp_pos (le_of_lt hp_lt_one) = (1 - p) / p := by
  have hp_le_one := le_of_lt hp_lt_one
  have key := hasSum_geometric_mul_nat hp_pos hp_lt_one
  have hnn : ∀ a, 0 ≤ geometricPMFReal p a * (a : ℝ) :=
    fun a => mul_nonneg (geometricPMFReal_nonneg hp_pos hp_le_one) (Nat.cast_nonneg a)
  have hint : Integrable (Nat.cast : ℕ → ℝ) (geometricPMF hp_pos hp_le_one).toMeasure := by
    refine ⟨by fun_prop, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, lintegral_countable']
    simp_rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), enorm_natCast]
    calc ∑' a, ↑a * (geometricPMF hp_pos hp_le_one) a
        ≤ ∑' a, ENNReal.ofReal (geometricPMFReal p a * a) := ENNReal.tsum_le_tsum fun a => by
          rw [show (geometricPMF hp_pos hp_le_one) a =
                ENNReal.ofReal (geometricPMFReal p a) from rfl,
              show (a : ℝ≥0∞) = ENNReal.ofReal (a : ℝ) from (ENNReal.ofReal_natCast a).symm,
              ← ENNReal.ofReal_mul (Nat.cast_nonneg a), mul_comm]
      _ = ENNReal.ofReal (∑' a, geometricPMFReal p a * a) :=
          (ENNReal.ofReal_tsum_of_nonneg hnn key.summable).symm
      _ < ∞ := by rw [key.tsum_eq]; exact ENNReal.ofReal_lt_top
  rw [geometricMeasure, PMF.integral_eq_tsum _ _ hint]
  simp_rw [fun a => show ((geometricPMF hp_pos hp_le_one) a).toReal = geometricPMFReal p a from
    ENNReal.toReal_ofReal (geometricPMFReal_nonneg hp_pos hp_le_one), smul_eq_mul, key.tsum_eq]

lemma hasSum_geometric_factorial_moment2 (hp_pos : 0 < p) (hp_lt_one : p < 1) :
    HasSum (fun n : ℕ => geometricPMFReal p n * (n * (n - 1 : ℝ))) (2 * (1 - p) ^ 2 / p ^ 2) := by
  set q := 1 - p with hq
  have hq_norm : ‖q‖ < 1 := by
    rw [Real.norm_of_nonneg (sub_nonneg.mpr hp_lt_one.le)]; exact sub_lt_self 1 hp_pos
  set f := fun n : ℕ => geometricPMFReal p n * (n * (n - 1 : ℝ))
  suffices HasSum (fun n : ℕ => f (n + 2)) (2 * (1 - p) ^ 2 / p ^ 2) by
    rwa [hasSum_nat_add_iff, Finset.sum_range_succ, Finset.sum_range_succ,
         Finset.sum_range_zero, show f 0 = 0 from by simp [f, geometricPMFReal],
         show f 1 = 0 from by simp [f, geometricPMFReal],
         add_zero, zero_add, add_zero] at this
  have hchoose := hasSum_choose_mul_geometric_of_norm_lt_one 2 hq_norm
  simp only [hq, sub_sub_cancel, pow_succ, pow_zero, one_mul, one_div] at hchoose
  have hconv : HasSum (fun n : ℕ => ((n + 2) * (n + 1) : ℝ) * q ^ n) (2 / p ^ 3) := by
    have h2 := hchoose.mul_left 2
    rw [show 2 * (p * p * p)⁻¹ = 2 / p ^ 3 from by field_simp] at h2
    convert h2 using 1; ext n
    have h1 : (n + 2).choose 2 = (n + 2) * (n + 1) / 2 := by
      rw [Nat.choose_two_right]; congr 1
    have hdvd : 2 ∣ (n + 2) * (n + 1) := by rw [mul_comm]; exact Nat.two_dvd_mul_add_one (n + 1)
    rw [h1, Nat.cast_div hdvd (by norm_num), hq]; push_cast; ring
  convert (hconv.mul_left (q ^ 2 * p)) using 1
  · ext n; simp only [f, geometricPMFReal, hq]; push_cast; ring
  · simp only [hq]; field_simp

/-- The variance of the geometric distribution with p ∈ (0,1) is (1-p)/p^2 -/
theorem geometricMeasure_variance (hp_pos : 0 < p) (hp_lt_one : p < 1) :
    ∫ n : ℕ, ((n : ℝ) - (1 - p) / p) ^ 2 ∂geometricMeasure hp_pos (le_of_lt hp_lt_one) =
    (1 - p) / p ^ 2 := by
  have hp_le_one := le_of_lt hp_lt_one
  have hpdf : ∀ a : ℕ, ((geometricPMF hp_pos hp_le_one) a).toReal = geometricPMFReal p a :=
    fun a => ENNReal.toReal_ofReal (geometricPMFReal_nonneg hp_pos hp_le_one)
  set μ := (1 - p) / p with hμ
  have hnn : ∀ a : ℕ, 0 ≤ geometricPMFReal p a * ((a : ℝ) - μ) ^ 2 :=
    fun a => mul_nonneg (geometricPMFReal_nonneg hp_pos hp_le_one) (sq_nonneg _)
  have key : HasSum (fun a : ℕ => geometricPMFReal p a * ((a : ℝ) - μ) ^ 2)
      ((1 - p) / p ^ 2) := by
    have h1 := geometricPMFRealSum hp_pos hp_le_one
    have h2 := hasSum_geometric_mul_nat hp_pos hp_lt_one
    have hA' : HasSum (fun a : ℕ => geometricPMFReal p a * (a : ℝ) ^ 2)
        (2 * (1 - p) ^ 2 / p ^ 2 + (1 - p) / p) :=
      ((hasSum_geometric_factorial_moment2 hp_pos hp_lt_one).add h2).congr_fun (fun a => by ring)
    have hB : HasSum (fun a : ℕ => geometricPMFReal p a * (2 * (a : ℝ) * μ))
        (2 * μ * μ) := by
      convert h2.mul_right (2 * μ) using 1 <;> [ext a; skip] <;> ring
    have hC : HasSum (fun a : ℕ => geometricPMFReal p a * μ ^ 2) (μ ^ 2) := by
      convert h1.mul_right (μ ^ 2) using 1; ring
    have hcomb := (hA'.sub hB).add hC
    rw [show 2 * (1 - p) ^ 2 / p ^ 2 + (1 - p) / p - 2 * μ * μ + μ ^ 2 =
        (1 - p) / p ^ 2 from by simp only [hμ]; field_simp; ring] at hcomb
    exact hcomb.congr_fun (fun a => by ring)
  have hint : Integrable (fun n : ℕ => ((n : ℝ) - μ) ^ 2)
      (geometricPMF hp_pos hp_le_one).toMeasure := by
    refine ⟨by fun_prop, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, lintegral_countable']
    simp_rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), enorm_eq_nnnorm]
    calc ∑' a, ↑‖((a : ℝ) - μ) ^ 2‖₊ * (geometricPMF hp_pos hp_le_one) a
        = ∑' a, ENNReal.ofReal (geometricPMFReal p a * ((a : ℝ) - μ) ^ 2) :=
          tsum_congr fun a => by
            rw [show (geometricPMF hp_pos hp_le_one) a =
                  ENNReal.ofReal (geometricPMFReal p a) from rfl,
                Real.nnnorm_of_nonneg (sq_nonneg _),
                ENNReal.ofReal_eq_coe_nnreal (geometricPMFReal_nonneg hp_pos hp_le_one),
                ENNReal.ofReal_eq_coe_nnreal (hnn a), ← ENNReal.coe_mul]
            congr 1; ext; simp [mul_comm]
      _ = ENNReal.ofReal (∑' a, geometricPMFReal p a * ((a : ℝ) - μ) ^ 2) :=
          (ENNReal.ofReal_tsum_of_nonneg hnn key.summable).symm
      _ < ∞ := by rw [key.tsum_eq]; exact ENNReal.ofReal_lt_top
  rw [geometricMeasure, PMF.integral_eq_tsum _ _ hint]
  simp_rw [hpdf, smul_eq_mul, key.tsum_eq]

end MeanVariance

end ProbabilityTheory
