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
      _ < ∞ := by
          rw [(ENNReal.ofReal_tsum_of_nonneg (fun a => mul_nonneg
              (geometricPMFReal_nonneg hp_pos hp_le_one) (Nat.cast_nonneg a)) key.summable).symm,
              key.tsum_eq]
          exact ENNReal.ofReal_lt_top
  rw [geometricMeasure, PMF.integral_eq_tsum _ _ hint]
  simp_rw [show ∀ a, ((geometricPMF hp_pos hp_le_one) a).toReal = geometricPMFReal p a from
    fun a => ENNReal.toReal_ofReal (geometricPMFReal_nonneg hp_pos hp_le_one), smul_eq_mul]
  exact key.tsum_eq

lemma hasSum_geometric_factorial_moment2 (hp_pos : 0 < p) (hp_lt_one : p < 1) :
    HasSum (fun n : ℕ => geometricPMFReal p n * (n * (n - 1 : ℝ))) (2 * (1 - p) ^ 2 / p ^ 2) := by
  set q := 1 - p with hq
  have hq_pos : 0 < q := sub_pos.mpr hp_lt_one
  have hq_lt_one : q < 1 := sub_lt_self 1 hp_pos
  have hq_norm : ‖q‖ < 1 := by rwa [Real.norm_of_nonneg (le_of_lt hq_pos)]
  set f := fun n : ℕ => geometricPMFReal p n * (n * (n - 1 : ℝ))
  have hf0 : f 0 = 0 := by simp [f, geometricPMFReal]
  have hf1 : f 1 = 0 := by simp [f, geometricPMFReal]
  have hshift : HasSum (fun n : ℕ => f (n + 2)) (2 * (1 - p) ^ 2 / p ^ 2) := by
    have hchoose := hasSum_choose_mul_geometric_of_norm_lt_one 2 hq_norm
    simp only [hq, sub_sub_cancel, pow_succ, pow_zero, one_mul, one_div] at hchoose
    have hconv : HasSum (fun n : ℕ => ((n + 2) * (n + 1) : ℝ) * q ^ n) (2 / p ^ 3) := by
      have h2 := hchoose.mul_left 2
      have hval : 2 * (p * p * p)⁻¹ = 2 / p ^ 3 := by field_simp
      rw [hval] at h2
      convert h2 using 1
      ext n
      have hchoose_eq : ((n + 2).choose 2 : ℝ) = (n + 2) * (n + 1) / 2 := by
        have h1 : (n + 2).choose 2 = (n + 2) * (n + 1) / 2 := by
          rw [Nat.choose_two_right]
          congr 1
        rw [h1]
        have hdvd : 2 ∣ (n + 2) * (n + 1) := by
          have : (n + 2) * (n + 1) = (n + 1) * (n + 2) := mul_comm _ _
          rw [this]
          exact Nat.two_dvd_mul_add_one (n + 1)
        rw [Nat.cast_div hdvd (by norm_num)]
        push_cast
        rfl
      rw [hchoose_eq, hq]
      ring
    have hmul := hconv.mul_left (q ^ 2 * p)
    have hval2 : q ^ 2 * p * (2 / p ^ 3) = 2 * (1 - p) ^ 2 / p ^ 2 := by
      simp only [hq]
      field_simp
    rw [hval2] at hmul
    convert hmul using 1
    ext n
    simp only [f, geometricPMFReal, hq]
    push_cast
    ring
  rwa [hasSum_nat_add_iff, Finset.sum_range_succ, Finset.sum_range_succ,
       Finset.sum_range_zero, hf0, hf1, add_zero, zero_add, add_zero] at hshift

/-- The variance of the geometric distribution with p ∈ (0,1) is (1-p)/p^2 -/
theorem geometricMeasure_variance (hp_pos : 0 < p) (hp_lt_one : p < 1) :
    ∫ n : ℕ, ((n : ℝ) - (1 - p) / p) ^ 2 ∂geometricMeasure hp_pos (le_of_lt hp_lt_one) =
    (1 - p) / p ^ 2 := by
  have hp_le_one := le_of_lt hp_lt_one
  have hpdf : ∀ a : ℕ, ((geometricPMF hp_pos hp_le_one) a).toReal = geometricPMFReal p a :=
    fun a => ENNReal.toReal_ofReal (geometricPMFReal_nonneg hp_pos hp_le_one)
  set μ := (1 - p) / p with hμ
  have key : HasSum (fun a : ℕ => geometricPMFReal p a * ((a : ℝ) - μ) ^ 2)
      ((1 - p) / p ^ 2) := by
    have h1 := geometricPMFRealSum hp_pos hp_le_one
    have h2 : HasSum (fun a : ℕ => geometricPMFReal p a * (a : ℝ)) μ :=
      hasSum_geometric_mul_nat hp_pos hp_lt_one
    have hA := hasSum_geometric_factorial_moment2 hp_pos hp_lt_one
    have hA' : HasSum (fun a : ℕ => geometricPMFReal p a * (a : ℝ) ^ 2)
        (2 * (1 - p) ^ 2 / p ^ 2 + (1 - p) / p) :=
      (hA.add h2).congr_fun (fun a => by ring)
    have hB : HasSum (fun a : ℕ => geometricPMFReal p a * (2 * (a : ℝ) * μ))
        (2 * μ * μ) := by
      have h := h2.mul_right (2 * μ)
      simp_rw [mul_comm _ (2 * μ), ← mul_assoc] at h
      convert h using 1
      funext a; ring
    have hC : HasSum (fun a : ℕ => geometricPMFReal p a * μ ^ 2) (μ ^ 2) := by
      have h := h1.mul_right (μ ^ 2)
      convert h using 1; ring
    have hcomb := (hA'.sub hB).add hC
    have hsimp : 2 * (1 - p) ^ 2 / p ^ 2 + (1 - p) / p - 2 * μ * μ + μ ^ 2 =
        (1 - p) / p ^ 2 := by
      simp only [hμ]; field_simp; ring
    rw [hsimp] at hcomb
    exact hcomb.congr_fun (fun a => by ring)
  have hint : Integrable (fun n : ℕ => ((n : ℝ) - μ) ^ 2)
      (geometricPMF hp_pos hp_le_one).toMeasure := by
    constructor
    · fun_prop
    · rw [hasFiniteIntegral_iff_enorm, lintegral_countable']
      simp_rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
        enorm_eq_nnnorm]
      have hnn : ∀ a : ℕ, 0 ≤ geometricPMFReal p a * ((a : ℝ) - μ) ^ 2 :=
        fun a => mul_nonneg (geometricPMFReal_nonneg hp_pos hp_le_one) (sq_nonneg _)
      have hbound : ∀ a : ℕ,
          (‖((a : ℝ) - μ) ^ 2‖₊ : ℝ≥0∞) * (geometricPMF hp_pos hp_le_one) a =
          ENNReal.ofReal (geometricPMFReal p a * ((a : ℝ) - μ) ^ 2) := fun a => by
        rw [show (geometricPMF hp_pos hp_le_one) a =
              ENNReal.ofReal (geometricPMFReal p a) from rfl,
            Real.nnnorm_of_nonneg (sq_nonneg _),
            ENNReal.ofReal_eq_coe_nnreal (geometricPMFReal_nonneg hp_pos hp_le_one),
            ENNReal.ofReal_eq_coe_nnreal (hnn a),
            ← ENNReal.coe_mul]
        congr 1
        ext
        simp [mul_comm]
      calc ∑' a, ↑‖((a : ℝ) - μ) ^ 2‖₊ * (geometricPMF hp_pos hp_le_one) a
          = ∑' a, ENNReal.ofReal (geometricPMFReal p a * ((a : ℝ) - μ) ^ 2) :=
            tsum_congr hbound
        _ = ENNReal.ofReal (∑' a, geometricPMFReal p a * ((a : ℝ) - μ) ^ 2) :=
            (ENNReal.ofReal_tsum_of_nonneg hnn key.summable).symm
        _ = ENNReal.ofReal ((1 - p) / p ^ 2) := by rw [key.tsum_eq]
        _ < ∞ := ENNReal.ofReal_lt_top
  rw [geometricMeasure, PMF.integral_eq_tsum _ _ hint]
  simp_rw [hpdf, smul_eq_mul]
  rw [tsum_congr]
  · exact key.tsum_eq
  · intro a; ring

end MeanVariance

end ProbabilityTheory
