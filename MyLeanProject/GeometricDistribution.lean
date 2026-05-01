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

public import Mathlib.Probability.Moments.Variance

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

/-- The geometric measure with success probability `p` as a measure over `ℕ`. -/
noncomputable
def geometricMeasure (p : ℝ) (_hp_pos : 0 < p) (_hp_le_one : p ≤ 1) : Measure ℕ :=
  Measure.sum (fun n ↦ ENNReal.ofReal (geometricPMFReal p n) • (.dirac n))

lemma geometricMeasure_singleton (hp_pos : 0 < p) (hp_le_one : p ≤ 1) (n : ℕ) :
    (geometricMeasure p hp_pos hp_le_one) {n} =
    ENNReal.ofReal (geometricPMFReal p n) := by
  rw [geometricMeasure, Measure.sum_smul_dirac_singleton]

lemma geometricMeasure_real_singleton (hp_pos : 0 < p) (hp_le_one : p ≤ 1) (n : ℕ) :
    (geometricMeasure p hp_pos hp_le_one).real {n} = geometricPMFReal p n := by
  rw [measureReal_def, geometricMeasure_singleton, ENNReal.toReal_ofReal
    (geometricPMFReal_nonneg hp_pos hp_le_one)]

instance isProbabilityMeasure_geometricMeasure (hp_pos : 0 < p) (hp_le_one : p ≤ 1) :
    IsProbabilityMeasure (geometricMeasure p hp_pos hp_le_one) :=
  (geometricPMFRealSum hp_pos hp_le_one).isProbabilityMeasure_sum_dirac
    (fun _ ↦ geometricPMFReal_nonneg hp_pos hp_le_one)

section Integral

variable {E : Type*} [NormedAddCommGroup E]

lemma integrable_geometricMeasure_iff {hp_pos : 0 < p} {hp_le_one : p ≤ 1} {f : ℕ → E} :
    Integrable f (geometricMeasure p hp_pos hp_le_one) ↔
    Summable (fun n ↦ geometricPMFReal p n * ‖f n‖) := by
  rw [geometricMeasure, integrable_sum_dirac_iff (by simp)]
  congrm Summable (fun n ↦ ?_ * _)
  rw [ENNReal.toReal_ofReal (geometricPMFReal_nonneg hp_pos hp_le_one)]

variable [NormedSpace ℝ E]

lemma integral_geometricMeasure [FiniteDimensional ℝ E] (hp_pos : 0 < p) (hp_le_one : p ≤ 1)
    (f : ℕ → E) :
    ∫ n, f n ∂geometricMeasure p hp_pos hp_le_one =
    ∑' n, geometricPMFReal p n • f n := by
  rw [geometricMeasure, integral_sum_dirac (by simp)]
  congr with n
  rw [ENNReal.toReal_ofReal (geometricPMFReal_nonneg hp_pos hp_le_one)]

end Integral

section Moments

lemma hasSum_geometricMeasure_nat (hp_pos : 0 < p) (hp_lt_one : p < 1) :
    HasSum (fun n : ℕ => geometricPMFReal p n * n) ((1 - p) / p) := by
  simp only [geometricPMFReal]
  have h := (hasSum_coe_mul_geometric_of_norm_lt_one (by
    rw [Real.norm_of_nonneg (sub_nonneg.mpr hp_lt_one.le)]; linarith)).mul_right p;
    simp [sub_sub_cancel] at h
  convert h using 1; ext n ; ring; field_simp

lemma hasSum_geometricMeasure_descFactorial_two (hp_pos : 0 < p) (hp_lt_one : p < 1) :
    HasSum (fun n => geometricPMFReal p n * (n * (n - 1))) (2 * (1 - p) ^ 2 / p ^ 2) := by
  simp only [geometricPMFReal]
  set f := fun n : ℕ => (1 - p) ^ n * p * (n * (n - 1))
  have hshift : HasSum (fun n : ℕ => f (n + 2)) (2 * (1 - p) ^ 2 / p ^ 2) := by
    have hchoose := hasSum_choose_mul_geometric_of_norm_lt_one 2
      (by rw [Real.norm_of_nonneg (sub_nonneg.mpr hp_lt_one.le)]; linarith)
    simp only [sub_sub_cancel] at hchoose; norm_num at hchoose
    have hconv : HasSum (fun n : ℕ => ((n + 1) * (n + 2)) * (1 - p) ^ n) (2 / p ^ 3) := by
      convert (hchoose.mul_left 2) using 1; ext n
      rw [Nat.choose_two_right, Nat.cast_div (by rw [mul_comm]; exact Nat.two_dvd_mul_add_one (n + 1)) (by norm_num)]
      push_cast; ring
    convert (hconv.mul_left ((1 - p) ^ 2 * p)) using 1
    ext n; simp[f]; ring; field_simp
  simp only [hasSum_nat_add_iff, Finset.sum_range_succ, Finset.sum_range_zero, add_zero,
             show f 0 = 0 by simp [f], show f 1 = 0 by simp [f]] at hshift
  exact hshift

lemma hasSum_geometricMeasure_sq (hp_pos : 0 < p) (hp_lt_one : p < 1) :
    HasSum (fun n : ℕ => geometricPMFReal p n * n ^ 2)
    (2 * (1 - p) ^ 2 / p ^ 2 + (1 - p) / p) := by
  have h1 := hasSum_geometricMeasure_nat hp_pos hp_lt_one
  have h2 := hasSum_geometricMeasure_descFactorial_two hp_pos hp_lt_one
  convert h2.add h1 using 1
  ext n; ring

lemma lintegral_sq_nat_geometricMeasure (hp_pos : 0 < p) (hp_lt_one : p < 1) :
    ∫⁻ n, ‖(n : ℝ)‖ₑ ^ 2 ∂geometricMeasure p hp_pos hp_lt_one.le =
    ENNReal.ofReal (2 * (1 - p) ^ 2 / p ^ 2 + (1 - p) / p) := by
  have h : ∀ n : ℕ, ‖(n : ℝ)‖ₑ ^ 2 = ENNReal.ofReal ((n : ℝ) ^ 2) := fun n ↦ by
    rw [← enorm_pow, Real.enorm_of_nonneg (sq_nonneg _)]
  simp_rw [h]
  have hint : Integrable (fun n : ℕ ↦ (n : ℝ) ^ 2) (geometricMeasure p hp_pos hp_lt_one.le) := by
    rw [integrable_geometricMeasure_iff]
    have heq : (fun n : ℕ ↦ geometricPMFReal p n * ‖(n : ℝ) ^ 2‖) =
        (fun n : ℕ ↦ geometricPMFReal p n * (n : ℝ) ^ 2) := by
      ext n; congr 1; rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    rw [heq]
    exact (hasSum_geometricMeasure_sq hp_pos hp_lt_one).summable
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ (fun _ ↦ sq_nonneg _))]
  congr 1; rw [integral_geometricMeasure]
  exact (hasSum_geometricMeasure_sq hp_pos hp_lt_one).tsum_eq

lemma memLp_two_nat_geometricMeasure (hp_pos : 0 < p) (hp_lt_one : p < 1) :
    MemLp (fun n : ℕ ↦ (n : ℝ)) 2 (geometricMeasure p hp_pos hp_lt_one.le) := by
  refine ⟨by fun_prop, ?_⟩
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
  simp only [ENNReal.toReal_ofNat, one_div, ENNReal.rpow_two]
  rw [lintegral_sq_nat_geometricMeasure hp_pos hp_lt_one]
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top

end Moments

section MeanVariance

@[simp]
theorem geometricMeasure_mean (hp_pos : 0 < p) (hp_lt_one : p < 1) :
    ∫ n : ℕ, (n : ℝ) ∂geometricMeasure p hp_pos hp_lt_one.le = (1 - p) / p := by
  rw [integral_geometricMeasure]
  exact (hasSum_geometricMeasure_nat hp_pos hp_lt_one).tsum_eq

@[simp]
theorem geometricMeasure_moment_two (hp_pos : 0 < p) (hp_lt_one : p < 1) :
    ∫ n : ℕ, (n : ℝ) ^ 2 ∂geometricMeasure p hp_pos hp_lt_one.le = 2 * (1 - p) ^ 2 / p ^ 2 + (1 - p) / p := by
  rw [integral_geometricMeasure]
  exact (hasSum_geometricMeasure_sq hp_pos hp_lt_one).tsum_eq

@[simp]
theorem geometricMeasure_variance (hp_pos : 0 < p) (hp_lt_one : p < 1) :
    Var[fun n : ℕ ↦ (n : ℝ); geometricMeasure p hp_pos hp_lt_one.le] = (1 - p) / p ^ 2 := by
  rw [variance_eq_sub (memLp_two_nat_geometricMeasure hp_pos hp_lt_one)]
  simp only [Pi.pow_apply]
  rw [geometricMeasure_moment_two hp_pos hp_lt_one, geometricMeasure_mean hp_pos hp_lt_one]
  field_simp; ring

end MeanVariance

end ProbabilityTheory
