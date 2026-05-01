/-
Copyright (c) 2024 Josha Dekker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josha Dekker
-/
module

public import Mathlib.Probability.CDF
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Probability.Moments.MGFAnalytic

/-! # Gamma distributions over ℝ

Define the gamma measure over the reals.

## Main definitions
* `gammaPDFReal`: the function `a r x ↦ r ^ a / (Gamma a) * x ^ (a - 1) * exp (-(r * x))`
  for `0 ≤ x` or `0` else, which is the probability density function of a gamma distribution with
  shape `a` and rate `r` (when `ha : 0 < a ` and `hr : 0 < r`).
* `gammaPDF`: `ℝ≥0∞`-valued pdf,
  `gammaPDF a r = ENNReal.ofReal (gammaPDFReal a r)`.
* `gammaMeasure`: a gamma measure on `ℝ`, parametrized by its shape `a` and rate `r`.

## Main results
* `gammaMeasure_mgf`: the moment generating function of the gamma distribution
  with shape `a` and rate `r` at `t < r` is `(r / (r - t)) ^ a`.
* `gammaMeasure_integral_id`: the mean of the gamma distribution is `a / r`.
* `gammaMeasure_variance`: the variance of the gamma distribution is `a / r ^ 2`.

-/

@[expose] public section

open scoped ENNReal NNReal

open MeasureTheory Real Set Filter Topology

/-- A Lebesgue Integral from -∞ to y can be expressed as the sum of one from -∞ to 0 and 0 to x -/
lemma lintegral_Iic_eq_lintegral_Iio_add_Icc {y z : ℝ} (f : ℝ → ℝ≥0∞) (hzy : z ≤ y) :
    ∫⁻ x in Iic y, f x = (∫⁻ x in Iio z, f x) + ∫⁻ x in Icc z y, f x := by
  rw [← Iio_union_Icc_eq_Iic hzy, lintegral_union measurableSet_Icc]
  simp_rw [Set.disjoint_iff_forall_ne, mem_Iio, mem_Icc]
  intros
  linarith

namespace ProbabilityTheory

section GammaPDF

/-- The pdf of the gamma distribution depending on its scale and rate -/
noncomputable
def gammaPDFReal (a r x : ℝ) : ℝ :=
  if 0 ≤ x then r ^ a / (Gamma a) * x ^ (a - 1) * exp (-(r * x)) else 0

/-- The pdf of the gamma distribution, as a function valued in `ℝ≥0∞` -/
noncomputable
def gammaPDF (a r x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (gammaPDFReal a r x)

lemma gammaPDF_eq (a r x : ℝ) :
    gammaPDF a r x =
      ENNReal.ofReal (if 0 ≤ x then r ^ a / (Gamma a) * x ^ (a - 1) * exp (-(r * x)) else 0) :=
  rfl

lemma gammaPDF_of_neg {a r x : ℝ} (hx : x < 0) : gammaPDF a r x = 0 := by
  simp only [gammaPDF_eq, if_neg (not_le.mpr hx), ENNReal.ofReal_zero]

lemma gammaPDF_of_nonneg {a r x : ℝ} (hx : 0 ≤ x) :
    gammaPDF a r x = ENNReal.ofReal (r ^ a / (Gamma a) * x ^ (a - 1) * exp (-(r * x))) := by
  simp only [gammaPDF_eq, if_pos hx]

/-- The Lebesgue integral of the gamma pdf over nonpositive reals equals 0 -/
lemma lintegral_gammaPDF_of_nonpos {x a r : ℝ} (hx : x ≤ 0) :
    ∫⁻ y in Iio x, gammaPDF a r y = 0 := by
  rw [setLIntegral_congr_fun (g := fun _ ↦ 0) measurableSet_Iio]
  · rw [lintegral_zero, ← ENNReal.ofReal_zero]
  · intro a (_ : a < _)
    simp only [gammaPDF_eq, ENNReal.ofReal_eq_zero]
    rw [if_neg (by linarith)]

/-- The gamma pdf is measurable. -/
@[fun_prop]
lemma measurable_gammaPDFReal (a r : ℝ) : Measurable (gammaPDFReal a r) :=
  Measurable.ite measurableSet_Ici (((measurable_id'.pow_const _).const_mul _).mul
    (measurable_id'.const_mul _).neg.exp) measurable_const

/-- The gamma pdf is strongly measurable -/
@[fun_prop]
lemma stronglyMeasurable_gammaPDFReal (a r : ℝ) :
    StronglyMeasurable (gammaPDFReal a r) :=
  (measurable_gammaPDFReal a r).stronglyMeasurable

/-- The gamma pdf is positive for all positive reals -/
lemma gammaPDFReal_pos {x a r : ℝ} (ha : 0 < a) (hr : 0 < r) (hx : 0 < x) :
    0 < gammaPDFReal a r x := by
  simp only [gammaPDFReal, if_pos hx.le]
  positivity

/-- The gamma pdf is nonnegative -/
lemma gammaPDFReal_nonneg {a r : ℝ} (ha : 0 < a) (hr : 0 < r) (x : ℝ) :
    0 ≤ gammaPDFReal a r x := by
  unfold gammaPDFReal
  split_ifs <;> positivity

open Measure

/-- The pdf of the gamma distribution integrates to 1 -/
@[simp]
lemma lintegral_gammaPDF_eq_one {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    ∫⁻ x, gammaPDF a r x = 1 := by
  have leftSide : ∫⁻ x in Iio 0, gammaPDF a r x = 0 := by
    rw [setLIntegral_congr_fun measurableSet_Iio
      (fun x (hx : x < 0) ↦ gammaPDF_of_neg hx), lintegral_zero]
  have rightSide : ∫⁻ x in Ici 0, gammaPDF a r x =
      ∫⁻ x in Ici 0, ENNReal.ofReal (r ^ a / Gamma a * x ^ (a - 1) * exp (-(r * x))) :=
    setLIntegral_congr_fun measurableSet_Ici (fun _ ↦ gammaPDF_of_nonneg)
  rw [← ENNReal.toReal_eq_one_iff, ← lintegral_add_compl _ measurableSet_Ici, compl_Ici,
    leftSide, rightSide, add_zero, ← integral_eq_lintegral_of_nonneg_ae]
  · simp_rw [integral_Ici_eq_integral_Ioi, mul_assoc]
    rw [integral_const_mul, integral_rpow_mul_exp_neg_mul_Ioi ha hr, div_mul_eq_mul_div,
      ← mul_assoc, mul_div_assoc, div_self (Gamma_pos_of_pos ha).ne', mul_one,
      div_rpow zero_le_one hr.le, one_rpow, mul_one_div, div_self (rpow_pos_of_pos hr _).ne']
  · rw [EventuallyLE, ae_restrict_iff' measurableSet_Ici]
    exact ae_of_all _ (fun x (hx : 0 ≤ x) ↦ by positivity)
  · apply (measurable_gammaPDFReal a r).aestronglyMeasurable.congr
    refine (ae_restrict_iff' measurableSet_Ici).mpr <| ae_of_all _ fun x (hx : 0 ≤ x) ↦ ?_
    simp_rw [gammaPDFReal, eq_true_intro hx, ite_true]

end GammaPDF

open MeasureTheory

/-- Measure defined by the gamma distribution -/
noncomputable
def gammaMeasure (a r : ℝ) : Measure ℝ :=
  volume.withDensity (gammaPDF a r)

lemma isProbabilityMeasure_gammaMeasure {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    IsProbabilityMeasure (gammaMeasure a r) where
  measure_univ := by simp [gammaMeasure, lintegral_gammaPDF_eq_one ha hr]

section GammaCDF

lemma cdf_gammaMeasure_eq_integral {a r : ℝ} (ha : 0 < a) (hr : 0 < r) (x : ℝ) :
    cdf (gammaMeasure a r) x = ∫ x in Iic x, gammaPDFReal a r x := by
  have : IsProbabilityMeasure (gammaMeasure a r) := isProbabilityMeasure_gammaMeasure ha hr
  rw [cdf_eq_real, gammaMeasure, measureReal_def, withDensity_apply _ measurableSet_Iic]
  refine (integral_eq_lintegral_of_nonneg_ae ?_ ?_).symm
  · exact ae_of_all _ fun b ↦ by simp [gammaPDFReal_nonneg ha hr]
  · fun_prop

lemma cdf_gammaMeasure_eq_lintegral {a r : ℝ} (ha : 0 < a) (hr : 0 < r) (x : ℝ) :
    cdf (gammaMeasure a r) x = ENNReal.toReal (∫⁻ x in Iic x, gammaPDF a r x) := by
  have : IsProbabilityMeasure (gammaMeasure a r) := isProbabilityMeasure_gammaMeasure ha hr
  simp only [gammaPDF, cdf_eq_real]
  simp [gammaMeasure, gammaPDF, measureReal_def]

end GammaCDF

section RPowDivSub

variable {a r : ℝ}

lemma hasDerivAt_rpow_div_sub (ha : 0 < a) (hr : 0 < r) {t : ℝ} (ht : t < r) :
    HasDerivAt (fun t => (r / (r - t)) ^ a) (a * r ^ a / (r - t) ^ (a + 1)) t := by
  have hrt_pos : 0 < r - t := sub_pos.mpr ht
  have hd : HasDerivAt (fun t => r - t) (-1) t := by
      convert (hasDerivAt_const t r).sub (hasDerivAt_id t) using 1; ring
  have h_div : HasDerivAt (fun t => r / (r - t)) (r / (r - t) ^ 2) t := by
    convert (hasDerivAt_const t r).div hd (hrt_pos.ne') using 1; field_simp; ring
  have h_pow := h_div.rpow_const (p := a) (Or.inl (div_ne_zero hr.ne' hrt_pos.ne'))
  convert h_pow using 1; rw [div_rpow hr.le hrt_pos.le]; field_simp
  calc r ^ a * (r - t) ^ 2 * (r - t) ^ (a - 1)
      = r ^ a * ((r - t) ^2 * (r - t) ^ (a - 1)) := by ring
    _ = r ^ a * (r - t) ^ (a + 1) := by
        rw [← rpow_natCast (r - t) 2, ← rpow_add hrt_pos]; congr 1; ring_nf
    _ = r * (r - t) ^ (a + 1) * r ^ (a - 1) := by
        rw [show (a : ℝ) = 1 + (a - 1) from by linarith [ha], rpow_add hr, rpow_one]; ring_nf

lemma deriv_rpow_div_sub_zero (ha : 0 < a) (hr : 0 < r) :
    deriv (fun t => (r / (r - t)) ^ a) 0 = a / r := by
  rw [(hasDerivAt_rpow_div_sub ha hr hr).deriv]; simp only [sub_zero]; field_simp;
  exact (rpow_add_one hr.ne' a).symm

lemma hasDerivAt2_rpow_div_sub (ha : 0 < a) (_hr : 0 < r) {t : ℝ} (ht : t < r) :
    HasDerivAt (fun t => a * r ^ a / (r - t) ^ (a + 1)) (a * (a + 1) * r ^ a / (r - t) ^ (a + 2)) t := by
  have hrt_pos : 0 < r - t := sub_pos.mpr ht
  have hd : HasDerivAt (fun t => r - t) (-1) t := by
        convert (hasDerivAt_const t r).sub (hasDerivAt_id t) using 1; ring
  have h_pow := hd.rpow_const (p := a + 1) (Or.inl hrt_pos.ne')
  have h_inv : HasDerivAt (fun t => ((r - t) ^ (a + 1))⁻¹) ((a + 1) / (r - t) ^ (a + 2)) t := by
    convert( h_pow.inv (rpow_pos_of_pos hrt_pos _).ne') using 1; field_simp
    rw [← rpow_natCast _ 2, ← rpow_mul hrt_pos.le, ← rpow_add hrt_pos]; congr 1; ring
  have h_const := (hasDerivAt_const t (a * r ^ a)).mul h_inv
  convert h_const using 1; field_simp; ring

lemma deriv2_rpow_div_sub_zero (ha : 0 < a) (hr : 0 < r) :
    iteratedDeriv 2 (fun t => (r / (r - t)) ^ a) 0 = a * (a + 1) / r ^ 2 := by
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  have h_eq : deriv (fun t => (r / (r - t)) ^ a) =ᶠ[𝓝 0] fun t => a * r ^ a / (r - t) ^ (a + 1) :=
    eventually_of_mem (Iio_mem_nhds hr) (fun t ht => (hasDerivAt_rpow_div_sub ha hr ht).deriv)
  rw [h_eq.deriv_eq, (hasDerivAt2_rpow_div_sub ha hr hr).deriv, sub_zero]
  field_simp; rw [rpow_add hr]; norm_cast

end RPowDivSub

section MeanVariance

variable {a r : ℝ}

/-- The moment generating function of the gamma distribution with shape `a` and rate `r`
at `t < r` equals `(r / (r - t)) ^ a`. -/
theorem gammaMeasure_mgf (ha : 0 < a) (hr : 0 < r) {t : ℝ} (ht : t < r) :
    mgf id (gammaMeasure a r) t = (r / (r - t)) ^ a := by
  have hrt_pos : 0 < r - t := sub_pos.mpr ht
  simp_rw [mgf, gammaMeasure, integral_withDensity_eq_integral_toReal_smul
    (show Measurable (gammaPDF a r) from (measurable_gammaPDFReal a r).ennreal_ofReal) (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top)),
    smul_eq_mul, gammaPDF, ENNReal.toReal_ofReal (gammaPDFReal_nonneg ha hr _)]
  have hkey x : gammaPDFReal a r x * rexp (t * x) = (r / (r - t)) ^ a * gammaPDFReal a (r - t) x := by
    simp only [gammaPDFReal]; split_ifs with hx
    rw [div_rpow hr.le hrt_pos.le]; field_simp; rw [mul_assoc, ← exp_add]; congr 1; ring_nf; ring
  simp_rw [id_def, hkey, integral_const_mul, integral_eq_lintegral_of_nonneg_ae
    (ae_of_all _ (gammaPDFReal_nonneg ha hrt_pos)) (measurable_gammaPDFReal a _).aestronglyMeasurable]
  have h_eq : (∫⁻ x, ENNReal.ofReal (gammaPDFReal a (r - t) x)) = ∫⁻ x, gammaPDF a (r - t) x :=
    lintegral_congr fun _ => rfl
  rw [h_eq, lintegral_gammaPDF_eq_one ha hrt_pos, ENNReal.toReal_one, mul_one]

lemma gammaMeasure_integrable_exp_mul (ha : 0 < a) (hr : 0 < r) {t : ℝ} (ht : t < r) :
    Integrable (fun x => rexp (t * id x)) (gammaMeasure a r) := by
  have hprob : IsProbabilityMeasure (gammaMeasure a r) := isProbabilityMeasure_gammaMeasure ha hr
  rw [← @mgf_pos_iff _ _ id (gammaMeasure a r) t ⟨hprob.ne_zero⟩, gammaMeasure_mgf ha hr ht]
  exact rpow_pos_of_pos (div_pos hr (sub_pos.mpr ht)) a

lemma gammaMeasure_zero_mem_interior_integrableExpSet (ha : 0 < a) (hr : 0 < r) :
    (0 : ℝ) ∈ interior (integrableExpSet id (gammaMeasure a r)) := by
  refine mem_interior.mpr ⟨Set.Ioo (-1) (r / 2), ?_, isOpen_Ioo, ?_⟩
  intro t ht; exact gammaMeasure_integrable_exp_mul ha hr (by linarith [ht.2]); exact ⟨by linarith, by linarith⟩

lemma mgf_id_gammaMeasure_eventually (ha : 0 < a) (hr : 0 < r) :
    ∀ᶠ t in 𝓝 0, mgf id (gammaMeasure a r) t = (r / (r - t)) ^ a :=
  eventually_of_mem (Iio_mem_nhds hr) fun _ ht => gammaMeasure_mgf ha hr ht

@[simp]
theorem gammaMeasure_mean (ha : 0 < a) (hr : 0 < r) :
    ∫ x, id x ∂gammaMeasure a r = a / r := by
  rw [← deriv_mgf_zero (gammaMeasure_zero_mem_interior_integrableExpSet ha hr),
    Filter.EventuallyEq.deriv_eq (mgf_id_gammaMeasure_eventually ha hr), deriv_rpow_div_sub_zero ha hr]

@[simp]
theorem gammaMeasure_moment_two (ha : 0 < a) (hr : 0 < r) :
    ∫ x, (id ^ 2) x ∂gammaMeasure a r = a * (a + 1) / r ^ 2 := by
  have h := iteratedDeriv_mgf_zero (gammaMeasure_zero_mem_interior_integrableExpSet ha hr) (n := 2)
  rw [← h, Filter.EventuallyEq.iteratedDeriv_eq (n := 2) (mgf_id_gammaMeasure_eventually ha hr),
      deriv2_rpow_div_sub_zero ha hr]

/-- The variance of the Gamma distribution with shape `a` and rate `r` is `a / r ^ 2`. -/
@[simp]
theorem gammaMeasure_variance (ha : 0 < a) (hr : 0 < r) :
    Var[id; gammaMeasure a r] = a / r ^ 2 := by
  have hprob : IsProbabilityMeasure (gammaMeasure a r) := isProbabilityMeasure_gammaMeasure ha hr
  rw [variance_eq_sub (memLp_of_mem_interior_integrableExpSet (gammaMeasure_zero_mem_interior_integrableExpSet ha hr) (p := 2)),
    gammaMeasure_moment_two ha hr, gammaMeasure_mean ha hr]
  ring

end MeanVariance

end ProbabilityTheory
