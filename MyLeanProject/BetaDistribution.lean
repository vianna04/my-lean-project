/-
Copyright (c) 2025 Tommy Löfgren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tommy Löfgren
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Probability.Moments.Variance

/-! # Beta distributions over ℝ

Define the beta distribution over the reals.

## Main definitions
* `betaPDFReal`: the function `α β x ↦ (1 / beta α β) * x ^ (α - 1) * (1 - x) ^ (β - 1)`
  for `0 < x ∧ x < 1` or `0` else, which is the probability density function of a beta distribution
  with shape parameters `α` and `β` (when `0 < α` and `0 < β`).
* `betaPDF`: `ℝ≥0∞`-valued pdf,
  `betaPDF α β = ENNReal.ofReal (betaPDFReal α β)`.
-/

@[expose] public section

open scoped ENNReal NNReal

open MeasureTheory Complex Set

namespace ProbabilityTheory

section BetaPDF

/-- The normalizing constant in the beta distribution. -/
noncomputable def beta (α β : ℝ) : ℝ :=
  Real.Gamma α * Real.Gamma β / Real.Gamma (α + β)

lemma beta_pos {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) : 0 < beta α β :=
  div_pos (mul_pos (Real.Gamma_pos_of_pos hα) (Real.Gamma_pos_of_pos hβ))
    (Real.Gamma_pos_of_pos (add_pos hα hβ))

/-- Relation between the beta function and the gamma function over the reals. -/
theorem beta_eq_betaIntegralReal (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    beta α β = (betaIntegral α β).re := by
  rw [betaIntegral_eq_Gamma_mul_div]
  · simp_rw [beta, ← ofReal_add α β, Gamma_ofReal]
    norm_cast
  all_goals simpa

/-- The probability density function of the beta distribution with shape parameters `α` and `β`.
Returns `(1 / beta α β) * x ^ (α - 1) * (1 - x) ^ (β - 1)`
when `0 < x < 1` and `0` otherwise. -/
noncomputable def betaPDFReal (α β x : ℝ) : ℝ :=
  if 0 < x ∧ x < 1 then
    (1 / beta α β) * x ^ (α - 1) * (1 - x) ^ (β - 1)
  else
    0

/-- The pdf of the beta distribution, as a function valued in `ℝ≥0∞`. -/
noncomputable def betaPDF (α β x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (betaPDFReal α β x)

lemma betaPDF_eq (α β x : ℝ) :
    betaPDF α β x =
      ENNReal.ofReal (if 0 < x ∧ x < 1 then
        (1 / beta α β) * x ^ (α - 1) * (1 - x) ^ (β - 1) else 0) := rfl

lemma betaPDF_eq_zero_of_nonpos {α β x : ℝ} (hx : x ≤ 0) :
    betaPDF α β x = 0 := by
  simp [betaPDF_eq, hx.not_gt]

lemma betaPDF_eq_zero_of_one_le {α β x : ℝ} (hx : 1 ≤ x) :
    betaPDF α β x = 0 := by
  simp [betaPDF_eq, hx.not_gt]

lemma betaPDF_of_pos_lt_one {α β x : ℝ} (hx_pos : 0 < x) (hx_lt : x < 1) :
    betaPDF α β x = ENNReal.ofReal ((1 / beta α β) * x ^ (α - 1) * (1 - x) ^ (β - 1)) := by
  rw [betaPDF_eq, if_pos ⟨hx_pos, hx_lt⟩]

lemma lintegral_betaPDF {α β : ℝ} :
    ∫⁻ x, betaPDF α β x =
      ∫⁻ (x : ℝ) in Ioo 0 1, ENNReal.ofReal (1 / beta α β * x ^ (α - 1) * (1 - x) ^ (β - 1)) := by
  rw [← lintegral_add_compl _ measurableSet_Iic,
    setLIntegral_eq_zero measurableSet_Iic (fun x (hx : x ≤ 0) ↦ betaPDF_eq_zero_of_nonpos hx),
    zero_add, compl_Iic, ← lintegral_add_compl _ measurableSet_Ici,
    setLIntegral_eq_zero measurableSet_Ici (fun x (hx : 1 ≤ x) ↦ betaPDF_eq_zero_of_one_le hx),
    zero_add, compl_Ici, Measure.restrict_restrict measurableSet_Iio, Iio_inter_Ioi,
    setLIntegral_congr_fun measurableSet_Ioo
      (fun x ⟨hx_pos, hx_lt⟩ ↦ betaPDF_of_pos_lt_one hx_pos hx_lt)]

/-- The beta pdf is positive for all positive reals with positive parameters. -/
lemma betaPDFReal_pos {α β x : ℝ} (hx1 : 0 < x) (hx2 : x < 1) (hα : 0 < α) (hβ : 0 < β) :
    0 < betaPDFReal α β x := by
  rw [betaPDFReal, if_pos ⟨hx1, hx2⟩]
  exact mul_pos (mul_pos (one_div_pos.2 (beta_pos hα hβ)) (Real.rpow_pos_of_pos hx1 (α - 1)))
    (Real.rpow_pos_of_pos (by linarith) (β - 1))

lemma betaPDFReal_nonneg {α β x : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    0 ≤ betaPDFReal α β x := by
  unfold betaPDFReal
  split_ifs with h
  · apply mul_nonneg
    · apply mul_nonneg
      · exact le_of_lt (div_pos one_pos (beta_pos hα hβ))
      · exact Real.rpow_nonneg (le_of_lt h.1) _
    · exact Real.rpow_nonneg (by linarith [h.2]) _
  · linarith

/-- The beta pdf is measurable. -/
@[fun_prop]
lemma measurable_betaPDFReal (α β : ℝ) : Measurable (betaPDFReal α β) :=
  Measurable.ite measurableSet_Ioo (by fun_prop) (by fun_prop)

/-- The beta pdf is strongly measurable. -/
@[fun_prop]
lemma stronglyMeasurable_betaPDFReal (α β : ℝ) :
    StronglyMeasurable (betaPDFReal α β) := (measurable_betaPDFReal α β).stronglyMeasurable

set_option backward.isDefEq.respectTransparency false in
/-- The pdf of the beta distribution integrates to 1. -/
@[simp]
lemma lintegral_betaPDF_eq_one {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    ∫⁻ x, betaPDF α β x = 1 := by
  rw [lintegral_betaPDF, ← ENNReal.toReal_eq_one_iff, ← integral_eq_lintegral_of_nonneg_ae]
  · simp_rw [mul_assoc, integral_const_mul]
    field_simp
    rw [div_eq_one_iff_eq (ne_of_gt (beta_pos hα hβ)), beta_eq_betaIntegralReal α β hα hβ,
      betaIntegral, intervalIntegral.integral_of_le (by norm_num),
      ← integral_Ioc_eq_integral_Ioo, ← RCLike.re_to_complex, ← integral_re]
    · refine setIntegral_congr_fun measurableSet_Ioc fun x ⟨hx1, hx₂⟩ ↦ ?_
      norm_cast
      rw [← Complex.ofReal_cpow, ← Complex.ofReal_cpow, RCLike.re_to_complex,
        Complex.re_mul_ofReal, Complex.ofReal_re]
      all_goals linarith
    convert betaIntegral_convergent (u := α) (v := β) (by simpa) (by simpa)
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by simp), IntegrableOn]
  · refine ae_restrict_of_forall_mem measurableSet_Ioo (fun x hx ↦ ?_)
    convert betaPDFReal_pos hx.1 hx.2 hα hβ |>.le using 1
    rw [betaPDFReal, if_pos ⟨hx.1, hx.2⟩]
  · exact Measurable.aestronglyMeasurable (by fun_prop)

end BetaPDF

/-- Measure defined by the beta distribution. -/
noncomputable
def betaMeasure (α β : ℝ) : Measure ℝ :=
  volume.withDensity (betaPDF α β)

lemma isProbabilityMeasureBeta {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    IsProbabilityMeasure (betaMeasure α β) where
  measure_univ := by simp [betaMeasure, lintegral_betaPDF_eq_one hα hβ]

lemma isProbabilityMeasure_betaMeasure {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    IsProbabilityMeasure (betaMeasure α β) where
  measure_univ := by simp [betaMeasure, lintegral_betaPDF_eq_one hα hβ]

section MeanVariance

variable {α β : ℝ}

lemma beta_ratio_succ_left (hα : 0 < α) (hβ : 0 < β) :
    beta (α + 1) β / beta α β = α / (α + β) := by
  simp only [beta]
  rw [Real.Gamma_add_one hα.ne']
  have hab : α + 1 + β = α + β + 1 := by ring
  rw [hab, Real.Gamma_add_one (add_pos hα hβ).ne']
  field_simp

lemma beta_ratio_succ_left_two (hα : 0 < α) (hβ : 0 < β) :
    beta (α + 2) β / beta α β = α * (α + 1) / ((α + β) * (α + β + 1)) := by
  have hb1 : beta (α + 1) β ≠ 0 := (beta_pos (by linarith) hβ).ne'
  rw [show (α + 2 : ℝ) = (α + 1) + 1 from by ring]
  rw [← div_mul_div_cancel₀ hb1 (a := beta ((α + 1) + 1) β) (c := beta α β),
    beta_ratio_succ_left (by linarith) hβ, beta_ratio_succ_left hα hβ,
    show α + 1 + β = α + β + 1 from by ring]
  field_simp;

lemma betaMeasure_integrable_id (hα : 0 < α) (hβ : 0 < β) :
    Integrable (fun x => x) (betaMeasure α β) := by
  have hprob := isProbabilityMeasure_betaMeasure hα hβ
  refine ⟨measurable_id.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have hmeas : Measurable (fun x => ENNReal.ofReal (betaPDFReal α β x)) :=
    (measurable_betaPDFReal α β).ennreal_ofReal
  calc ∫⁻ x, ‖x‖₊ ∂betaMeasure α β
      ≤ ∫⁻ _, 1 ∂betaMeasure α β := by
        apply lintegral_mono_ae
        show ∀ᵐ x ∂volume.withDensity (fun x => ENNReal.ofReal (betaPDFReal α β x)),
          (‖x‖₊ : ℝ≥0∞) ≤ 1
        rw [ae_withDensity_iff hmeas]
        apply ae_of_all; intro x hx
        have hpos : 0 < betaPDFReal α β x := by
          rcases (ENNReal.ofReal_eq_zero.not.mp hx) with h; push Not at h; exact h
        simp only [betaPDFReal] at hpos; split_ifs at hpos with h
        · rw [Real.nnnorm_of_nonneg h.1.le]; exact_mod_cast h.2.le
        · linarith
    _ = 1 := by simp [hprob.measure_univ]
    _ < ⊤ := ENNReal.one_lt_top

lemma betaMeasure_integrable_sq (hα : 0 < α) (hβ : 0 < β) :
    Integrable (fun x => x ^ 2) (betaMeasure α β) := by
  have hprob := isProbabilityMeasure_betaMeasure hα hβ
  have hmeas : Measurable (fun x => ENNReal.ofReal (betaPDFReal α β x)) :=
    (measurable_betaPDFReal α β).ennreal_ofReal
  refine ⟨(measurable_id.pow_const 2).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  calc ∫⁻ x, ‖x ^ 2‖₊ ∂betaMeasure α β
      ≤ ∫⁻ _, 1 ∂betaMeasure α β := by
        apply lintegral_mono_ae
        show ∀ᵐ x ∂volume.withDensity (fun x => ENNReal.ofReal (betaPDFReal α β x)),
          (‖x ^ 2‖₊ : ℝ≥0∞) ≤ 1
        rw [ae_withDensity_iff hmeas]
        apply ae_of_all; intro x hx
        have hpos : 0 < betaPDFReal α β x := by
          rcases (ENNReal.ofReal_eq_zero.not.mp hx) with h; push Not at h; exact h
        simp only [betaPDFReal] at hpos; split_ifs at hpos with h
        · rw [Real.nnnorm_of_nonneg (sq_nonneg x)]; exact_mod_cast (by nlinarith [h.2] : x ^ 2 ≤ 1)
        · linarith
    _ = 1 := by simp [hprob.measure_univ]
    _ < ⊤ := ENNReal.one_lt_top

lemma integral_id_eq_beta_ratio (hα : 0 < α) (hβ : 0 < β) :
    ∫ x : ℝ, x * betaPDFReal α β x = beta (α + 1) β / beta α β := by
  have hα1 : (0 : ℝ) < α + 1 := by linarith
  have hkey : ∀ x : ℝ, x * betaPDFReal α β x =
      (beta (α + 1) β / beta α β) * betaPDFReal (α + 1) β x := by
    intro x; simp only [betaPDFReal]; split_ifs with h
    · rw [show x ^ (α + 1 - 1) = x ^ (α - 1) * x from by
        rw [show α + 1 - 1 = α - 1 + 1 from by ring, Real.rpow_add h.1, Real.rpow_one]]
      simp only [beta]; field_simp
    · simp
  rw [integral_congr_ae (ae_of_all _ hkey), integral_const_mul]
  have : ∫ a, betaPDFReal (α + 1) β a = 1 := by
    rw [integral_eq_lintegral_of_nonneg_ae
      (ae_of_all _ (fun x => betaPDFReal_nonneg hα1 hβ))
      (measurable_betaPDFReal (α + 1) β).aestronglyMeasurable]
    have h := lintegral_betaPDF_eq_one hα1 hβ
    simp only [betaPDF] at h
    rw [h, ENNReal.toReal_one]
  rw [this, mul_one]

lemma integral_sq_eq_beta_ratio (hα : 0 < α) (hβ : 0 < β) :
    ∫ x : ℝ, x ^ 2 * betaPDFReal α β x = beta (α + 2) β / beta α β := by
  have hα2 : (0 : ℝ) < α + 2 := by linarith
  have hkey : ∀ x : ℝ, x ^ 2 * betaPDFReal α β x =
      (beta (α + 2) β / beta α β) * betaPDFReal (α + 2) β x := by
    intro x; simp only [betaPDFReal]; split_ifs with h
    · rw [show x ^ (α + 2 - 1) = x ^ (α - 1) * x ^ 2 from by
        rw [show α + 2 - 1 = α - 1 + 2 from by ring, Real.rpow_add h.1]; simp]
      simp only [beta]; field_simp
    · simp
  rw [integral_congr_ae (ae_of_all _ hkey), integral_const_mul]
  have : ∫ a, betaPDFReal (α + 2) β a = 1 := by
    rw [integral_eq_lintegral_of_nonneg_ae
      (ae_of_all _ (fun x => betaPDFReal_nonneg hα2 hβ))
      (measurable_betaPDFReal (α + 2) β).aestronglyMeasurable]
    have h := lintegral_betaPDF_eq_one hα2 hβ
    simp only [betaPDF] at h
    rw [h, ENNReal.toReal_one]
  rw [this, mul_one]

theorem betaMeasure_mean (hα : 0 < α) (hβ : 0 < β) :
    ∫ x, x ∂betaMeasure α β = α / (α + β) := by
  have hmeas : Measurable (betaPDF α β) := (measurable_betaPDFReal α β).ennreal_ofReal
  have hlt_top : ∀ x, betaPDF α β x < ⊤ := fun _ => ENNReal.ofReal_lt_top
  rw [betaMeasure, integral_withDensity_eq_integral_toReal_smul hmeas (ae_of_all _ hlt_top)]
  simp only [smul_eq_mul]
  simp_rw [betaPDF, ENNReal.toReal_ofReal (betaPDFReal_nonneg hα hβ)]
  rw [show ∫ x, betaPDFReal α β x * x = ∫ x, x * betaPDFReal α β x from by
    congr 1; ext x; ring]
  rw [integral_id_eq_beta_ratio hα hβ, beta_ratio_succ_left hα hβ]

theorem betaMeasure_variance (hα : 0 < α) (hβ : 0 < β) :
    Var[fun x => x; betaMeasure α β] = α * β / ((α + β) ^ 2 * (α + β + 1)) := by
  have hprob := isProbabilityMeasure_betaMeasure hα hβ
  rw [variance_eq_integral measurable_id'.aemeasurable, betaMeasure_mean hα hβ]
  have hmeas : Measurable (betaPDF α β) := (measurable_betaPDFReal α β).ennreal_ofReal
  have hlt_top : ∀ x, betaPDF α β x < ⊤ := fun _ => ENNReal.ofReal_lt_top
  have h_moment2 : ∫ x, x ^ 2 ∂betaMeasure α β = α * (α + 1) / ((α + β) * (α + β + 1)) := by
    rw [betaMeasure, integral_withDensity_eq_integral_toReal_smul hmeas (ae_of_all _ hlt_top)]
    simp only [smul_eq_mul]
    simp_rw [betaPDF, ENNReal.toReal_ofReal (betaPDFReal_nonneg hα hβ)]
    rw [show ∫ x, betaPDFReal α β x * x ^ 2 = ∫ x, x ^ 2 * betaPDFReal α β x from by
      congr 1; ext x; ring]
    rw [integral_sq_eq_beta_ratio hα hβ, beta_ratio_succ_left_two hα hβ]
  have hint1 : Integrable (fun ω => -2 * (α / (α + β)) * ω) (betaMeasure α β) :=
    (betaMeasure_integrable_id hα hβ).const_mul _
  have hint2 : Integrable (fun ω => -2 * (α / (α + β)) * ω + (α / (α + β)) ^ 2)
      (betaMeasure α β) := hint1.add (integrable_const _)
  calc ∫ ω, (ω - α / (α + β)) ^ 2 ∂betaMeasure α β
      = ∫ ω, (ω ^ 2 + (-2 * (α / (α + β)) * ω + (α / (α + β)) ^ 2))
          ∂betaMeasure α β := by congr 1; ext ω; ring
    _ = ∫ ω, ω ^ 2 ∂betaMeasure α β +
          ∫ ω, (-2 * (α / (α + β)) * ω + (α / (α + β)) ^ 2) ∂betaMeasure α β :=
          integral_add (betaMeasure_integrable_sq hα hβ) hint2
    _ = ∫ ω, ω ^ 2 ∂betaMeasure α β +
          (-2 * (α / (α + β)) * ∫ ω, ω ∂betaMeasure α β + (α / (α + β)) ^ 2) := by
          rw [integral_add hint1 (integrable_const _), integral_const_mul, integral_const,
            show (betaMeasure α β).real Set.univ = 1 from by simp [measureReal_def], one_smul]
    _ = α * β / ((α + β) ^ 2 * (α + β + 1)) := by
          rw [h_moment2, betaMeasure_mean hα hβ]; field_simp; ring

end MeanVariance

end ProbabilityTheory
