module

public import HarmonicMaps.Analysis.VariableMollificationTensor
public import HarmonicMaps.Analysis.VariableMollificationAveraging

/-!
# Linearity of the actual variable averages

Pointwise sampling integrability gives ordinary additivity and subtraction
for the literal averages. On the zero-radius region, the unit kernel mass
recovers the original input value pointwise.
-/

public section

open MeasureTheory Set
open scoped BigOperators

namespace HarmonicMaps

/-- Zero sampling radius recovers the original input pointwise. -/
theorem variableMollification_eq_of_zero {n q : ℕ} (s : Domain n → ℝ)
    (f : Domain n → Ambient q) {x : Domain n} (hx : s x = 0) :
    (∫ y in Metric.ball (0 : Domain n) 1,
      fixedMollifierKernel n y • f (variableShift s y x)) = f x := by
  simp only [variableShift, hx, zero_smul, sub_zero]
  rw [integral_smul_const, fixedMollifierKernel_setIntegral, one_smul]

/-- Scalar multiplication is the literal pointwise averaging identity. -/
theorem variableMollification_smul {n q : ℕ} (s : Domain n → ℝ)
    (f : Domain n → Ambient q) (a : ℝ) (x : Domain n) :
    (∫ y in Metric.ball (0 : Domain n) 1,
      fixedMollifierKernel n y • (a • f (variableShift s y x))) =
      a • (∫ y in Metric.ball (0 : Domain n) 1,
        fixedMollifierKernel n y • f (variableShift s y x)) := by
  simp_rw [smul_comm (fixedMollifierKernel n _) a]
  exact integral_smul a _

/-- Additivity uses actual local sampling integrability of both maps. -/
theorem variableMollification_add {n q : ℕ}
    {s : Domain n → ℝ} {theta delta hbar : ℝ}
    (hvalues : ∀ x, 0 ≤ s x ∧ s x ≤ hbar) (hhbar : hbar ≤ delta)
    (hoff : ∀ x ∉ Metric.ball (0 : Domain n) (theta + delta), s x = 0)
    {f g : Domain n → Ambient q}
    (hf : IntegrableOn f (Metric.ball 0 (theta + 2 * delta)) volume)
    (hg : IntegrableOn g (Metric.ball 0 (theta + 2 * delta)) volume) (x : Domain n) :
    (∫ y in Metric.ball (0 : Domain n) 1,
      fixedMollifierKernel n y • (f (variableShift s y x) + g (variableShift s y x))) =
      (∫ y in Metric.ball (0 : Domain n) 1, fixedMollifierKernel n y • f (variableShift s y x)) +
      (∫ y in Metric.ball (0 : Domain n) 1, fixedMollifierKernel n y • g (variableShift s y x)) := by
  simp_rw [smul_add]
  exact integral_add (variableMollification_weighted_sampling_integrable hvalues hhbar hoff hf x)
    (variableMollification_weighted_sampling_integrable hvalues hhbar hoff hg x)

/-- Subtraction identifies the literal average of a map difference. -/
theorem variableMollification_sub {n q : ℕ}
    {s : Domain n → ℝ} {theta delta hbar : ℝ}
    (hvalues : ∀ x, 0 ≤ s x ∧ s x ≤ hbar) (hhbar : hbar ≤ delta)
    (hoff : ∀ x ∉ Metric.ball (0 : Domain n) (theta + delta), s x = 0)
    {f g : Domain n → Ambient q}
    (hf : IntegrableOn f (Metric.ball 0 (theta + 2 * delta)) volume)
    (hg : IntegrableOn g (Metric.ball 0 (theta + 2 * delta)) volume) (x : Domain n) :
    (∫ y in Metric.ball (0 : Domain n) 1,
      fixedMollifierKernel n y • (f (variableShift s y x) - g (variableShift s y x))) =
      (∫ y in Metric.ball (0 : Domain n) 1, fixedMollifierKernel n y • f (variableShift s y x)) -
      (∫ y in Metric.ball (0 : Domain n) 1, fixedMollifierKernel n y • g (variableShift s y x)) := by
  simp_rw [smul_sub]
  exact integral_sub (variableMollification_weighted_sampling_integrable hvalues hhbar hoff hf x)
    (variableMollification_weighted_sampling_integrable hvalues hhbar hoff hg x)

/-- Tensor subtraction preserves the same original gradient columns in the
literal average of the difference field. -/
theorem variableMollification_tensor_sub {n q : ℕ}
    {s : Domain n → ℝ} {theta delta hbar : ℝ}
    (hvalues : ∀ x, 0 ≤ s x ∧ s x ≤ hbar) (hhbar : hbar ≤ delta)
    (hoff : ∀ x ∉ Metric.ball (0 : Domain n) (theta + delta), s x = 0)
    {Df Dg : Domain n → Gradient n q}
    (hDf : ∀ j : Fin n, IntegrableOn (fun z => Df z j)
      (Metric.ball 0 (theta + 2 * delta)) volume)
    (hDg : ∀ j : Fin n, IntegrableOn (fun z => Dg z j)
      (Metric.ball 0 (theta + 2 * delta)) volume) (x : Domain n) (i : Fin n) :
    let c := fun y (j : Fin n) => ((ContinuousLinearMap.id ℝ (Domain n) -
      (fderiv ℝ s x).smulRight y) (EuclideanSpace.single i 1)) j
    (∫ y in Metric.ball (0 : Domain n) 1, fixedMollifierKernel n y •
      ∑ j : Fin n, c y j • (Df (variableShift s y x) j - Dg (variableShift s y x) j)) =
      (∫ y in Metric.ball (0 : Domain n) 1, fixedMollifierKernel n y •
        ∑ j : Fin n, c y j • Df (variableShift s y x) j) -
      (∫ y in Metric.ball (0 : Domain n) 1, fixedMollifierKernel n y •
        ∑ j : Fin n, c y j • Dg (variableShift s y x) j) := by
  dsimp only
  simp_rw [smul_sub, Finset.sum_sub_distrib, smul_sub]
  exact integral_sub (variableMollification_tensor_integrable hvalues hhbar hoff hDf x i)
    (variableMollification_tensor_integrable hvalues hhbar hoff hDg x i)

end HarmonicMaps
