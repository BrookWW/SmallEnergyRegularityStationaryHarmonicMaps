module

public import HarmonicMaps.Analysis.MollificationJensen
public import HarmonicMaps.Analysis.SobolevMollificationGradient

/-!
# Total Hilbert--Schmidt energy of mollified gradients

The literal averages of the gradient columns have energy at most the input
unit-ball energy, with multiplicative constant one.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace HarmonicMaps

noncomputable section

/-- Pointwise Jensen for the literal averages of all gradient columns. -/
theorem sourceMollifiedGradient_hsNormSq_le {n q : ℕ}
    {Du : Domain n → Gradient n q}
    (hDu : ∀ i : Fin n, MemLp (fun z => Du z i) 2
      (volume.restrict (Metric.ball (0 : Domain n) 1)))
    (h : PositiveRadius) (hh : h.val ≤ 1 / 4) {x : Domain n}
    (hx : x ∈ Metric.ball (0 : Domain n) (3 / 4)) :
    hsNormSq (fun i => ∫ y in Metric.ball (0 : Domain n) 1,
      fixedMollifierKernel n y • Du (x - h.val • y) i) ≤
      ∫ y in Metric.ball (0 : Domain n) 1,
        fixedMollifierKernel n y * hsNormSq (Du (x - h.val • y)) := by
  change (∑ i : Fin n, ‖∫ y in Metric.ball (0 : Domain n) 1,
    fixedMollifierKernel n y • Du (x - h.val • y) i‖ ^ 2) ≤
    ∫ y in Metric.ball (0 : Domain n) 1,
      fixedMollifierKernel n y * ∑ i : Fin n, ‖Du (x - h.val • y) i‖ ^ 2
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum]
  · exact Finset.sum_le_sum fun i _ => sourceMollification_column_jensen (hDu i) h hh hx
  · exact fun i _ => sourceMollification_column_integrable_energyIntegrand (hDu i) h hh hx

/-- Column L2 data imply integrability of the averaged HS density on the half ball. -/
theorem sourceMollifiedGradient_integrable_hsNormSq {n q : ℕ}
    {Du : Domain n → Gradient n q}
    (hDu : ∀ i : Fin n, MemLp (fun z => Du z i) 2
      (volume.restrict (Metric.ball (0 : Domain n) 1)))
    (h : PositiveRadius) (hh : h.val ≤ 1 / 4) :
    IntegrableOn (fun x => hsNormSq ((fun i => ∫ y in Metric.ball (0 : Domain n) 1,
        fixedMollifierKernel n y • Du (x - h.val • y) i)))
      (Metric.ball (0 : Domain n) (1 / 2)) volume := by
  exact integrable_finsetSum Finset.univ fun i _ =>
    sourceMollification_column_integrable_norm_sq (hDu i) h hh

/-- Jensen and Fubini bound the genuine averaged HS energy with exact factor one. -/
theorem sourceMollifiedGradient_energy_le {n q : ℕ}
    {Du : Domain n → Gradient n q}
    (hDu : ∀ i : Fin n, MemLp (fun z => Du z i) 2
      (volume.restrict (Metric.ball (0 : Domain n) 1)))
    (h : PositiveRadius) (hh : h.val ≤ 1 / 4) :
    (∫ x in Metric.ball (0 : Domain n) (1 / 2),
      hsNormSq ((fun i => ∫ y in Metric.ball (0 : Domain n) 1,
        fixedMollifierKernel n y • Du (x - h.val • y) i))) ≤
      ∫ z in Metric.ball (0 : Domain n) 1, hsNormSq (Du z) := by
  change (∫ x in Metric.ball (0 : Domain n) (1 / 2),
    ∑ i : Fin n, ‖∫ y in Metric.ball (0 : Domain n) 1,
      fixedMollifierKernel n y • Du (x - h.val • y) i‖ ^ 2) ≤
    ∫ z in Metric.ball (0 : Domain n) 1, ∑ i : Fin n, ‖Du z i‖ ^ 2
  rw [integral_finsetSum, integral_finsetSum]
  · exact Finset.sum_le_sum fun i _ => sourceMollification_column_energy_le (hDu i) h hh
  · exact fun i _ => (hDu i).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
  · exact fun i _ => sourceMollification_column_integrable_norm_sq (hDu i) h hh

/-- The extended energies satisfy the same bound; both densities are genuinely integrable. -/
theorem sourceMollifiedGradient_dirichletEnergy_le {n q : ℕ}
    {Du : Domain n → Gradient n q}
    (hDu : ∀ i : Fin n, MemLp (fun z => Du z i) 2
      (volume.restrict (Metric.ball (0 : Domain n) 1)))
    (h : PositiveRadius) (hh : h.val ≤ 1 / 4) :
    dirichletEnergy ((fun x i => ∫ y in Metric.ball (0 : Domain n) 1,
      fixedMollifierKernel n y • Du (x - h.val • y) i)) (Metric.ball (0 : Domain n) (1 / 2)) ≤
      dirichletEnergy Du (Metric.ball (0 : Domain n) 1) := by
  rw [dirichletEnergy_eq_ofReal_integral
    (sourceMollifiedGradient_integrable_hsNormSq hDu h hh),
    dirichletEnergy_eq_ofReal_integral (integrable_hsNormSq_of_memLp_columns hDu)]
  exact ENNReal.ofReal_le_ofReal (sourceMollifiedGradient_energy_le hDu h hh)

/-- The actual classical gradient of the globally smooth convolution auxiliary. -/
def zeroExtendedMollificationGradient {n q : ℕ} (u : Domain n → Ambient q)
    (hu : IntegrableOn u (Metric.ball (0 : Domain n) 1))
    (h : PositiveRadius) (x : Domain n) : Gradient n q :=
  fun i => coordinateDerivative (zeroExtendedMollification u hu h)
    (zeroExtendedMollification_contDiff u hu h) i x

/-- The actual smooth gradient equals the literal averages of the same weak gradient. -/
theorem MemW12.zeroExtendedMollificationGradient_eq {n q : ℕ}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12 (ballDomain (0 : Domain n) 1) u Du)
    (h : PositiveRadius) (hh : h.val ≤ 1 / 4) {x : Domain n}
    (hx : x ∈ Metric.ball (0 : Domain n) (3 / 4)) :
    zeroExtendedMollificationGradient u hu.integrable_unitBall h x =
      (fun i => ∫ y in Metric.ball (0 : Domain n) 1,
        fixedMollifierKernel n y • Du (x - h.val • y) i) := by
  funext i
  exact hu.zeroExtendedMollification_coordinateDerivative h hh hx i

/-- Finite Sobolev data make the actual mollified HS density integrable on B1/2. -/
theorem MemW12.zeroExtendedMollification_integrable_hsNormSq {n q : ℕ}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12 (ballDomain (0 : Domain n) 1) u Du)
    (h : PositiveRadius) (hh : h.val ≤ 1 / 4) :
    IntegrableOn (fun x => hsNormSq
      (zeroExtendedMollificationGradient u hu.integrable_unitBall h x))
      (Metric.ball (0 : Domain n) (1 / 2)) volume := by
  apply (sourceMollifiedGradient_integrable_hsNormSq hu.2.2 h hh).congr_fun _
    measurableSet_ball
  intro x hx
  exact congrArg hsNormSq (hu.zeroExtendedMollificationGradient_eq h hh
    (Metric.ball_subset_ball (by norm_num : (1 / 2 : ℝ) ≤ 3 / 4) hx)).symm

/-- The source total-energy estimate for the actual classical mollification gradient. -/
theorem MemW12.zeroExtendedMollification_energy_le {n q : ℕ}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12 (ballDomain (0 : Domain n) 1) u Du)
    (h : PositiveRadius) (hh : h.val ≤ 1 / 4) :
    (∫ x in Metric.ball (0 : Domain n) (1 / 2), hsNormSq
      (zeroExtendedMollificationGradient u hu.integrable_unitBall h x)) ≤
      ∫ z in Metric.ball (0 : Domain n) 1, hsNormSq (Du z) := by
  calc
    (∫ x in Metric.ball (0 : Domain n) (1 / 2), hsNormSq
        (zeroExtendedMollificationGradient u hu.integrable_unitBall h x)) =
        ∫ x in Metric.ball (0 : Domain n) (1 / 2), hsNormSq
          ((fun i => ∫ y in Metric.ball (0 : Domain n) 1,
        fixedMollifierKernel n y • Du (x - h.val • y) i)) := by
      apply setIntegral_congr_fun measurableSet_ball
      intro x hx
      exact congrArg hsNormSq (hu.zeroExtendedMollificationGradient_eq h hh
        (Metric.ball_subset_ball (by norm_num : (1 / 2 : ℝ) ≤ 3 / 4) hx))
    _ ≤ ∫ z in Metric.ball (0 : Domain n) 1, hsNormSq (Du z) :=
      sourceMollifiedGradient_energy_le hu.2.2 h hh

/-- The genuine extended Dirichlet energy obeys the source estimate with factor one. -/
theorem MemW12.zeroExtendedMollification_dirichletEnergy_le {n q : ℕ}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12 (ballDomain (0 : Domain n) 1) u Du)
    (h : PositiveRadius) (hh : h.val ≤ 1 / 4) :
    dirichletEnergy (zeroExtendedMollificationGradient u hu.integrable_unitBall h)
      (Metric.ball (0 : Domain n) (1 / 2)) ≤
      dirichletEnergy Du (Metric.ball (0 : Domain n) 1) := by
  have hInput : IntegrableOn (fun z => hsNormSq (Du z))
      (Metric.ball (0 : Domain n) 1) volume := hu.integrable_hsNormSq
  rw [dirichletEnergy_eq_ofReal_integral
    (hu.zeroExtendedMollification_integrable_hsNormSq h hh),
    dirichletEnergy_eq_ofReal_integral hInput]
  exact ENNReal.ofReal_le_ofReal (hu.zeroExtendedMollification_energy_le h hh)

end
end HarmonicMaps

end
