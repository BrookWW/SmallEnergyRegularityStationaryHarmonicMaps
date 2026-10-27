module

public import HarmonicMaps.Analysis.MollificationLocalKernel
public import HarmonicMaps.Analysis.MollificationEnergy
public import HarmonicMaps.Analysis.FiniteEnergySobolev
public import HarmonicMaps.Analysis.CenteredEnergy

/-!
# Pointwise Hilbert--Schmidt gradient bounds for source mollification

The classical columns of the literal source integral equal averages of the
original weak-gradient columns. Hilbert--Schmidt Jensen, the fixed kernel
majorant, and centered energy give a dimension-only pointwise bound.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace HarmonicMaps

noncomputable section

/-- Jensen and the local kernel estimate bound the actual classical HS gradient. -/
theorem MemW12.sourceMollification_pointwise_hsNormSq_le {n q : ℕ}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12 (ballDomain (0 : Domain n) 1) u Du)
    (h : PositiveRadius) (hh : h.val ≤ 1 / 4) {x : Domain n}
    (hx : x ∈ Metric.ball (0 : Domain n) (3 / 4)) :
    let m : Domain n → Ambient q := fun x =>
      ∫ y in Metric.ball (0 : Domain n) 1,
        fixedMollifierKernel n y • u (x - h.val • y)
    hsNormSq (fun i => fderiv ℝ m x (EuclideanSpace.single i 1)) ≤
      fixedMollifierKernelBound n * (h.val ^ n)⁻¹ *
        ∫ z in Metric.ball x h.val, hsNormSq (Du z) := by
  dsimp only
  have hsubset : Metric.ball x h.val ⊆ Metric.ball (0 : Domain n) 1 := by
    apply Metric.ball_subset_ball'
    have hxd : dist x (0 : Domain n) < 3 / 4 := hx
    linarith only [hxd, hh]
  have hi := hu.integrable_hsNormSq.mono_set hsubset
  have hkernel := mollification_local_kernel_estimate h x hi
    (Filter.Eventually.of_forall fun z => hsNormSq_nonneg (Du z))
    (fixedMollifierKernel_le_bound n)
  have hcolumns :
      (fun i => fderiv ℝ (fun x : Domain n => ∫ y in Metric.ball (0 : Domain n) 1,
        fixedMollifierKernel n y • u (x - h.val • y)) x (EuclideanSpace.single i 1)) =
      (fun i => ∫ y in Metric.ball (0 : Domain n) 1,
        fixedMollifierKernel n y • Du (x - h.val • y) i) := by
    funext i
    exact hu.sourceMollification_coordinateDerivative h hh hx i
  rw [hcolumns]
  exact (sourceMollifiedGradient_hsNormSq_le hu.2.2 h hh hx).trans hkernel.2

private theorem mollification_energy_scale {n : ℕ} (hn : 2 ≤ n)
    (h : PositiveRadius) :
    (h.val ^ n)⁻¹ * h.val ^ (n - 2) = h.val ^ (-2 : ℤ) := by
  have hpow : h.val ^ n = h.val ^ (n - 2) * h.val ^ 2 := by
    conv_lhs => rw [show n = (n - 2) + 2 by omega, pow_add]
  rw [hpow, mul_inv_rev, mul_assoc,
    inv_mul_cancel₀ (pow_ne_zero (n - 2) h.property.ne'), mul_one]
  rw [zpow_neg]
  rfl

/-- The source pointwise gradient estimate uses one explicit dimension-only coefficient. -/
theorem IsLocallyEnergyMinimizing.sourceMollification_pointwise_gradient_bound
    {n q : ℕ} (hn : 2 ≤ n) (N : CompactSmoothEmbeddedTarget q)
    (u : Domain n → Ambient q) (Du : Domain n → Gradient n q)
    (hu : MemW12Loc (ballDomain (0 : Domain n) 1) u Du)
    (hN : TakesValuesIn N (ballDomain (0 : Domain n) 1) u)
    (hmin : IsLocallyEnergyMinimizing N (ballDomain (0 : Domain n) 1) u Du)
    (hE : dirichletEnergy Du (Metric.ball (0 : Domain n) 1) ≠ ⊤)
    (h : PositiveRadius) (hh : h.val ≤ 1 / 4) (x : Domain n)
    (hx : x ∈ Metric.ball (0 : Domain n) (1 / 2)) :
    let m : Domain n → Ambient q := fun x =>
      ∫ y in Metric.ball (0 : Domain n) 1,
        fixedMollifierKernel n y • u (x - h.val • y)
    hsNormSq (fun i => fderiv ℝ m x (EuclideanSpace.single i 1)) ≤
      (fixedMollifierKernelBound n * (2 : ℝ) ^ (n - 2)) *
        (dirichletEnergy Du (Metric.ball (0 : Domain n) 1)).toReal *
          h.val ^ (-2 : ℤ) := by
  have hfinite := hu.memW12_unitBall_of_finiteEnergy N hN hE
  have hx' : x ∈ Metric.ball (0 : Domain n) (3 / 4) :=
    Metric.ball_subset_ball (by norm_num : (1 / 2 : ℝ) ≤ 3 / 4) hx
  have hcenter := hmin.centered_energy_bound hn N u Du hu hN hE x hx h hh
  calc
    _ ≤ fixedMollifierKernelBound n * (h.val ^ n)⁻¹ *
        ∫ z in Metric.ball x h.val, hsNormSq (Du z) :=
      hfinite.sourceMollification_pointwise_hsNormSq_le h hh hx'
    _ ≤ fixedMollifierKernelBound n * (h.val ^ n)⁻¹ *
        ((2 : ℝ) ^ (n - 2) * h.val ^ (n - 2) *
          (dirichletEnergy Du (Metric.ball (0 : Domain n) 1)).toReal) :=
      mul_le_mul_of_nonneg_left hcenter.2
        (mul_nonneg (fixedMollifierKernelBound_pos n).le (inv_nonneg.mpr (pow_pos h.property n).le))
    _ = _ := by
      rw [show fixedMollifierKernelBound n * (h.val ^ n)⁻¹ *
          ((2 : ℝ) ^ (n - 2) * h.val ^ (n - 2) *
            (dirichletEnergy Du (Metric.ball (0 : Domain n) 1)).toReal) =
          (fixedMollifierKernelBound n * (2 : ℝ) ^ (n - 2)) *
            (dirichletEnergy Du (Metric.ball (0 : Domain n) 1)).toReal *
              ((h.val ^ n)⁻¹ * h.val ^ (n - 2)) by ring,
        mollification_energy_scale hn h]

end
end HarmonicMaps

end
