module

public import HarmonicMaps.Analysis.MollificationEnergy
public import HarmonicMaps.Analysis.FiniteEnergySobolev

/-!
# The total gradient energy estimate for the literal source integral

At every point of the half ball the source integral is differentiable. Its
actual gradient is the fixed-kernel average of the displayed weak gradient,
so the Jensen--Fubini estimate applies with multiplicative constant one.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace HarmonicMaps

/-- The classical HS density of the literal source mollification is integrable. -/
theorem MemW12.sourceMollification_integrable_hsNormSq {n q : ℕ}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12 (ballDomain (0 : Domain n) 1) u Du)
    (h : PositiveRadius) (hh : h.val ≤ 1 / 4) :
    IntegrableOn (fun x => hsNormSq (fun i =>
      fderiv ℝ (fun x : Domain n => ∫ y in Metric.ball (0 : Domain n) 1,
        fixedMollifierKernel n y • u (x - h.val • y)) x
          (EuclideanSpace.single i 1)))
      (Metric.ball (0 : Domain n) (1 / 2)) volume := by
  apply (sourceMollifiedGradient_integrable_hsNormSq hu.2.2 h hh).congr_fun _
    measurableSet_ball
  intro x hx
  apply congrArg hsNormSq
  funext i
  exact (hu.sourceMollification_coordinateDerivative h hh
    (Metric.ball_subset_ball (by norm_num : (1 / 2 : ℝ) ≤ 3 / 4) hx) i).symm

/-- The literal source mollification has total gradient energy at most the
input unit-ball HS energy, with exact multiplicative constant one. -/
theorem MemW12.sourceMollification_energy_le {n q : ℕ}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12 (ballDomain (0 : Domain n) 1) u Du)
    (h : PositiveRadius) (hh : h.val ≤ 1 / 4) :
    (∫ x in Metric.ball (0 : Domain n) (1 / 2), hsNormSq (fun i =>
      fderiv ℝ (fun x : Domain n => ∫ y in Metric.ball (0 : Domain n) 1,
        fixedMollifierKernel n y • u (x - h.val • y)) x
          (EuclideanSpace.single i 1))) ≤
      ∫ x in Metric.ball (0 : Domain n) 1, hsNormSq (Du x) := by
  calc
    (∫ x in Metric.ball (0 : Domain n) (1 / 2), hsNormSq (fun i =>
        fderiv ℝ (fun x : Domain n => ∫ y in Metric.ball (0 : Domain n) 1,
          fixedMollifierKernel n y • u (x - h.val • y)) x
            (EuclideanSpace.single i 1))) =
        ∫ x in Metric.ball (0 : Domain n) (1 / 2), hsNormSq (fun i =>
          ∫ y in Metric.ball (0 : Domain n) 1,
            fixedMollifierKernel n y • Du (x - h.val • y) i) := by
      apply setIntegral_congr_fun measurableSet_ball
      intro x hx
      apply congrArg hsNormSq
      funext i
      exact hu.sourceMollification_coordinateDerivative h hh
        (Metric.ball_subset_ball (by norm_num : (1 / 2 : ℝ) ≤ 3 / 4) hx) i
    _ ≤ ∫ x in Metric.ball (0 : Domain n) 1, hsNormSq (Du x) :=
      sourceMollifiedGradient_energy_le hu.2.2 h hh

/-- Compact target values and finite energy supply finite Sobolev data in the
original source setting. -/
theorem MemW12Loc.sourceMollification_energy_le {n q : ℕ}
    (N : CompactSmoothEmbeddedTarget q)
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12Loc (ballDomain (0 : Domain n) 1) u Du)
    (hN : TakesValuesIn N (ballDomain (0 : Domain n) 1) u)
    (hE : dirichletEnergy Du (Metric.ball (0 : Domain n) 1) ≠ ⊤)
    (h : PositiveRadius) (hh : h.val ≤ 1 / 4) :
    (∫ x in Metric.ball (0 : Domain n) (1 / 2), hsNormSq (fun i =>
      fderiv ℝ (fun x : Domain n => ∫ y in Metric.ball (0 : Domain n) 1,
        fixedMollifierKernel n y • u (x - h.val • y)) x
          (EuclideanSpace.single i 1))) ≤
      ∫ x in Metric.ball (0 : Domain n) 1, hsNormSq (Du x) :=
  (hu.memW12_unitBall_of_finiteEnergy N hN hE).sourceMollification_energy_le h hh

end HarmonicMaps
