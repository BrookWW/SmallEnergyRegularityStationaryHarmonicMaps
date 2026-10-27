module

public import HarmonicMaps.Analysis.MollificationChangeVariables
public import HarmonicMaps.Analysis.FiniteEnergySobolev

/-!
# Fixed-scale interior mollification

The source unit-ball integral is defined on the proved interior neighborhood
`B(0,3/4)`. Its actual integrability and equality to the smooth zero-extension
convolution are established before the public definition. The source-facing
application obtains finite Sobolev data from the existing finite-energy theorem.
-/

@[expose] public section

open MeasureTheory Set
open scoped ContDiff

namespace HarmonicMaps

/-- Finite unit-ball Sobolev data give the L1 input needed for convolution. -/
theorem MemW12.integrable_unitBall {n q : ℕ} {u : Domain n → Ambient q}
    {Du : Domain n → Gradient n q}
    (hu : MemW12 (ballDomain (0 : Domain n) 1) u Du) :
    IntegrableOn u (Metric.ball (0 : Domain n) 1) := by
  letI : IsFiniteMeasure (volume.restrict (Metric.ball (0 : Domain n) 1)) :=
    isFiniteMeasure_restrict.mpr measure_ball_ne_top
  have hL2 : MemLp u 2 (volume.restrict (Metric.ball (0 : Domain n) 1)) := hu.2.1
  exact hL2.integrable (by norm_num)

noncomputable section

/-- The literal source integral on the whole proved interior carrier.
Every allowed input has an integrable source integrand. Exterior values of
the original map are never sampled on this carrier. -/
def interiorMollification {n q : ℕ} (u : Domain n → Ambient q)
    (_hu : IntegrableOn u (Metric.ball (0 : Domain n) 1)) (h : PositiveRadius)
    (_hh : h.val ≤ 1 / 4)
    (x : {x : Domain n // x ∈ Metric.ball (0 : Domain n) (3 / 4)}) : Ambient q :=
  ∫ y in Metric.ball (0 : Domain n) 1,
    fixedMollifierKernel n y • u (x.val - h.val • y)

/-- The defining equation retains the source's integration variable and scale. -/
theorem interiorMollification_eq_integral {n q : ℕ} (u : Domain n → Ambient q)
    (hu : IntegrableOn u (Metric.ball (0 : Domain n) 1)) (h : PositiveRadius)
    (hh : h.val ≤ 1 / 4)
    (x : {x : Domain n // x ∈ Metric.ball (0 : Domain n) (3 / 4)}) :
    interiorMollification u hu h hh x =
      ∫ y in Metric.ball (0 : Domain n) 1,
        fixedMollifierKernel n y • u (x.val - h.val • y) := rfl

/-- The public source definition is backed by genuine integrability. -/
theorem interiorMollification_integrable {n q : ℕ} (u : Domain n → Ambient q)
    (hu : IntegrableOn u (Metric.ball (0 : Domain n) 1)) (h : PositiveRadius)
    (hh : h.val ≤ 1 / 4)
    (x : {x : Domain n // x ∈ Metric.ball (0 : Domain n) (3 / 4)}) :
    IntegrableOn (fun y => fixedMollifierKernel n y • u (x.val - h.val • y))
      (Metric.ball (0 : Domain n) 1) :=
  sourceMollification_integrableOn u hu h hh x.val x.property

/-- The original integral agrees with the global auxiliary on the interior carrier. -/
theorem interiorMollification_eq_zeroExtended {n q : ℕ} (u : Domain n → Ambient q)
    (hu : IntegrableOn u (Metric.ball (0 : Domain n) 1)) (h : PositiveRadius)
    (hh : h.val ≤ 1 / 4)
    (x : {x : Domain n // x ∈ Metric.ball (0 : Domain n) (3 / 4)}) :
    interiorMollification u hu h hh x = zeroExtendedMollification u hu h x.val :=
  sourceMollification_eq_zeroExtended u hu h hh x.val x.property

/-- Smoothness of the literal source integral on its proved open neighborhood.
The predicate concerns only points in this ball; no exterior source value is claimed. -/
theorem sourceMollification_contDiffOn {n q : ℕ} (u : Domain n → Ambient q)
    (hu : IntegrableOn u (Metric.ball (0 : Domain n) 1)) (h : PositiveRadius)
    (hh : h.val ≤ 1 / 4) :
    ContDiffOn ℝ ∞ (fun x : Domain n => ∫ y in Metric.ball (0 : Domain n) 1,
      fixedMollifierKernel n y • u (x - h.val • y))
      (Metric.ball (0 : Domain n) (3 / 4)) := by
  apply (zeroExtendedMollification_contDiff u hu h).contDiffOn.congr
  intro x hx
  exact sourceMollification_eq_zeroExtended u hu h hh x hx

/-- The source partial map has the explicitly constructed smooth representative. -/
theorem interiorMollification_smoothRepresentative {n q : ℕ} (u : Domain n → Ambient q)
    (hu : IntegrableOn u (Metric.ball (0 : Domain n) 1)) (h : PositiveRadius)
    (hh : h.val ≤ 1 / 4) :
    ∃ M : Domain n → Ambient q, ContDiff ℝ ∞ M ∧
      ∀ x : {x : Domain n // x ∈ Metric.ball (0 : Domain n) (3 / 4)},
        M x.val = interiorMollification u hu h hh x :=
  ⟨zeroExtendedMollification u hu h, zeroExtendedMollification_contDiff u hu h,
    fun x => (interiorMollification_eq_zeroExtended u hu h hh x).symm⟩

/-- The chosen open interior contains the closed source half-unit ball. -/
theorem mollification_closedHalfBall_subset_neighborhood (n : ℕ) :
    Metric.closedBall (0 : Domain n) (1 / 2) ⊆ Metric.ball (0 : Domain n) (3 / 4) :=
  Metric.closedBall_subset_ball (by norm_num : (1 / 2 : ℝ) < 3 / 4)

/-- Source local Sobolev, compact-target and finite-energy data supply the
literal integrability and neighborhood smoothness, through the existing
finite Sobolev theorem for the same map and displayed gradient. -/
theorem MemW12Loc.interiorMollification_spec {n q : ℕ} (N : CompactSmoothEmbeddedTarget q)
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12Loc (ballDomain (0 : Domain n) 1) u Du)
    (hN : TakesValuesIn N (ballDomain (0 : Domain n) 1) u)
    (hE : dirichletEnergy Du (Metric.ball (0 : Domain n) 1) ≠ ⊤)
    (h : PositiveRadius) (hh : h.val ≤ 1 / 4) :
    (∀ x ∈ Metric.ball (0 : Domain n) (3 / 4), ∀ y ∈ Metric.ball (0 : Domain n) 1,
      x - h.val • y ∈ Metric.ball (0 : Domain n) 1) ∧
    (∀ x ∈ Metric.ball (0 : Domain n) (3 / 4),
      IntegrableOn (fun y => fixedMollifierKernel n y • u (x - h.val • y))
        (Metric.ball (0 : Domain n) 1)) ∧
    ContDiffOn ℝ ∞ (fun x : Domain n => ∫ y in Metric.ball (0 : Domain n) 1,
      fixedMollifierKernel n y • u (x - h.val • y))
      (Metric.ball (0 : Domain n) (3 / 4)) ∧
    Metric.closedBall (0 : Domain n) (1 / 2) ⊆ Metric.ball (0 : Domain n) (3 / 4) ∧
    (∃ M : Domain n → Ambient q, ContDiff ℝ ∞ M ∧
      ∀ x ∈ Metric.ball (0 : Domain n) (3 / 4),
        M x = ∫ y in Metric.ball (0 : Domain n) 1,
          fixedMollifierKernel n y • u (x - h.val • y)) := by
  have hW : MemW12 (ballDomain (0 : Domain n) 1) u Du :=
    hu.memW12_unitBall_of_finiteEnergy N hN hE
  have hInt := hW.integrable_unitBall
  refine ⟨(fun x hx y hy => mollification_sampling_mem_unitBall h hh hx hy),
    (fun x hx => sourceMollification_integrableOn u hInt h hh x hx),
    sourceMollification_contDiffOn u hInt h hh,
    mollification_closedHalfBall_subset_neighborhood n,
    zeroExtendedMollification u hInt h, zeroExtendedMollification_contDiff u hInt h, ?_⟩
  intro x hx
  exact (sourceMollification_eq_zeroExtended u hInt h hh x hx).symm

end
end HarmonicMaps
