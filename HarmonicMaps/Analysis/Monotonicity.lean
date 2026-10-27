module

public import HarmonicMaps.Analysis.NormalizedEnergyCalculus
public import HarmonicMaps.Analysis.RadiusBoundaryIdentity
public import HarmonicMaps.Analysis.AnnularPolarIntegral

/-!
# Exact monotonicity for locally energy-minimizing maps

The actual radius boundary identity and absolute continuity give the exact
normalized-energy increment. The polar annulus formula identifies the radial
term with the original same-gradient spatial density. Every positive pair
of radii up to and including the outer radius is covered.
-/

public section

open MeasureTheory Set
open scoped BigOperators

namespace HarmonicMaps

/-- The exact monotonicity increment and order inequality for a local
minimizer, at arbitrary center and all `0 < s < r ≤ R`. The extended energies
are finite by the original Sobolev assumptions, so their real values retain
the exact source energy normalization. -/
theorem IsLocallyEnergyMinimizing.monotonicity {n q : ℕ} (hn : 2 ≤ n)
    {Ω : OpenDomain n} {N : CompactSmoothEmbeddedTarget q}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hmin : IsLocallyEnergyMinimizing N Ω u Du) (hu : MemW12Loc Ω u Du)
    (hN : TakesValuesIn N Ω u) {a : Domain n} {R : ℝ} (hR : 0 < R)
    (hball : Metric.closedBall a R ⊆ Ω.val) {s r : ℝ}
    (hs : 0 < s) (hsr : s < r) (hrR : r ≤ R) :
    IntegrableOn (fun x => ‖x - a‖ ^ (2 - (n : ℤ)) *
      ‖‖x - a‖⁻¹ • ∑ i : Fin n, (x - a) i • Du x i‖ ^ 2)
      (Metric.ball a r \ Metric.ball a s) volume ∧
    ((normalizedEnergy Du a ⟨r, hs.trans hsr⟩).toReal -
      (normalizedEnergy Du a ⟨s, hs⟩).toReal =
      2 * ∫ x in Metric.ball a r \ Metric.ball a s, ‖x - a‖ ^ (2 - (n : ℤ)) *
        ‖‖x - a‖⁻¹ • ∑ i : Fin n, (x - a) i • Du x i‖ ^ 2) ∧
    normalizedEnergy Du a ⟨s, hs⟩ ≤ normalizedEnergy Du a ⟨r, hs.trans hsr⟩ := by
  have hn0 : 0 < n := lt_of_lt_of_le (by decide : 0 < 2) hn
  let e := fun t : ℝ => ∫ x in Metric.ball a t, hsNormSq (Du x)
  let p := fun t : ℝ => t ^ (n - 1) *
    ∫ θ : Metric.sphere (0 : Domain n) 1, hsNormSq (Du (a + t • θ.val))
      ∂(volume : Measure (Domain n)).toSphere
  let g := fun t : ℝ => t ^ (n - 1) *
    ∫ θ : Metric.sphere (0 : Domain n) 1,
      ‖‖(a + t • θ.val) - a‖⁻¹ • ∑ i : Fin n,
        ((a + t • θ.val) - a) i • Du (a + t • θ.val) i‖ ^ 2
      ∂(volume : Measure (Domain n)).toSphere
  have hb := hmin.radius_boundary_identity hn hu hN hR hball
  change AbsolutelyContinuousOnInterval e 0 R ∧
    ∀ᵐ t : ℝ, t ∈ Ioo 0 R →
      HasDerivAt e (p t) t ∧ ((n : ℝ) - 2) * e t - t * p t = -2 * t * g t at hb
  have hae : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) R),
      HasDerivAt e (p t) t ∧ ((n : ℝ) - 2) * e t - t * p t = -2 * t * g t :=
    (ae_restrict_iff' measurableSet_Ioo).mpr hb.2
  have hg : IntegrableOn g (Ioo (0 : ℝ) R) volume :=
    (hu.integrable_polar_energy_densities hn0 hball).2
  have hcalc := normalized_energy_increment n hs hsr hrR hb.1
    (hae.mono (fun _ h => h.1)) (hae.mono (fun _ h => h.2)) hg
  have hradial : IntegrableOn (fun x =>
      ‖‖x - a‖⁻¹ • ∑ i : Fin n, (x - a) i • Du x i‖ ^ 2)
      (Metric.ball a r \ Metric.ball a s) volume :=
    (hu.integrable_radial_columns_ball hball).mono_set
      (sdiff_subset.trans (Metric.ball_subset_ball hrR))
  have hannulus := integral_weighted_annulus_eq_polar hn0 hs hsr.le hradial
    (contDiffOn_zpow_positive_interval (2 - (n : ℤ)) hs).continuousOn
  have hsrBall : Metric.closedBall a s ⊆ Ω.val :=
    (Metric.closedBall_subset_closedBall (hsr.le.trans hrR)).trans hball
  have hrBall : Metric.closedBall a r ⊆ Ω.val :=
    (Metric.closedBall_subset_closedBall hrR).trans hball
  have hsI := hu.integrable_hsNormSq_ball hsrBall
  have hrI := hu.integrable_hsNormSq_ball hrBall
  have hincrement : (normalizedEnergy Du a ⟨r, hs.trans hsr⟩).toReal -
      (normalizedEnergy Du a ⟨s, hs⟩).toReal =
      2 * ∫ x in Metric.ball a r \ Metric.ball a s, ‖x - a‖ ^ (2 - (n : ℤ)) *
        ‖‖x - a‖⁻¹ • ∑ i : Fin n, (x - a) i • Du x i‖ ^ 2 := by
    rw [normalizedEnergy_toReal hrI, normalizedEnergy_toReal hsI]
    change r ^ (2 - (n : ℤ)) * e r - s ^ (2 - (n : ℤ)) * e s = _
    rw [hcalc.2.2.2]
    exact congrArg (fun z : ℝ => 2 * z) hannulus.2.symm
  refine ⟨hannulus.1, hincrement, ?_⟩
  have hsfinite := normalizedEnergy_ne_top_of_dirichletEnergy_ne_top
    (r := (⟨s, hs⟩ : PositiveRadius)) (hu.dirichletEnergy_ne_top_ball hsrBall)
  have hrfinite := normalizedEnergy_ne_top_of_dirichletEnergy_ne_top
    (r := (⟨r, hs.trans hsr⟩ : PositiveRadius)) (hu.dirichletEnergy_ne_top_ball hrBall)
  apply (ENNReal.toReal_le_toReal hsfinite hrfinite).mp
  have hnonneg : 0 ≤ 2 * ∫ x in Metric.ball a r \ Metric.ball a s,
      ‖x - a‖ ^ (2 - (n : ℤ)) *
        ‖‖x - a‖⁻¹ • ∑ i : Fin n, (x - a) i • Du x i‖ ^ 2 :=
    mul_nonneg (by norm_num) (integral_nonneg fun x =>
      mul_nonneg (zpow_nonneg (norm_nonneg _) _) (sq_nonneg _))
  linarith only [hincrement, hnonneg]

/-- Normalized energy is nondecreasing on the entire positive radius range,
including its outer endpoint, for the actual local minimizer. -/
theorem IsLocallyEnergyMinimizing.normalizedEnergy_monotoneOn {n q : ℕ} (hn : 2 ≤ n)
    {Ω : OpenDomain n} {N : CompactSmoothEmbeddedTarget q}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hmin : IsLocallyEnergyMinimizing N Ω u Du) (hu : MemW12Loc Ω u Du)
    (hN : TakesValuesIn N Ω u) {a : Domain n} {R : ℝ} (hR : 0 < R)
    (hball : Metric.closedBall a R ⊆ Ω.val) :
    MonotoneOn (fun t : PositiveRadius => normalizedEnergy Du a t) {t | t.val ≤ R} := by
  intro s _hsR r hrR hsr
  by_cases heq : s = r
  · rw [heq]
  · have hlt : s.val < r.val := lt_of_le_of_ne hsr (fun h => heq (Subtype.ext h))
    exact (hmin.monotonicity hn hu hN hR hball s.property hlt hrR).2.2

end HarmonicMaps
