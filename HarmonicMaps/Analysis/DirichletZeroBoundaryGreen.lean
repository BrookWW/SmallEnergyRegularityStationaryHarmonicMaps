module

public import HarmonicMaps.Analysis.DirichletCompactGreen
public import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# Green pairings with genuine zero-boundary Sobolev tests

The existing graph-closure approximants supply simultaneous map and original
column limits. Continuity of the L2 inner product passes the compact-test
Green identity to those limits and preserves its negative Laplacian sign.
-/

public section

open MeasureTheory Filter Set
open scoped Topology ContDiff BigOperators

namespace HarmonicMaps

private theorem inner_integrable_L2 {n q : ℕ} {μ : Measure (Domain n)}
    {f g : Domain n → Ambient q} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun x => inner ℝ (f x) (g x)) μ := by
  apply (L2.integrable_inner (𝕜 := ℝ) (hf.toLp f) (hg.toLp g)).congr
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hfx hgx
  rw [hfx, hgx]

private theorem integral_inner_toLp {n q : ℕ} {μ : Measure (Domain n)}
    {f g : Domain n → Ambient q} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, inner ℝ (f x) (g x) ∂μ) = inner ℝ (hf.toLp f) (hg.toLp g) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hfx hgx
  rw [hfx, hgx]

private theorem tendsto_integral_inner_L2 {n q : ℕ} {μ : Measure (Domain n)}
    {f : ℕ → Domain n → Ambient q} {u g : Domain n → Ambient q}
    (hf : ∀ k, MemLp (f k) 2 μ) (hu : MemLp u 2 μ) (hg : MemLp g 2 μ)
    (hlim : Tendsto (fun k => eLpNorm (f k - u) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ x, inner ℝ (g x) (f k x) ∂μ) atTop
      (𝓝 (∫ x, inner ℝ (g x) (u x) ∂μ)) := by
  have hLp := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hf u hu).mpr hlim
  have hconst : Tendsto (fun _ : ℕ => hg.toLp g) atTop (𝓝 (hg.toLp g)) :=
    tendsto_const_nhds
  have hinner := hconst.inner (𝕜 := ℝ) hLp
  simp_rw [integral_inner_toLp hg (hf _), integral_inner_toLp hg hu]
  exact hinner

/-- All actual graph-closure tests have integrable signed Green pairings for
the same displayed columns. -/
theorem dirichlet_zeroBoundary_green {n q : ℕ} (R : PositiveRadius)
    (U : Set (Domain n)) (hU : IsOpen U)
    (hclosed : Metric.closedBall (0 : Domain n) R.val ⊆ U)
    (m : Domain n → Ambient q) (hm : ContDiffOn ℝ ∞ m U)
    (f : Domain n → Ambient q) (Df : Domain n → Gradient n q)
    (hf : HasZeroBoundaryValues (ballDomain (0 : Domain n) R.val) f Df) :
    IntegrableOn (fun x => ∑ i : Fin n,
      inner ℝ (fderiv ℝ m x (EuclideanSpace.single i 1)) (Df x i))
      (Metric.ball 0 R.val) volume ∧
    IntegrableOn (fun x => inner ℝ
      (∑ i : Fin n,
        fderiv ℝ (fun z => fderiv ℝ m z (EuclideanSpace.single i 1)) x
          (EuclideanSpace.single i 1)) (f x)) (Metric.ball 0 R.val) volume ∧
    (∫ x in Metric.ball 0 R.val, ∑ i : Fin n,
      inner ℝ (fderiv ℝ m x (EuclideanSpace.single i 1)) (Df x i)) =
      -(∫ x in Metric.ball 0 R.val, inner ℝ
        (∑ i : Fin n,
          fderiv ℝ (fun z => fderiv ℝ m z (EuclideanSpace.single i 1)) x
            (EuclideanSpace.single i 1)) (f x)) := by
  let μ := volume.restrict (Metric.ball (0 : Domain n) R.val)
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  obtain ⟨_, hmD, hmLap, _⟩ := dirichlet_smoothData_closedBall R U hU hclosed m hm
  have hmeasure : μ ≤ volume.restrict (Metric.closedBall (0 : Domain n) R.val) :=
    Measure.restrict_mono_set volume Metric.ball_subset_closedBall
  have hD (i : Fin n) : MemLp (fun x => fderiv ℝ m x (EuclideanSpace.single i 1)) 2 μ :=
    (hmD i).mono_measure hmeasure
  have hLap : MemLp (fun x => ∑ i : Fin n,
      fderiv ℝ (fun z => fderiv ℝ m z (EuclideanSpace.single i 1)) x
        (EuclideanSpace.single i 1)) 2 μ := hmLap.mono_measure hmeasure
  obtain ⟨hW, a, ha, has, hmap, hgrad⟩ := hf
  have haL (k : ℕ) : MemLp (a k) 2 μ :=
    ((ha k).continuous.memLp_top_of_hasCompactSupport (has k).1 μ).mono_exponent (by simp)
  have haD (k : ℕ) (i : Fin n) : MemLp (coordinateDerivative (a k) (ha k) i) 2 μ := by
    have hc := (has k).1.fderiv_apply ℝ (EuclideanSpace.single i 1)
    have hcont : Continuous (coordinateDerivative (a k) (ha k) i) :=
      ((ha k).continuous_fderiv (by simp)).clm_apply continuous_const
    exact (hcont.memLp_top_of_hasCompactSupport hc μ).mono_exponent (by simp)
  have hleft (i : Fin n) : Integrable (fun x =>
      inner ℝ (fderiv ℝ m x (EuclideanSpace.single i 1)) (Df x i)) μ :=
    inner_integrable_L2 (hD i) (hW.2.2 i)
  have hleftLim : Tendsto (fun k => ∑ i : Fin n,
      ∫ x, inner ℝ (fderiv ℝ m x (EuclideanSpace.single i 1))
        (coordinateDerivative (a k) (ha k) i x) ∂μ) atTop
      (𝓝 (∑ i : Fin n, ∫ x, inner ℝ
        (fderiv ℝ m x (EuclideanSpace.single i 1)) (Df x i) ∂μ)) :=
    tendsto_finsetSum Finset.univ (fun i _ =>
      tendsto_integral_inner_L2 (fun k => haD k i) (hW.2.2 i) (hD i) (hgrad i))
  have hrightLim := tendsto_integral_inner_L2 haL hW.2.1 hLap hmap
  have hseq (k : ℕ) : (∑ i : Fin n,
      ∫ x, inner ℝ (fderiv ℝ m x (EuclideanSpace.single i 1))
        (coordinateDerivative (a k) (ha k) i x) ∂μ) =
      -(∫ x, inner ℝ (∑ i : Fin n,
        fderiv ℝ (fun z => fderiv ℝ m z (EuclideanSpace.single i 1)) x
          (EuclideanSpace.single i 1)) (a k x) ∂μ) := by
    rw [← integral_finsetSum _ (fun i _ => inner_integrable_L2 (hD i) (haD k i))]
    exact (dirichlet_compactTest_green R U hU hclosed m hm (a k) (ha k)
      (has k).1 (has k).2).2.2
  refine ⟨integrable_finsetSum Finset.univ (fun i _ => hleft i),
    inner_integrable_L2 hLap hW.2.1, ?_⟩
  rw [integral_finsetSum _ (fun i _ => hleft i)]
  exact tendsto_nhds_unique hleftLim (hrightLim.neg.congr' (Eventually.of_forall
    (fun k => (hseq k).symm)))

/-- The same signed identity uses the native Euclidean Laplacian. -/
theorem dirichlet_zeroBoundary_green_laplacian {n q : ℕ} (R : PositiveRadius)
    (U : Set (Domain n)) (hU : IsOpen U)
    (hclosed : Metric.closedBall (0 : Domain n) R.val ⊆ U)
    (m : Domain n → Ambient q) (hm : ContDiffOn ℝ ∞ m U)
    (f : Domain n → Ambient q) (Df : Domain n → Gradient n q)
    (hf : HasZeroBoundaryValues (ballDomain (0 : Domain n) R.val) f Df) :
    IntegrableOn (fun x => ∑ i : Fin n,
      inner ℝ (fderiv ℝ m x (EuclideanSpace.single i 1)) (Df x i))
      (Metric.ball 0 R.val) volume ∧
    IntegrableOn (fun x => inner ℝ (Laplacian.laplacian m x) (f x))
      (Metric.ball 0 R.val) volume ∧
    (∫ x in Metric.ball 0 R.val, ∑ i : Fin n,
      inner ℝ (fderiv ℝ m x (EuclideanSpace.single i 1)) (Df x i)) =
      -(∫ x in Metric.ball 0 R.val, inner ℝ (Laplacian.laplacian m x) (f x)) := by
  obtain ⟨hleft, hright, hsign⟩ := dirichlet_zeroBoundary_green R U hU hclosed m hm f Df hf
  have hpair (x : Domain n) (hx : x ∈ Metric.ball 0 R.val) :
      inner ℝ (Laplacian.laplacian m x) (f x) = inner ℝ
        (∑ i : Fin n,
          fderiv ℝ (fun z => fderiv ℝ m z (EuclideanSpace.single i 1)) x
            (EuclideanSpace.single i 1)) (f x) := by
    rw [dirichlet_smoothData_laplacian R U hU hclosed m hm x
      (Metric.ball_subset_closedBall hx)]
  refine ⟨hleft, hright.congr_fun (fun x hx => (hpair x hx).symm) measurableSet_ball, ?_⟩
  rw [setIntegral_congr_fun measurableSet_ball hpair]
  exact hsign

end HarmonicMaps

end
