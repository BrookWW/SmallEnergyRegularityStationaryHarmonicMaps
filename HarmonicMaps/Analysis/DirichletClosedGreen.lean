module

public import HarmonicMaps.Analysis.DirichletZeroBoundaryGreen
import Mathlib.Analysis.Calculus.FDeriv.Congr

/-!
# Green identity for data smooth within a closed ball

The closed-ball derivatives provide finite native Laplacian and interior
column data. Compact tests lie in smaller interior balls. Their signed Green
identity passes through the actual W0 graph closure to every original test
column.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology BigOperators

namespace HarmonicMaps

private theorem closedGreen_uniqueDiff {n : ℕ} (R : PositiveRadius) :
    UniqueDiffOn ℝ (Metric.closedBall (0 : Domain n) R.val) :=
  uniqueDiffOn_convex (convex_closedBall _ _)
    ⟨0, Metric.ball_subset_interior_closedBall (Metric.mem_ball_self R.property)⟩

private theorem closedGreen_continuous_memLp {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] {f : Domain n → E} {R : ℝ}
    (hf : ContinuousOn f (Metric.closedBall (0 : Domain n) R)) :
    MemLp f 2 (volume.restrict (Metric.closedBall (0 : Domain n) R)) := by
  let K := Metric.closedBall (0 : Domain n) R
  have hK : IsCompact K := isCompact_closedBall _ _
  letI : IsFiniteMeasure (volume.restrict K) :=
    isFiniteMeasure_restrict.mpr hK.measure_ne_top
  obtain ⟨C, hC⟩ := (hK.image_of_continuousOn hf).isBounded.exists_norm_le
  apply MemLp.of_bound
    (hf.aestronglyMeasurable_of_subset_isCompact hK hK.measurableSet Subset.rfl) C
  filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
  exact hC _ (mem_image_of_mem f hx)


private theorem closedGreen_smaller_support {n q : ℕ} (R : PositiveRadius)
    (φ : Domain n → Ambient q) (hcφ : HasCompactSupport φ)
    (hsφ : tsupport φ ⊆ Metric.ball (0 : Domain n) R.val) :
    ∃ r : PositiveRadius, r.val < R.val ∧ tsupport φ ⊆ Metric.ball (0 : Domain n) r.val := by
  by_cases hne : (tsupport φ).Nonempty
  · obtain ⟨y, hy, hmax⟩ := hcφ.exists_isMaxOn hne continuous_norm.continuousOn
    have hyR : ‖y‖ < R.val := by
      simpa only [Metric.mem_ball, dist_zero_right] using hsφ hy
    let r : ℝ := (‖y‖ + R.val) / 2
    have hr : 0 < r := by dsimp only [r]; linarith only [norm_nonneg y, R.property]
    refine ⟨⟨r, hr⟩, ?_, ?_⟩
    · dsimp only [r]
      linarith only [hyR]
    · intro x hx
      rw [Metric.mem_ball, dist_zero_right]
      have hxy : ‖x‖ ≤ ‖y‖ := hmax hx
      dsimp only [r]
      linarith only [hxy, hyR]
  · refine ⟨⟨R.val / 2, half_pos R.property⟩, half_lt_self R.property, ?_⟩
    intro x hx
    exact (hne ⟨x, hx⟩).elim


private theorem closedGreen_inner_integrable_L2 {n q : ℕ} {μ : Measure (Domain n)}
    {f g : Domain n → Ambient q} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun x => inner ℝ (f x) (g x)) μ := by
  apply (L2.integrable_inner (𝕜 := ℝ) (hf.toLp f) (hg.toLp g)).congr
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hfx hgx
  rw [hfx, hgx]

private theorem closedGreen_integral_inner_toLp {n q : ℕ} {μ : Measure (Domain n)}
    {f g : Domain n → Ambient q} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, inner ℝ (f x) (g x) ∂μ) = inner ℝ (hf.toLp f) (hg.toLp g) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hfx hgx
  rw [hfx, hgx]

private theorem closedGreen_tendsto_integral_inner_L2 {n q : ℕ} {μ : Measure (Domain n)}
    {f : ℕ → Domain n → Ambient q} {u g : Domain n → Ambient q}
    (hf : ∀ k, MemLp (f k) 2 μ) (hu : MemLp u 2 μ) (hg : MemLp g 2 μ)
    (hlim : Tendsto (fun k => eLpNorm (f k - u) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ x, inner ℝ (g x) (f k x) ∂μ) atTop
      (𝓝 (∫ x, inner ℝ (g x) (u x) ∂μ)) := by
  have hLp := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hf u hu).mpr hlim
  have hconst : Tendsto (fun _ : ℕ => hg.toLp g) atTop (𝓝 (hg.toLp g)) :=
    tendsto_const_nhds
  have hinner := hconst.inner (𝕜 := ℝ) hLp
  simp_rw [closedGreen_integral_inner_toLp hg (hf _), closedGreen_integral_inner_toLp hg hu]
  exact hinner

private theorem closedGreen_classical_data {n q : ℕ} (R : PositiveRadius)
    (m : Domain n → Ambient q)
    (hm : ContDiffOn ℝ ∞ m (Metric.closedBall (0 : Domain n) R.val)) :
    (∀ i : Fin n, MemLp (fun x => fderiv ℝ m x (EuclideanSpace.single i 1))
      2 (volume.restrict (Metric.ball 0 R.val))) ∧
    MemLp (fun x => Laplacian.laplacian m x) 2
      (volume.restrict (Metric.ball 0 R.val)) := by
  let K := Metric.closedBall (0 : Domain n) R.val
  let B := Metric.ball (0 : Domain n) R.val
  have hUnique : UniqueDiffOn ℝ K := closedGreen_uniqueDiff R
  have hDm : ContDiffOn ℝ ∞ (fderivWithin ℝ m K) K :=
    hm.fderivWithin hUnique (by simp)
  have hcolumn (i : Fin n) : ContDiffOn ℝ ∞
      (fun x => fderivWithin ℝ m K x (EuclideanSpace.single i 1)) K :=
    hDm.clm_apply contDiffOn_const
  have hSecond (i : Fin n) : ContinuousOn (fun x =>
      fderivWithin ℝ (fun z => fderivWithin ℝ m K z (EuclideanSpace.single i 1)) K x
        (EuclideanSpace.single i 1)) K :=
    ((hcolumn i).continuousOn_fderivWithin hUnique (by simp)).clm_apply continuousOn_const
  have hKnhds (x : Domain n) (hx : x ∈ B) : K ∈ 𝓝 x :=
    mem_of_superset (Metric.isOpen_ball.mem_nhds hx) Metric.ball_subset_closedBall
  have hMeasure : volume.restrict B ≤ volume.restrict K :=
    Measure.restrict_mono_set volume Metric.ball_subset_closedBall
  have hFirst (i : Fin n) : MemLp (fun x => fderiv ℝ m x (EuclideanSpace.single i 1))
      2 (volume.restrict B) := by
    apply ((closedGreen_continuous_memLp (hcolumn i).continuousOn).mono_measure hMeasure).ae_eq
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
    rw [fderivWithin_of_mem_nhds (hKnhds x hx)]
  have hLap : MemLp (fun x => ∑ i : Fin n,
      fderivWithin ℝ (fun z => fderivWithin ℝ m K z (EuclideanSpace.single i 1)) K x
        (EuclideanSpace.single i 1)) 2 (volume.restrict B) :=
    (closedGreen_continuous_memLp
      (continuousOn_finsetSum Finset.univ (fun i _ => hSecond i))).mono_measure hMeasure
  refine ⟨hFirst, hLap.ae_eq ?_⟩
  filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
  have hmOpen : ContDiffOn ℝ ∞ m B := hm.mono Metric.ball_subset_closedBall
  have hDOpen : ContDiffOn ℝ ∞ (fderiv ℝ m) B :=
    hmOpen.fderiv_of_isOpen Metric.isOpen_ball (by simp)
  have hDiff : DifferentiableAt ℝ (fderiv ℝ m) x :=
    (hDOpen.contDiffAt
      (Metric.isOpen_ball.mem_nhds hx)).differentiableAt (by simp)
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis m
    (EuclideanSpace.basisFun (Fin n) ℝ)]
  apply Finset.sum_congr rfl
  intro i _
  have heq : (fun z => fderivWithin ℝ m K z (EuclideanSpace.single i 1)) =ᶠ[𝓝 x]
      (fun z => fderiv ℝ m z (EuclideanSpace.single i 1)) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hx] with z hz
    rw [fderivWithin_of_mem_nhds (hKnhds z hz)]
  rw [fderivWithin_of_mem_nhds (hKnhds x hx), heq.fderiv_eq,
    EuclideanSpace.basisFun_apply, iteratedFDeriv_two_apply,
    fderiv_clm_apply hDiff (differentiableAt_const _)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, fderiv_const_apply,
    ContinuousLinearMap.comp_zero, zero_add, ContinuousLinearMap.flip_apply]

private theorem closedGreen_compactTest {n q : ℕ} (R : PositiveRadius)
    (m : Domain n → Ambient q)
    (hm : ContDiffOn ℝ ∞ m (Metric.closedBall (0 : Domain n) R.val))
    (φ : Domain n → Ambient q) (hφ : ContDiff ℝ ∞ φ)
    (hcφ : HasCompactSupport φ) (hsφ : tsupport φ ⊆ Metric.ball (0 : Domain n) R.val) :
    (∫ x in Metric.ball (0 : Domain n) R.val, ∑ i : Fin n,
      inner ℝ (fderiv ℝ m x (EuclideanSpace.single i 1))
        (coordinateDerivative φ hφ i x)) =
      -(∫ x in Metric.ball (0 : Domain n) R.val,
        inner ℝ (Laplacian.laplacian m x) (φ x)) := by
  obtain ⟨r, hrR, hsr⟩ := closedGreen_smaller_support R φ hcφ hsφ
  have hclosed : Metric.closedBall (0 : Domain n) r.val ⊆ Metric.ball (0 : Domain n) R.val :=
    Metric.closedBall_subset_ball hrR
  have hmOpen := hm.mono Metric.ball_subset_closedBall
  obtain ⟨_, _, hGreen⟩ := dirichlet_compactTest_green r
    (Metric.ball (0 : Domain n) R.val) Metric.isOpen_ball hclosed m hmOpen φ hφ hcφ hsr
  have hRight : (∫ x in Metric.ball (0 : Domain n) r.val, inner ℝ
      (∑ i : Fin n,
        fderiv ℝ (fun z => fderiv ℝ m z (EuclideanSpace.single i 1)) x
          (EuclideanSpace.single i 1)) (φ x)) =
      ∫ x in Metric.ball (0 : Domain n) r.val, inner ℝ (Laplacian.laplacian m x) (φ x) :=
    setIntegral_congr_fun Metric.isOpen_ball.measurableSet (fun x hx => by
      rw [dirichlet_smoothData_laplacian r (Metric.ball (0 : Domain n) R.val)
        Metric.isOpen_ball hclosed m hmOpen x (Metric.ball_subset_closedBall hx)])
  have hZero (x : Domain n) (hx : x ∉ Metric.ball (0 : Domain n) r.val) (i : Fin n) :
      coordinateDerivative φ hφ i x = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    exact hx (hsr (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1) hmem))
  have hLeftEq (s : ℝ) (hrs : r.val ≤ s) :
      (∫ x in Metric.ball (0 : Domain n) s, ∑ i : Fin n,
        inner ℝ (fderiv ℝ m x (EuclideanSpace.single i 1))
          (coordinateDerivative φ hφ i x)) =
        ∫ x : Domain n, ∑ i : Fin n, inner ℝ
          (fderiv ℝ m x (EuclideanSpace.single i 1)) (coordinateDerivative φ hφ i x) :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      apply Finset.sum_eq_zero
      intro i _
      rw [hZero x (fun hy => hx (Metric.ball_subset_ball hrs hy)) i, inner_zero_right])
  have hRightEq (s : ℝ) (hrs : r.val ≤ s) :
      (∫ x in Metric.ball (0 : Domain n) s, inner ℝ (Laplacian.laplacian m x) (φ x)) =
        ∫ x : Domain n, inner ℝ (Laplacian.laplacian m x) (φ x) :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      have hz : φ x = 0 := image_eq_zero_of_notMem_tsupport
        (fun hy => hx (Metric.ball_subset_ball hrs (hsr hy)))
      rw [hz, inner_zero_right])
  rw [hRight, hLeftEq r.val le_rfl, hRightEq r.val le_rfl] at hGreen
  rw [hLeftEq R.val hrR.le, hRightEq R.val hrR.le]
  exact hGreen

/-- Smoothness within the closed ball produces integrable native Green pairings
for every genuine zero-boundary Sobolev test, with the original columns. -/
theorem closed_dirichlet_zeroBoundary_green_laplacian {n q : ℕ} (R : PositiveRadius)
    (m : Domain n → Ambient q)
    (hm : ContDiffOn ℝ ∞ m (Metric.closedBall (0 : Domain n) R.val))
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
  let μ := volume.restrict (Metric.ball (0 : Domain n) R.val)
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  obtain ⟨hD, hLap⟩ := closedGreen_classical_data R m hm
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
    closedGreen_inner_integrable_L2 (hD i) (hW.2.2 i)
  have hleftLim : Tendsto (fun k => ∑ i : Fin n,
      ∫ x, inner ℝ (fderiv ℝ m x (EuclideanSpace.single i 1))
        (coordinateDerivative (a k) (ha k) i x) ∂μ) atTop
      (𝓝 (∑ i : Fin n, ∫ x, inner ℝ
        (fderiv ℝ m x (EuclideanSpace.single i 1)) (Df x i) ∂μ)) :=
    tendsto_finsetSum Finset.univ (fun i _ =>
      closedGreen_tendsto_integral_inner_L2 (fun k => haD k i) (hW.2.2 i) (hD i) (hgrad i))
  have hrightLim := closedGreen_tendsto_integral_inner_L2 haL hW.2.1 hLap hmap
  have hseq (k : ℕ) : (∑ i : Fin n,
      ∫ x, inner ℝ (fderiv ℝ m x (EuclideanSpace.single i 1))
        (coordinateDerivative (a k) (ha k) i x) ∂μ) =
      -(∫ x, inner ℝ (Laplacian.laplacian m x) (a k x) ∂μ) := by
    rw [← integral_finsetSum _ (fun i _ => closedGreen_inner_integrable_L2 (hD i) (haD k i))]
    exact closedGreen_compactTest R m hm (a k) (ha k) (has k).1 (has k).2
  refine ⟨integrable_finsetSum Finset.univ (fun i _ => hleft i),
    closedGreen_inner_integrable_L2 hLap hW.2.1, ?_⟩
  rw [integral_finsetSum _ (fun i _ => hleft i)]
  exact tendsto_nhds_unique hleftLim (hrightLim.neg.congr' (Eventually.of_forall
    (fun k => (hseq k).symm)))

end HarmonicMaps

end
