module

public import HarmonicMaps.Analysis.DirichletSmoothData
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Signed Green pairings for compact smooth tests

Actual local smooth data give integrable classical columns on the source
ball. Compact smooth tests produce a Green pairing with the negative
Laplacian sign. No harmonic solution or zero-boundary difference is selected.
-/

public section

open MeasureTheory Set
open scoped ContDiff BigOperators

namespace HarmonicMaps

private theorem inner_integrable_L2 {n q : ℕ} {μ : Measure (Domain n)}
    {f g : Domain n → Ambient q} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun x => inner ℝ (f x) (g x)) μ := by
  apply (L2.integrable_inner (𝕜 := ℝ) (hf.toLp f) (hg.toLp g)).congr
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hfx hgx
  rw [hfx, hgx]

private theorem compact_inner_integrable {n q : ℕ} {R : ℝ}
    {f g : Domain n → Ambient q}
    (hf : ContinuousOn f (Metric.closedBall 0 R))
    (hg : ContinuousOn g (Metric.closedBall 0 R))
    (hs : Function.support g ⊆ Metric.ball 0 R) :
    Integrable (fun x => inner ℝ (f x) (g x)) volume := by
  apply (integrableOn_iff_integrable_of_support_subset ?_).mp
    ((hf.inner hg).integrableOn_compact (isCompact_closedBall _ _))
  intro x hx
  apply Metric.ball_subset_closedBall
  apply hs
  by_contra hzero
  exact hx (by simp only [Function.notMem_support.mp hzero, inner_zero_right])

/-- The actual integrable compact-test Green pairing has the negative sign. -/
theorem dirichlet_compactTest_green {n q : ℕ} (R : PositiveRadius)
    (U : Set (Domain n)) (hU : IsOpen U)
    (hclosed : Metric.closedBall (0 : Domain n) R.val ⊆ U)
    (m : Domain n → Ambient q) (hm : ContDiffOn ℝ ∞ m U)
    (φ : Domain n → Ambient q) (hφ : ContDiff ℝ ∞ φ)
    (hcφ : HasCompactSupport φ) (hsφ : tsupport φ ⊆ Metric.ball 0 R.val) :
    IntegrableOn (fun x => ∑ i : Fin n,
      inner ℝ (fderiv ℝ m x (EuclideanSpace.single i 1))
        (coordinateDerivative φ hφ i x)) (Metric.ball 0 R.val) volume ∧
    IntegrableOn (fun x => inner ℝ
      (∑ i : Fin n,
        fderiv ℝ (fun z => fderiv ℝ m z (EuclideanSpace.single i 1)) x
          (EuclideanSpace.single i 1)) (φ x)) (Metric.ball 0 R.val) volume ∧
    (∫ x in Metric.ball 0 R.val, ∑ i : Fin n,
      inner ℝ (fderiv ℝ m x (EuclideanSpace.single i 1))
        (coordinateDerivative φ hφ i x)) =
      -(∫ x in Metric.ball 0 R.val, inner ℝ
        (∑ i : Fin n,
          fderiv ℝ (fun z => fderiv ℝ m z (EuclideanSpace.single i 1)) x
            (EuclideanSpace.single i 1)) (φ x)) := by
  letI : IsFiniteMeasure (volume.restrict (Metric.ball (0 : Domain n) R.val)) :=
    isFiniteMeasure_restrict.mpr measure_ball_ne_top
  obtain ⟨_, hDm2, hLap2, _⟩ := dirichlet_smoothData_closedBall R U hU hclosed m hm
  have hmeasure : volume.restrict (Metric.ball (0 : Domain n) R.val) ≤
      volume.restrict (Metric.closedBall (0 : Domain n) R.val) :=
    Measure.restrict_mono_set volume Metric.ball_subset_closedBall
  have hφ2 : MemLp φ 2 (volume.restrict (Metric.ball (0 : Domain n) R.val)) :=
    (hφ.continuous.memLp_top_of_hasCompactSupport hcφ _).mono_exponent (by simp)
  have hDm : ContDiffOn ℝ ∞ (fderiv ℝ m) U :=
    hm.fderiv_of_isOpen hU (by simp)
  have hcolumn (i : Fin n) :
      ContDiffOn ℝ ∞ (fun z => fderiv ℝ m z (EuclideanSpace.single i 1)) U :=
    hDm.clm_apply contDiffOn_const
  have hsecond (i : Fin n) : ContinuousOn
      (fun x => fderiv ℝ (fun z => fderiv ℝ m z (EuclideanSpace.single i 1)) x
        (EuclideanSpace.single i 1)) (Metric.closedBall 0 R.val) :=
    (((hcolumn i).continuousOn_fderiv_of_isOpen hU (by simp)).clm_apply
      continuousOn_const).mono hclosed
  have hleft (i : Fin n) : IntegrableOn (fun x =>
      inner ℝ (fderiv ℝ m x (EuclideanSpace.single i 1))
        (coordinateDerivative φ hφ i x)) (Metric.ball 0 R.val) volume := by
    have hdφ : Continuous (coordinateDerivative φ hφ i) :=
      (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
    have hc : HasCompactSupport (coordinateDerivative φ hφ i) :=
      hcφ.fderiv_apply ℝ (EuclideanSpace.single i 1)
    exact inner_integrable_L2 ((hDm2 i).mono_measure hmeasure)
      ((hdφ.memLp_top_of_hasCompactSupport hc _).mono_exponent (by simp))
  have hright (i : Fin n) : Integrable (fun x => inner ℝ
      (fderiv ℝ (fun z => fderiv ℝ m z (EuclideanSpace.single i 1)) x
        (EuclideanSpace.single i 1)) (φ x)) volume :=
    compact_inner_integrable (hsecond i) hφ.continuous.continuousOn
      (subset_tsupport φ |>.trans hsφ)
  have hsign (i : Fin n) :
      (∫ x in Metric.ball 0 R.val, inner ℝ
        (fderiv ℝ m x (EuclideanSpace.single i 1)) (coordinateDerivative φ hφ i x)) =
      -(∫ x in Metric.ball 0 R.val, inner ℝ
        (fderiv ℝ (fun z => fderiv ℝ m z (EuclideanSpace.single i 1)) x
          (EuclideanSpace.single i 1)) (φ x)) := by
    have hl : Integrable (fun x => inner ℝ
        (fderiv ℝ m x (EuclideanSpace.single i 1)) (coordinateDerivative φ hφ i x)) volume := by
      apply (integrableOn_iff_integrable_of_support_subset ?_).mp (hleft i)
      intro x hx
      apply hsφ
      by_contra hnot
      have hdnot : x ∉ tsupport (coordinateDerivative φ hφ i) :=
        fun hmem => hnot (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1) hmem)
      exact hx (by simp only [image_eq_zero_of_notMem_tsupport hdnot, inner_zero_right])
    have hv : Integrable (fun x => inner ℝ
        (fderiv ℝ m x (EuclideanSpace.single i 1)) (φ x)) volume :=
      compact_inner_integrable ((hcolumn i).continuousOn.mono hclosed)
        hφ.continuous.continuousOn (subset_tsupport φ |>.trans hsφ)
    have hi := integral_bilinear_fderiv_right_eq_neg_left_of_integrable
      (f := fun z => fderiv ℝ m z (EuclideanSpace.single i 1))
      (g := φ) (v := EuclideanSpace.single i 1) (B := innerSL ℝ)
      (hright i) hl hv
      (fun x hx => ((hcolumn i).contDiffAt
        (hU.mem_nhds (hclosed (Metric.ball_subset_closedBall (hsφ hx))))).differentiableAt
          (by simp))
      (fun _ _ => (hφ.differentiable (by simp)).differentiableAt)
    have hzφ (x : Domain n) (hx : x ∉ Metric.ball 0 R.val) : φ x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun hmem => hx (hsφ hmem))
    have hzD (x : Domain n) (hx : x ∉ Metric.ball 0 R.val) :
        coordinateDerivative φ hφ i x = 0 :=
      image_eq_zero_of_notMem_tsupport
        (fun hmem => hx (hsφ (tsupport_fderiv_apply_subset ℝ
          (EuclideanSpace.single i 1) hmem)))
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx => by rw [hzD x hx, inner_zero_right]),
      setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun x hx => by rw [hzφ x hx, inner_zero_right])]
    exact hi
  refine ⟨integrable_finsetSum Finset.univ (fun i _ => hleft i),
    inner_integrable_L2 (hLap2.mono_measure hmeasure) hφ2, ?_⟩
  rw [integral_finsetSum _ (fun i _ => hleft i)]
  simp_rw [hsign, sum_inner]
  rw [Finset.sum_neg_distrib, integral_finsetSum _ (fun i _ => (hright i).integrableOn)]

end HarmonicMaps

end
