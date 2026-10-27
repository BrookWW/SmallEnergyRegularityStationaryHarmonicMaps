module

public import StationaryHarmonicMaps.Analysis.HodgeDirichletUniqueness
public import StationaryHarmonicMaps.Analysis.SobolevCutoff
public import StationaryHarmonicMaps.Analysis.HSProductIntegrals
public import StationaryHarmonicMaps.Analysis.SobolevLpOscillation
public import HolderToCK.Foundation.WeakPoisson
public import HarmonicMaps.Analysis.SobolevCutoffBoundary

/-!
# Rough div--curl cancellation against actual compact kernels

The original distributional divergence equation extends to the genuine
zero-boundary Sobolev product of a smooth kernel with the original map.
The resulting identity moves the derivative onto the kernel and permits
subtraction of any constant. All products are genuine L1 functions. These
identities are the local cancellation step in the CLMS maximal argument;
they do not assert Hardy--BMO duality.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped ENNReal ContDiff Topology

namespace StationaryHarmonicMaps.Analysis

/-- The original distributional divergence equation admits every actual native W0 test. -/
theorem divergence_free_zeroBoundary_test {n q : ℕ} (Ω : OpenDomain n)
    (Z : Domain n → Gradient n q)
    (hZ : ∀ i, MemLp (fun x => Z x i) 2 (volume.restrict Ω.val))
    (hdiv : HolderToCK.WeakPoissonOn Ω Z (fun _ => (0 : Ambient q)))
    {w : Domain n → Ambient q} {Dw : Domain n → Gradient n q}
    (hw : HasZeroBoundaryValues Ω w Dw) :
    IntegrableOn (fun x => ∑ i : Fin n, inner ℝ (Z x i) (Dw x i)) Ω.val volume ∧
    (∫ x in Ω.val, ∑ i : Fin n, inner ℝ (Z x i) (Dw x i)) = 0 := by
  have H := gradient_pairing_eq_on_zeroBoundary_of_smooth Ω Z (fun _ _ => 0) hZ
    (fun _ => MemLp.zero) (fun ψ hψ hc hs => by
      have H := (hdiv.2 ψ hψ hc hs).2.2
      simpa only [inner_zero_left, Finset.sum_const_zero, integral_zero, neg_zero] using H) hw
  exact ⟨H.1, by simpa only [inner_zero_left, Finset.sum_const_zero, integral_zero] using H.2.2⟩

/-- Actual rough Sobolev data satisfy the compact-kernel cancellation identity with any subtracted constant. -/
theorem divcurl_kernel_cancellation {n q : ℕ} (a : Domain n) {r : ℝ} (hr : 0 < r)
    (Z : Domain n → Gradient n q)
    (hZ : ∀ i, MemLp (fun x => Z x i) 2 (volume.restrict (Metric.ball a r)))
    (hdiv : HolderToCK.WeakPoissonOn (ballDomain a r) Z (fun _ => (0 : Ambient q)))
    {w : Domain n → Ambient q} {Dw : Domain n → Gradient n q}
    (hw : MemW12 (ballDomain a r) w Dw) (c : Ambient q)
    (κ : Domain n → ℝ) (hκ : ContDiff ℝ ∞ κ)
    (hcκ : HasCompactSupport κ) (hsκ : tsupport κ ⊆ Metric.ball a r) :
    IntegrableOn (fun x => κ x * ∑ i : Fin n, inner ℝ (Z x i) (Dw x i))
      (Metric.ball a r) volume ∧
    IntegrableOn (fun x => ∑ i : Fin n,
      fderiv ℝ κ x (EuclideanSpace.single i 1) * inner ℝ (Z x i) (w x-c))
      (Metric.ball a r) volume ∧
    (∫ x in Metric.ball a r, κ x * ∑ i : Fin n, inner ℝ (Z x i) (Dw x i)) =
      -(∫ x in Metric.ball a r, ∑ i : Fin n,
        fderiv ℝ κ x (EuclideanSpace.single i 1) * inner ℝ (Z x i) (w x-c)) := by
  let μ : Measure (Domain n) := volume.restrict (Metric.ball a r)
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  letI : IsFiniteMeasure (volume.restrict (ballDomain a r).val) :=
    isFiniteMeasure_restrict.mpr measure_ball_ne_top
  have hwc : MemW12 (ballDomain a r) (fun x => w x-c) Dw :=
    ⟨(memW12Loc_sub_const hw.to_memW12Loc c).1, hw.2.1.sub (memLp_const c), hw.2.2⟩
  have htest := hwc.smoothCutoff_zeroBoundary_ball hr hκ hcκ hsκ
  have H := divergence_free_zeroBoundary_test (ballDomain a r) Z hZ hdiv htest
  have hκtop : MemLp κ (⊤ : ℝ≥0∞) μ := hκ.continuous.memLp_top_of_hasCompactSupport hcκ μ
  have hdκtop (i : Fin n) : MemLp (fun x => fderiv ℝ κ x (EuclideanSpace.single i 1)) (⊤ : ℝ≥0∞) μ :=
    ((hκ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_top_of_hasCompactSupport
      (hcκ.fderiv_apply ℝ (EuclideanSpace.single i 1)) μ
  have hleft : Integrable (fun x => κ x * ∑ i : Fin n, inner ℝ (Z x i) (Dw x i)) μ := by
    have HI := integrable_finsetSum Finset.univ fun i _ =>
      HolderToCK.integrable_inner_of_memLp_two (hZ i) (hw.2.2 i)
    change Integrable (fun x => ∑ i : Fin n, inner ℝ (Z x i) (Dw x i)) μ at HI
    exact (HI.smul_of_top_right hκtop).congr (Eventually.of_forall fun x => rfl)
  have hright : Integrable (fun x => ∑ i : Fin n,
      fderiv ℝ κ x (EuclideanSpace.single i 1) * inner ℝ (Z x i) (w x-c)) μ := by
    apply integrable_finsetSum
    intro i _
    have HI := HolderToCK.integrable_inner_of_memLp_two (hZ i) hwc.2.1
    change Integrable (fun x => inner ℝ (Z x i) (w x-c)) μ at HI
    exact (HI.smul_of_top_right (hdκtop i)).congr (Eventually.of_forall fun x => rfl)
  have hpoint (x : Domain n) :
      (∑ i : Fin n, inner ℝ (Z x i)
        (coordinateDerivative κ hκ i x • (w x-c)+κ x • Dw x i)) =
      (∑ i : Fin n, fderiv ℝ κ x (EuclideanSpace.single i 1) * inner ℝ (Z x i) (w x-c)) +
        κ x * ∑ i : Fin n, inner ℝ (Z x i) (Dw x i) := by
    simp only [inner_add_right, real_inner_smul_right, Finset.sum_add_distrib,
      coordinateDerivative, Finset.mul_sum]
  refine ⟨hleft,hright,?_⟩
  have HH := H.2
  rw [integral_congr_ae (Eventually.of_forall hpoint)] at HH
  change (∫ x, (∑ i : Fin n, fderiv ℝ κ x (EuclideanSpace.single i 1) *
    inner ℝ (Z x i) (w x-c)) + κ x * ∑ i : Fin n, inner ℝ (Z x i) (Dw x i) ∂μ) = 0 at HH
  rw [integral_add hright hleft] at HH
  linarith

/-- A columnwise kernel derivative bound controls the cancellation by actual local L2 energies and oscillation. -/
theorem divcurl_kernel_energy_bound {n q : ℕ} (a : Domain n) {r : ℝ} (hr : 0 < r)
    (Z : Domain n → Gradient n q)
    (hZ : ∀ i, MemLp (fun x => Z x i) 2 (volume.restrict (Metric.ball a r)))
    (hdiv : HolderToCK.WeakPoissonOn (ballDomain a r) Z (fun _ => (0 : Ambient q)))
    {w : Domain n → Ambient q} {Dw : Domain n → Gradient n q}
    (hw : MemW12 (ballDomain a r) w Dw) (c : Ambient q)
    (κ : Domain n → ℝ) (hκ : ContDiff ℝ ∞ κ)
    (hcκ : HasCompactSupport κ) (hsκ : tsupport κ ⊆ Metric.ball a r)
    {B : ℝ} (hB : 0 ≤ B)
    (hDκ : ∀ x ∈ Metric.ball a r, ∀ i : Fin n,
      |fderiv ℝ κ x (EuclideanSpace.single i 1)| ≤ B) :
    |∫ x in Metric.ball a r, κ x * ∑ i : Fin n, inner ℝ (Z x i) (Dw x i)| ≤
      B * Real.sqrt (n : ℝ) * Real.sqrt (∫ x in Metric.ball a r, hsNormSq (Z x)) *
        Real.sqrt (∫ x in Metric.ball a r, ‖w x-c‖ ^ 2) := by
  let μ : Measure (Domain n) := volume.restrict (Metric.ball a r)
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  letI : IsFiniteMeasure (volume.restrict (ballDomain a r).val) :=
    isFiniteMeasure_restrict.mpr measure_ball_ne_top
  have hwc : MemLp (fun x => w x-c) 2 μ := hw.2.1.sub (memLp_const c)
  have HC := divcurl_kernel_cancellation a hr Z hZ hdiv hw c κ hκ hcκ hsκ
  have HE := integral_hs_mul_norm_le Z (fun x => w x-c) hZ hwc
  have hpoint (x : Domain n) (hx : x ∈ Metric.ball a r) :
      |∑ i : Fin n, fderiv ℝ κ x (EuclideanSpace.single i 1) * inner ℝ (Z x i) (w x-c)| ≤
      (B * Real.sqrt (n : ℝ)) * (Real.sqrt (hsNormSq (Z x)) * ‖w x-c‖) := by
    calc
      _ ≤ ∑ i : Fin n, |fderiv ℝ κ x (EuclideanSpace.single i 1) * inner ℝ (Z x i) (w x-c)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin n, B * (‖Z x i‖ * ‖w x-c‖) := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul]
        exact mul_le_mul (hDκ x hx i) (abs_real_inner_le_norm _ _) (abs_nonneg _) hB
      _ = B * ((∑ i : Fin n, ‖Z x i‖) * ‖w x-c‖) := by
        rw [Finset.sum_mul, Finset.mul_sum]
      _ ≤ B * ((Real.sqrt (n : ℝ) * Real.sqrt (hsNormSq (Z x))) * ‖w x-c‖) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
          (sum_column_norm_le_sqrt_dimension_mul_hs (Z x)) (norm_nonneg _)) hB
      _ = _ := by ring
  rw [HC.2.2, abs_neg]
  calc
    _ ≤ ∫ x in Metric.ball a r, |∑ i : Fin n,
        fderiv ℝ κ x (EuclideanSpace.single i 1) * inner ℝ (Z x i) (w x-c)| :=
      abs_integral_le_integral_abs
    _ ≤ ∫ x in Metric.ball a r, (B * Real.sqrt (n : ℝ)) *
        (Real.sqrt (hsNormSq (Z x)) * ‖w x-c‖) := by
      apply integral_mono_ae HC.2.1.abs (HE.1.const_mul _)
      filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
      exact hpoint x hx
    _ = (B * Real.sqrt (n : ℝ)) *
        (∫ x in Metric.ball a r, Real.sqrt (hsNormSq (Z x)) * ‖w x-c‖) := integral_const_mul _ _
    _ ≤ (B * Real.sqrt (n : ℝ)) *
        (Real.sqrt (∫ x in Metric.ball a r, hsNormSq (Z x)) *
          Real.sqrt (∫ x in Metric.ball a r, ‖w x-c‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left HE.2 (mul_nonneg hB (Real.sqrt_nonneg _))
    _ = _ := by ring

end StationaryHarmonicMaps.Analysis

end
