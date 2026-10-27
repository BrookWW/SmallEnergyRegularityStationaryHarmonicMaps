module

public import HarmonicMaps.Analysis.HarmonicReplacementGradientErrorGreen
public import HarmonicMaps.Analysis.HarmonicGradientErrorBound
public import HarmonicMaps.Analysis.HarmonicMaximumDifference
public import HarmonicMaps.Analysis.HarmonicInteriorGradient
public import HarmonicMaps.Frozen.UniformSmoothing
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Quantitative estimates for the actual harmonic replacement

The original Sobolev and minimizing data produce one replacement with exact
energy and signed Green identities, uniform difference, interior gradient,
and gradient-error estimates. The constant depends only on the dimension and
the target, and precedes every small parameter and source map.
-/

public section

open MeasureTheory Set
open scoped ENNReal ContDiff

namespace HarmonicMaps

private theorem oscillation_of_hsNormSq_bound {n q : ℕ}
    (m : Domain n → Ambient q)
    (hm : ContDiffOn ℝ ∞ m (Metric.ball (0 : Domain n) (3 / 4 : ℝ)))
    (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ x ∈ Metric.ball (0 : Domain n) (1 / 2 : ℝ),
      hsNormSq (fun i => fderiv ℝ m x (EuclideanSpace.single i 1)) ≤ M ^ 2) :
    ∀ x ∈ Metric.ball (0 : Domain n) (1 / 2 : ℝ), ‖m x - m 0‖ ≤ M := by
  have hhalf : Metric.ball (0 : Domain n) (1 / 2 : ℝ) ⊆ Metric.ball 0 (3 / 4) :=
    Metric.ball_subset_ball (by norm_num)
  have hdiff (x : Domain n) (hx : x ∈ Metric.ball (0 : Domain n) (1 / 2 : ℝ)) :
      DifferentiableAt ℝ m x :=
    (hm.contDiffAt (Metric.isOpen_ball.mem_nhds (hhalf hx))).differentiableAt (by simp)
  have hop (x : Domain n) (hx : x ∈ Metric.ball (0 : Domain n) (1 / 2 : ℝ)) :
      ‖fderiv ℝ m x‖ ≤ M := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm hM
    intro v hv
    have hsq := norm_apply_sq_le_hsNormSq (fderiv ℝ m x) v
    rw [hv, one_pow, one_mul] at hsq
    nlinarith only [hsq, hbound x hx, norm_nonneg (fderiv ℝ m x v), hM]
  intro x hx
  have hzero : (0 : Domain n) ∈ Metric.ball (0 : Domain n) (1 / 2 : ℝ) :=
    Metric.mem_ball_self (by norm_num)
  have hnorm : ‖x‖ ≤ 1 := by
    have hxnorm : ‖x‖ < (1 / 2 : ℝ) := by
      simpa only [Metric.mem_ball, dist_zero_right] using hx
    linarith only [hxnorm]
  have hlip := (convex_ball (0 : Domain n) (1 / 2 : ℝ)).norm_image_sub_le_of_norm_fderiv_le
    hdiff hop hzero hx
  rw [sub_zero] at hlip
  exact hlip.trans ((mul_le_mul_of_nonneg_left hnorm hM).trans_eq (mul_one M))

/-- One target-and-dimension constant bounds the actual replacement difference,
native interior gradient and gradient error by the original energy. -/
theorem harmonicReplacement_estimates (n : ℕ) (hn : 2 ≤ n)
    (q : ℕ) (N : CompactSmoothEmbeddedTarget q) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (η : ℝ), 0 < η → η ^ (1 / 4 : ℝ) ≤ 1 / 4 →
    ∀ (u : Domain n → Ambient q) (Du : Domain n → Gradient n q),
      MemW12Loc (ballDomain (0 : Domain n) 1) u Du →
      TakesValuesIn N (ballDomain (0 : Domain n) 1) u →
      IsLocallyEnergyMinimizing N (ballDomain (0 : Domain n) 1) u Du →
      dirichletEnergy Du (Metric.ball (0 : Domain n) 1) ≤ ENNReal.ofReal η →
    let m : Domain n → Ambient q := fun x =>
      ∫ y in Metric.ball (0 : Domain n) 1,
        fixedMollifierKernel n y • u (x - η ^ (1 / 4 : ℝ) • y)
    let E := (dirichletEnergy Du (Metric.ball (0 : Domain n) 1)).toReal
    ∃ w : Domain n → Ambient q,
      ContDiffOn ℝ ∞ w (Metric.closedBall (0 : Domain n) (1 / 2 : ℝ)) ∧
      (∀ x ∈ Metric.sphere (0 : Domain n) (1 / 2 : ℝ), w x = m x) ∧
      (∀ x ∈ Metric.ball (0 : Domain n) (1 / 2 : ℝ), Laplacian.laplacian w x = 0) ∧
      MemW12 (ballDomain (0 : Domain n) (1 / 2 : ℝ)) w
        (fun x i => fderiv ℝ w x (EuclideanSpace.single i 1)) ∧
      HasZeroBoundaryValues (ballDomain (0 : Domain n) (1 / 2 : ℝ)) (m - w)
        (fun x i => fderiv ℝ m x (EuclideanSpace.single i 1) -
          fderiv ℝ w x (EuclideanSpace.single i 1)) ∧
      (∀ z : Domain n → Ambient q,
        ContDiffOn ℝ ∞ z (Metric.closedBall (0 : Domain n) (1 / 2 : ℝ)) →
        (∀ x ∈ Metric.sphere (0 : Domain n) (1 / 2 : ℝ), z x = m x) →
        (∀ x ∈ Metric.ball (0 : Domain n) (1 / 2 : ℝ), Laplacian.laplacian z x = 0) →
        EqOn z w (Metric.closedBall (0 : Domain n) (1 / 2 : ℝ))) ∧
      (∫ x in Metric.ball (0 : Domain n) (1 / 2 : ℝ),
        hsNormSq (fun i => fderiv ℝ m x (EuclideanSpace.single i 1))) =
        (∫ x in Metric.ball (0 : Domain n) (1 / 2 : ℝ),
          hsNormSq (fun i => fderiv ℝ w x (EuclideanSpace.single i 1))) +
        (∫ x in Metric.ball (0 : Domain n) (1 / 2 : ℝ),
          hsNormSq (fun i => fderiv ℝ m x (EuclideanSpace.single i 1) -
            fderiv ℝ w x (EuclideanSpace.single i 1))) ∧
      (∫ x in Metric.ball (0 : Domain n) (1 / 2 : ℝ),
        hsNormSq (fun i => fderiv ℝ w x (EuclideanSpace.single i 1))) ≤ E ∧
      (∫ x in Metric.ball (0 : Domain n) (1 / 2 : ℝ),
        hsNormSq (fun i => fderiv ℝ m x (EuclideanSpace.single i 1) -
          fderiv ℝ w x (EuclideanSpace.single i 1))) =
        -(∫ x in Metric.ball (0 : Domain n) (1 / 2 : ℝ),
          inner ℝ (Laplacian.laplacian m x) ((m - w) x)) ∧
      (∀ x ∈ Metric.ball (0 : Domain n) (1 / 2 : ℝ),
        ‖m x - w x‖ ≤ C * η ^ (1 / 4 : ℝ)) ∧
      (∀ x ∈ Metric.ball (0 : Domain n) (1 / 4 : ℝ),
        hsNormSq (fun i => fderiv ℝ w x (EuclideanSpace.single i 1)) ≤ C * E) ∧
      (∫ x in Metric.ball (0 : Domain n) (1 / 2 : ℝ),
        hsNormSq (fun i => fderiv ℝ m x (EuclideanSpace.single i 1) -
          fderiv ℝ w x (EuclideanSpace.single i 1))) ≤ C * η ^ (1 / 4 : ℝ) * E := by
  obtain ⟨C₀, hC₀, hSmoothing⟩ := uniformSmoothing_complete n hn
  let D : ℝ := Real.sqrt C₀
  let S : Set ℝ := {k | ∃ p : N.Carrier, ∃ hp : p.val ∈ tubularTube q N,
    k = ‖tubularProjectionSecondDerivative q N ⟨p.val, hp⟩‖}
  let K : ℝ := sSup S
  let G : ℝ := ((volume : Measure (Domain n)).real
    (Metric.ball (0 : Domain n) (1 / 4 : ℝ)))⁻¹
  let C : ℝ := 2 * D + 2 * D * |K| + G + 1
  have hD : 0 < D := Real.sqrt_pos.2 hC₀
  have hG : 0 ≤ G := inv_nonneg.mpr ENNReal.toReal_nonneg
  have hDK : 0 ≤ 2 * D * |K| := mul_nonneg (by positivity) (abs_nonneg K)
  have hC : 0 < C := by dsimp only [C]; linarith only [hD, hDK, hG]
  have hCD : 2 * D ≤ C := by dsimp only [C]; linarith only [hDK, hG]
  have hCK : 2 * D * |K| ≤ C := by dsimp only [C]; linarith only [hD, hG]
  have hCG : G ≤ C := by dsimp only [C]; linarith only [hD, hDK]
  refine ⟨C, hC, ?_⟩
  intro η hη hscale u Du hu hN hmin hsmall
  let hbar : ℝ := η ^ (1 / 4 : ℝ)
  have hhbar : 0 < hbar := Real.rpow_pos_of_pos hη _
  let h : PositiveRadius := ⟨hbar, hhbar⟩
  let R : PositiveRadius := ⟨1 / 2, by norm_num⟩
  let m : Domain n → Ambient q := fun x =>
    ∫ y in Metric.ball (0 : Domain n) 1, fixedMollifierKernel n y • u (x - hbar • y)
  let E : ℝ := (dirichletEnergy Du (Metric.ball (0 : Domain n) 1)).toReal
  have hfinite : dirichletEnergy Du (Metric.ball (0 : Domain n) 1) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hsmall
  have hE : 0 ≤ E := ENNReal.toReal_nonneg
  have hEη : E ≤ η := ENNReal.toReal_le_of_le_ofReal hη.le hsmall
  obtain ⟨hm, hpoint, _, _, hLapInt, hLapBound⟩ :=
    hSmoothing q N u Du hu hN hmin hfinite h hscale
  have hm' : ContDiffOn ℝ ∞ m (Metric.ball (0 : Domain n) (3 / 4 : ℝ)) := hm
  have hfour : hbar ^ 4 = η := by
    dsimp only [hbar]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hη.le]
    norm_num
  have hpower : η * hbar ^ (-2 : ℤ) = hbar ^ 2 := by
    rw [← hfour, zpow_neg, zpow_ofNat]
    field_simp
  have hDsquare : D ^ 2 = C₀ := Real.sq_sqrt hC₀.le
  have hgradm (x : Domain n) (hx : x ∈ Metric.ball (0 : Domain n) (1 / 2 : ℝ)) :
      hsNormSq (fun i => fderiv ℝ m x (EuclideanSpace.single i 1)) ≤ (D * hbar) ^ 2 := by
    have hg := (hpoint x hx).2
    change hsNormSq (fun i => fderiv ℝ m x (EuclideanSpace.single i 1)) ≤
      C₀ * E * hbar ^ (-2 : ℤ) at hg
    calc
      _ ≤ C₀ * E * hbar ^ (-2 : ℤ) := hg
      _ ≤ C₀ * η * hbar ^ (-2 : ℤ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hEη hC₀.le)
          (zpow_nonneg hhbar.le _)
      _ = _ := by rw [mul_assoc, hpower, mul_pow, hDsquare]
  have hosc := oscillation_of_hsNormSq_bound m hm' (D * hbar)
    (mul_nonneg hD.le hhbar.le) hgradm
  obtain ⟨v, _, hb, w, hwv, hws, hwh, hformula, hwW, hzero, huniq, _,
    hidentity, hwBound, hgreen⟩ :=
    harmonicReplacement_gradientErrorGreen hn N u Du hu hN η hη hscale hsmall
  have hboundary (x : Domain n) (hx : x ∈ Metric.sphere (0 : Domain n) (1 / 2 : ℝ)) :
      w x = m x := (hwv ⟨x, Metric.sphere_subset_closedBall hx⟩).trans (hb ⟨x, hx⟩)
  have hclosed : Metric.closedBall (0 : Domain n) (1 / 2 : ℝ) ⊆
      Metric.ball 0 (3 / 4) := Metric.closedBall_subset_ball (by norm_num)
  have hformula' := hformula
  rw [← poisson_scaledPolar_eq_euclideanSphereArea hn R] at hformula'
  have hdiff (x : Domain n) (hx : x ∈ Metric.ball (0 : Domain n) (1 / 2 : ℝ)) :
      ‖m x - w x‖ ≤ 2 * D * hbar := by
    have hbnd := poisson_harmonicDifference_le_of_oscillation hn R
      (Metric.ball 0 (3 / 4)) Metric.isOpen_ball hclosed m w hm' hformula'
      (m 0) (D * hbar) hosc x hx
    exact hbnd.trans_eq (by ring)
  have hreal : E = ∫ x in Metric.ball (0 : Domain n) 1, hsNormSq (Du x) :=
    dirichletEnergy_toReal (hu.memW12_unitBall_of_finiteEnergy N hN hfinite).integrable_hsNormSq
  have hwE : (∫ x in Metric.ball (0 : Domain n) (1 / 2 : ℝ),
      hsNormSq (fun i => fderiv ℝ w x (EuclideanSpace.single i 1))) ≤ E := by
    rw [hreal]
    exact hwBound
  have hwgrad (x : Domain n) (hx : x ∈ Metric.ball (0 : Domain n) (1 / 4 : ℝ)) :
      hsNormSq (fun i => fderiv ℝ w x (EuclideanSpace.single i 1)) ≤ C * E := by
    have hg := harmonic_interiorGradient hn w (hws.mono Metric.ball_subset_closedBall)
      hwh hwW.integrable_hsNormSq x hx
    exact hg.trans ((mul_le_mul_of_nonneg_left hwE hG).trans
      (mul_le_mul_of_nonneg_right hCG hE))
  have herror := harmonic_gradientError_le_of_pointwise_distance R
    (Metric.ball 0 (3 / 4)) Metric.isOpen_ball hclosed m w hm' hws hwh hzero
    (2 * D * hbar) hdiff hLapInt
  have herrorBound : (∫ x in Metric.ball (0 : Domain n) (1 / 2 : ℝ),
      hsNormSq (fun i => fderiv ℝ m x (EuclideanSpace.single i 1) -
        fderiv ℝ w x (EuclideanSpace.single i 1))) ≤ C * hbar * E := by
    change (∫ x in Metric.ball (0 : Domain n) (1 / 2 : ℝ),
      ‖Laplacian.laplacian m x‖) ≤ K * E at hLapBound
    calc
      _ ≤ (2 * D * hbar) * (∫ x in Metric.ball (0 : Domain n) (1 / 2 : ℝ),
          ‖Laplacian.laplacian m x‖) := herror
      _ ≤ (2 * D * hbar) * (K * E) :=
        mul_le_mul_of_nonneg_left hLapBound (by positivity)
      _ ≤ (2 * D * hbar) * (|K| * E) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (le_abs_self K) hE)
          (by positivity)
      _ = (2 * D * |K|) * hbar * E := by ring
      _ ≤ C * hbar * E := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCK hhbar.le) hE
  exact ⟨w, hws, hboundary, hwh, hwW, hzero, huniq, hidentity, hwE, hgreen,
    fun x hx => (hdiff x hx).trans (mul_le_mul_of_nonneg_right hCD hhbar.le),
    hwgrad, herrorBound⟩

end HarmonicMaps
end
