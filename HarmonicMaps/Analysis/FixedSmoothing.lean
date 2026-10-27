module

public import HarmonicMaps.Frozen.UniformSmoothing
public import HarmonicMaps.Frozen.TubularProjection
public import HarmonicMaps.Analysis.BallSegmentEnergy
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Fixed-scale projected smoothing and oscillation

One dimension-only constant controls the actual Hilbert--Schmidt derivative,
operator derivative and oscillation of the literal fixed-scale integral. The
projected map agrees pointwise with the actual tube-subtype nearest projection
and takes values in the original target throughout the half ball.
-/

public section

open MeasureTheory Set
open scoped ENNReal ContDiff

namespace HarmonicMaps

/-- The literal fixed-scale smoothing and its projection have the source
smoothness, target values, derivative bound and uniform oscillation estimate. -/
theorem fixedSmoothing_complete :
    ∃ ρ : ∀ (q : ℕ), CompactSmoothEmbeddedTarget q → ℝ,
    ∃ Q : ∀ (q : ℕ), CompactSmoothEmbeddedTarget q → Ambient q → Ambient q,
    (∀ (q : ℕ) (N : CompactSmoothEmbeddedTarget q),
      0 < ρ q N ∧ ρ q N ≤ tubularBaseRadius q N ∧ ContDiff ℝ ∞ (Q q N) ∧
      ∀ z : tubularTube q N, Metric.infDist z.val N.carrierSet < ρ q N →
        Q q N z.val = (tubularProjection q N z).val) ∧
    ∀ (n : ℕ), 2 ≤ n →
    ∃ C₀ C : ℝ, 0 < C₀ ∧ 0 < C ∧
    ∀ (q : ℕ) (N : CompactSmoothEmbeddedTarget q),
    ∀ (η : ℝ), 0 < η → η < 1 → η ^ (1 / 4 : ℝ) ≤ 1 / 4 →
      Real.sqrt (C₀ * η) < ρ q N →
    ∀ (u : Domain n → Ambient q) (Du : Domain n → Gradient n q),
      MemW12Loc (ballDomain (0 : Domain n) 1) u Du →
      TakesValuesIn N (ballDomain (0 : Domain n) 1) u →
      IsLocallyEnergyMinimizing N (ballDomain (0 : Domain n) 1) u Du →
      dirichletEnergy Du (Metric.ball (0 : Domain n) 1) ≤ ENNReal.ofReal η →
    let hbar := η ^ (1 / 4 : ℝ)
    let m : Domain n → Ambient q := fun x =>
      ∫ y in Metric.ball (0 : Domain n) 1,
        fixedMollifierKernel n y • u (x - hbar • y)
    ContDiffOn ℝ ∞ m (Metric.ball (0 : Domain n) (3 / 4)) ∧
    ContDiffOn ℝ ∞ (Q q N ∘ m) (Metric.ball (0 : Domain n) (1 / 2)) ∧
    (∀ x ∈ Metric.ball (0 : Domain n) (1 / 2),
      ∃ hx : m x ∈ tubularTube q N,
        Metric.infDist (m x) N.carrierSet < ρ q N ∧
        Q q N (m x) = (tubularProjection q N ⟨m x, hx⟩).val ∧
        Q q N (m x) ∈ N.carrierSet ∧ ‖fderiv ℝ (Q q N) (m x)‖ ≤ 2 ∧
        Real.sqrt (hsNormSq (fun i => fderiv ℝ m x (EuclideanSpace.single i 1))) ≤
          C * hbar ∧
        ‖fderiv ℝ m x‖ ≤ C * hbar ∧ ‖m x - m 0‖ ≤ C * hbar) ∧
    ∀ x ∈ Metric.ball (0 : Domain n) (1 / 2),
      ∀ y ∈ Metric.ball (0 : Domain n) (1 / 2),
        ‖m x - m y‖ ≤ C * hbar * ‖x - y‖ := by
  classical
  have hfamily : ∀ (q : ℕ) (N : CompactSmoothEmbeddedTarget q),
      ∃ (r : ℝ) (F : Ambient q → Ambient q),
        0 < r ∧ r ≤ tubularBaseRadius q N ∧ ContDiff ℝ ∞ F ∧
        (∀ z : tubularTube q N, Metric.infDist z.val N.carrierSet < r →
          F z.val = (tubularProjection q N z).val) ∧
        ∀ z : tubularTube q N, Metric.infDist z.val N.carrierSet < r →
          ‖fderiv ℝ F z.val‖ ≤ 2 := by
    intro q N
    obtain ⟨r, hr, hrbase, hsub, _, _, _, _, hD, _, _, _, _, F, hF, hFeq, _⟩ :=
      tubularProjection_complete q N
    refine ⟨r, F, hr, hrbase, hF, hFeq, ?_⟩
    intro z hz
    let V : Set (Ambient q) := {w | Metric.infDist w N.carrierSet < r}
    have hV : IsOpen V := isOpen_lt (Metric.continuous_infDist_pt N.carrierSet) continuous_const
    have hVsub : V ⊆ tubularTube q N := by
      intro w hw
      change Metric.infDist w N.carrierSet < 2 * tubularBaseRadius q N
      change Metric.infDist w N.carrierSet < r at hw
      linarith only [hw, hr, hrbase]
    have hjet := (tubularProjectionDerivative_characterization q N).1
      z V F hV hz hVsub hF.contDiffOn (fun w hw => hFeq w hw)
    rw [hjet]
    have hzwide : z.val ∈ {w | Metric.infDist w N.carrierSet < 2 * r} := by
      change Metric.infDist z.val N.carrierSet < 2 * r
      linarith only [hz, hr]
    exact hD ⟨z.val, hzwide⟩
  choose ρ Q hρ hρbase hQ hQeq hQD using hfamily
  refine ⟨ρ, Q, fun q N => ⟨hρ q N, hρbase q N, hQ q N, hQeq q N⟩, ?_⟩
  intro n hn
  obtain ⟨C₀, hC₀, hSmoothing⟩ := uniformSmoothing_complete n hn
  let C : ℝ := Real.sqrt C₀
  have hC : 0 < C := Real.sqrt_pos.2 hC₀
  have hCsq : C ^ 2 = C₀ := Real.sq_sqrt hC₀.le
  refine ⟨C₀, C, hC₀, hC, ?_⟩
  intro q N
  let r : ℝ := ρ q N
  let F : Ambient q → Ambient q := Q q N
  have hr : 0 < r := hρ q N
  have hrbase : r ≤ tubularBaseRadius q N := hρbase q N
  have hF : ContDiff ℝ ∞ F := hQ q N
  have hFeq := hQeq q N
  intro η hη _hηOne hscale hsmall u Du hu hN hmin hEnergy
  let hbar : ℝ := η ^ (1 / 4 : ℝ)
  have hhbar : 0 < hbar := Real.rpow_pos_of_pos hη _
  let h : PositiveRadius := ⟨hbar, hhbar⟩
  let m : Domain n → Ambient q := fun x =>
    ∫ y in Metric.ball (0 : Domain n) 1,
      fixedMollifierKernel n y • u (x - hbar • y)
  have hfinite : dirichletEnergy Du (Metric.ball (0 : Domain n) 1) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hEnergy
  have hEreal : (dirichletEnergy Du (Metric.ball (0 : Domain n) 1)).toReal ≤ η :=
    ENNReal.toReal_le_of_le_ofReal hη.le hEnergy
  obtain ⟨hm, hpoint, _⟩ := hSmoothing q N u Du hu hN hmin hfinite h hscale
  have hm' : ContDiffOn ℝ ∞ m (Metric.ball (0 : Domain n) (3 / 4)) := hm
  have hhalf : Metric.ball (0 : Domain n) (1 / 2 : ℝ) ⊆
      Metric.ball 0 (3 / 4) := Metric.ball_subset_ball (by norm_num)
  have hdiff (x : Domain n) (hx : x ∈ Metric.ball (0 : Domain n) (1 / 2)) :
      DifferentiableAt ℝ m x :=
    (hm'.contDiffAt (Metric.isOpen_ball.mem_nhds (hhalf hx))).differentiableAt (by simp)
  have hfour : hbar ^ 4 = η := by
    dsimp only [hbar]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hη.le]
    norm_num
  have hpower : η * hbar ^ (-2 : ℤ) = hbar ^ 2 := by
    rw [← hfour, zpow_neg, zpow_ofNat]
    field_simp
  have hbound (x : Domain n) (hx : x ∈ Metric.ball (0 : Domain n) (1 / 2)) :
      hsNormSq (fun i => fderiv ℝ m x (EuclideanSpace.single i 1)) ≤ (C * hbar) ^ 2 := by
    have hg := (hpoint x hx).2
    change hsNormSq (fun i => fderiv ℝ m x (EuclideanSpace.single i 1)) ≤
      C₀ * (dirichletEnergy Du (Metric.ball (0 : Domain n) 1)).toReal * hbar ^ (-2 : ℤ) at hg
    calc
      _ ≤ C₀ * (dirichletEnergy Du (Metric.ball (0 : Domain n) 1)).toReal *
          hbar ^ (-2 : ℤ) := hg
      _ ≤ C₀ * η * hbar ^ (-2 : ℤ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hEreal hC₀.le)
          (zpow_nonneg hhbar.le _)
      _ = (C * hbar) ^ 2 := by rw [mul_assoc, hpower, mul_pow, hCsq]
  have hop (x : Domain n) (hx : x ∈ Metric.ball (0 : Domain n) (1 / 2)) :
      ‖fderiv ℝ m x‖ ≤ C * hbar := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (mul_nonneg hC.le hhbar.le)
    intro v hv
    have hsq := norm_apply_sq_le_hsNormSq (fderiv ℝ m x) v
    rw [hv, one_pow, one_mul] at hsq
    nlinarith only [hsq, hbound x hx, norm_nonneg (fderiv ℝ m x v),
      mul_nonneg hC.le hhbar.le]
  have hlip (x : Domain n) (hx : x ∈ Metric.ball (0 : Domain n) (1 / 2))
      (y : Domain n) (hy : y ∈ Metric.ball (0 : Domain n) (1 / 2)) :
      ‖m x - m y‖ ≤ C * hbar * ‖x - y‖ :=
    (convex_ball (0 : Domain n) (1 / 2)).norm_image_sub_le_of_norm_fderiv_le
      hdiff hop hy hx
  refine ⟨hm', hF.contDiffOn.comp (hm'.mono hhalf) (mapsTo_univ _ _), ?_, hlip⟩
  intro x hx
  have hdist : Metric.infDist (m x) N.carrierSet < r := by
    have hd := (hpoint x hx).1
    have hsq : Metric.infDist (m x) N.carrierSet ^ 2 ≤ C₀ * η :=
      hd.trans (mul_le_mul_of_nonneg_left hEreal hC₀.le)
    have hsqrt : Metric.infDist (m x) N.carrierSet ≤ Real.sqrt (C₀ * η) := by
      have hroot := Real.sq_sqrt (mul_nonneg hC₀.le hη.le)
      nlinarith only [hsq, hroot, Metric.infDist_nonneg (x := m x) (s := N.carrierSet),
        Real.sqrt_nonneg (C₀ * η)]
    exact hsqrt.trans_lt hsmall
  have hxtube : m x ∈ tubularTube q N := by
    change Metric.infDist (m x) N.carrierSet < 2 * tubularBaseRadius q N
    linarith only [hdist, hr, hrbase]
  have hvalue : F (m x) = (tubularProjection q N ⟨m x, hxtube⟩).val :=
    hFeq ⟨m x, hxtube⟩ hdist
  have htarget : F (m x) ∈ N.carrierSet := hvalue ▸ (tubularProjection q N ⟨m x, hxtube⟩).property
  have hQderiv : ‖fderiv ℝ F (m x)‖ ≤ 2 := hQD q N ⟨m x, hxtube⟩ hdist
  have hHS : Real.sqrt (hsNormSq (fun i => fderiv ℝ m x (EuclideanSpace.single i 1))) ≤
      C * hbar := by
    exact (Real.sqrt_le_sqrt (hbound x hx)).trans_eq (Real.sqrt_sq (mul_nonneg hC.le hhbar.le))
  have hzero : (0 : Domain n) ∈ Metric.ball (0 : Domain n) (1 / 2) :=
    Metric.mem_ball_self (by norm_num)
  have hnormx : ‖x‖ ≤ 1 := by
    have hn : ‖x‖ < 1 / 2 := by simpa only [Metric.mem_ball, dist_zero_right] using hx
    linarith only [hn]
  have hosc : ‖m x - m 0‖ ≤ C * hbar := by
    have h := hlip x hx 0 hzero
    rw [sub_zero] at h
    exact h.trans ((mul_le_mul_of_nonneg_left hnormx (mul_nonneg hC.le hhbar.le)).trans_eq (mul_one _))
  exact ⟨hxtube, hdist, hvalue, htarget, hQderiv, hHS, hop x hx, hosc⟩

end HarmonicMaps
end
