module

public import HarmonicMaps.Analysis.ProjectedCompetitor
public import HarmonicMaps.Analysis.HarmonicReplacementEstimate
public import HarmonicMaps.Analysis.DecayCutoff
public import Mathlib.Analysis.Calculus.FDeriv.Congr

/-!
# Source energy comparison on the selected annulus

The genuine projected competitor, harmonic replacement and selected good shell
give the three source powers of the uniform small-energy parameter. Independently
chosen projection extensions agree with the same nearest projection on an open
neighborhood of all attained fixed-smoothing values.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

namespace HarmonicMaps

/-- Uniform constants precede the source parameter and original map. The actual
cutoff, shell, projected competitor and harmonic energy estimate are produced
inside the proof, with the original weak gradient and integer normalization. -/
theorem decay_energy_comparison (n : ℕ) (hn : 2 ≤ n)
    (q : ℕ) (N : CompactSmoothEmbeddedTarget q) :
    ∃ C₂ η₀ : ℝ, 0 < C₂ ∧ 0 < η₀ ∧ η₀ < 1 ∧
    ∀ η : ℝ, 0 < η → η ≤ η₀ →
    let gamma := 1 / (64 * ((n : ℝ) - 1))
    let tau := η ^ gamma
    0 < tau ∧ tau < 1 / 8 ∧
    ∀ (u : Domain n → Ambient q) (Du : Domain n → Gradient n q),
      MemW12Loc (ballDomain (0 : Domain n) 1) u Du →
      TakesValuesIn N (ballDomain (0 : Domain n) 1) u →
      IsLocallyEnergyMinimizing N (ballDomain (0 : Domain n) 1) u Du →
      dirichletEnergy Du (Metric.ball (0 : Domain n) 1) ≤ ENNReal.ofReal η →
      tau ^ (2 - (n : ℤ)) * (dirichletEnergy Du (Metric.ball (0 : Domain n) tau)).toReal ≤
        C₂ * (η ^ (1 / 4 - gamma * ((n : ℝ) - 2)) +
          η ^ (2 * gamma) + η ^ (1 / 8 - gamma * ((n : ℝ) - 1))) *
        (dirichletEnergy Du (Metric.ball (0 : Domain n) 1)).toReal := by
  obtain ⟨ρc, Qc, hFc, hComp⟩ := projectedCompetitor_complete
  obtain ⟨Cc, hCc, hCompn⟩ := hComp n hn
  obtain ⟨ρh, Qh, hFh, hHarm⟩ := harmonicReplacement_projectedEnergy
  obtain ⟨Ch, hCh, hHarmn⟩ := hHarm n hn
  obtain ⟨C₁, hC₁, hHarmN⟩ := hHarmn q N
  obtain ⟨Cs, hCs, hSmooth⟩ := uniformSmoothing_complete n hn
  let C₀ : ℝ := max Cc (max Ch Cs)
  let ρ : ℝ := min (ρc q N) (ρh q N)
  have hC₀ : 0 < C₀ := hCc.trans_le (le_max_left _ _)
  have hρ : 0 < ρ := lt_min (hFc q N).1 (hFh q N).1
  obtain ⟨b, _, _, _, _, _, _, _, _, _, _, _, hCutoff⟩ := decay_cutoff_complete
  obtain ⟨η₀, hη₀, hη₀one, hCutoffη⟩ := hCutoff n hn C₀ ρ hC₀ hρ
  let C₂ : ℝ := C₁ + C₁ * (2 : ℝ) ^ n + 50
  have hTwo : 0 ≤ (2 : ℝ) ^ n := pow_nonneg (by norm_num) n
  have hProd : 0 ≤ C₁ * (2 : ℝ) ^ n := mul_nonneg hC₁.le hTwo
  have hC₂ : 0 < C₂ := by dsimp only [C₂]; linarith only [hC₁, hProd]
  have hFirst : C₁ ≤ C₂ := by dsimp only [C₂]; linarith only [hProd]
  have hSecond : C₁ * (2 : ℝ) ^ n ≤ C₂ := by
    dsimp only [C₂]; linarith only [hC₁]
  have hThird : (50 : ℝ) ≤ C₂ := by dsimp only [C₂]; linarith only [hC₁, hProd]
  refine ⟨C₂, η₀, hC₂, hη₀, hη₀one, ?_⟩
  intro η hη hηsmall
  let gamma : ℝ := 1 / (64 * ((n : ℝ) - 1))
  let tau : ℝ := η ^ gamma
  let delta : ℝ := η ^ (1 / 8 : ℝ)
  obtain ⟨hGeometry, _, _, hMaps⟩ := hCutoffη η hη hηsmall
  obtain ⟨_, hηone, hhbar, hd, htau, _, _, _, _, hTube, hScale, _, _, hTau, _⟩ := hGeometry
  have hTauSmall : tau < 1 / 8 := by linarith only [hTau]
  refine ⟨htau, hTauSmall, ?_⟩
  intro u Du hu hN hmin hsmall
  have hfinite : dirichletEnergy Du (Metric.ball (0 : Domain n) 1) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hsmall
  have hEη := ENNReal.toReal_le_of_le_ofReal hη.le hsmall
  have hInt := (hu.memW12_unitBall_of_finiteEnergy N hN hfinite).integrable_hsNormSq
  let E : ℝ := (dirichletEnergy Du (Metric.ball (0 : Domain n) 1)).toReal
  have hE : 0 ≤ E := ENNReal.toReal_nonneg
  have hRoot (C : ℝ) (hC : C ≤ C₀) : Real.sqrt (C * η) < ρ :=
    (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hC hη.le)).trans_lt hTube
  have hTubeC : Real.sqrt (Cc * η) < ρc q N :=
    (hRoot Cc (le_max_left _ _)).trans_le (min_le_left _ _)
  have hTubeH : Real.sqrt (Ch * η) < ρh q N :=
    (hRoot Ch ((le_max_left _ _).trans (le_max_right _ _))).trans_le (min_le_right _ _)
  have hTubeS : Real.sqrt (Cs * η) < ρc q N :=
    (hRoot Cs ((le_max_right _ _).trans (le_max_right _ _))).trans_le (min_le_left _ _)
  obtain ⟨j, _, _, hTauTheta, hThetaUpper, hDeltaTheta, _, hQuarter, _, _,
    hShellFirst, hShellSecond, hhdelta, _, _, hs, _, _, hRadial, hValues,
    hOn, hOff, _, hDs⟩ := hMaps q N u Du hu hN hsmall
  let theta : ℝ := tau + (3 * (j : ℝ) - 2) * delta
  let beta : ℝ → ℝ := fun t => 1 - ∫ y in Iic t, b y
  let s : Domain n → ℝ := fun x => η ^ (1 / 4 : ℝ) * beta ((‖x‖ - theta) / delta)
  let m : Domain n → Ambient q := fun x =>
    ∫ y in Metric.ball (0 : Domain n) 1,
      fixedMollifierKernel n y • u (x - η ^ (1 / 4 : ℝ) • y)
  have hθ : 0 < theta := htau.trans hTauTheta
  have hθquarter : theta ≤ 1 / 4 := by linarith only [hQuarter, hd]
  have hHalf : theta + 2 * delta < 1 / 2 := hQuarter.trans (by norm_num)
  obtain ⟨_, _, _, _, _, _, _, _, hCompare⟩ :=
    hCompn q N η hη hηone hScale hTubeC theta delta s hd hDeltaTheta hHalf
      hs hRadial hValues hOn hOff hhdelta hDs u Du hu hN hmin hsmall
  obtain ⟨_, _, hPointH, hHarmonic⟩ :=
    hHarmN η hη hηone hScale hTubeH theta hθ hθquarter u Du hu hN hmin hsmall
  obtain ⟨_, hPointS, _⟩ := hSmooth q N u Du hu hN hmin hfinite ⟨_, hhbar⟩ hScale
  have hNearC (x : Domain n) (hx : x ∈ Metric.ball (0 : Domain n) (1 / 2 : ℝ)) :
      Metric.infDist (m x) N.carrierSet < ρc q N := by
    have hsq := (hPointS x hx).1
    change Metric.infDist (m x) N.carrierSet ^ 2 ≤ Cs * E at hsq
    have hbound := hsq.trans (mul_le_mul_of_nonneg_left hEη hCs.le)
    have hle : Metric.infDist (m x) N.carrierSet ≤ Real.sqrt (Cs * η) := by
      nlinarith only [hbound, Real.sq_sqrt (mul_nonneg hCs.le hη.le),
        Real.sqrt_nonneg (Cs * η), Metric.infDist_nonneg (x := m x) (s := N.carrierSet)]
    exact hle.trans_lt hTubeS
  have hEq : EqOn (Qc q N ∘ m) (Qh q N ∘ m)
      (Metric.ball (0 : Domain n) (1 / 2 : ℝ)) := by
    intro x hx
    obtain ⟨hc, heqc, _, _⟩ := (hFc q N).2.2.2.2.2 (m x) (hNearC x hx)
    obtain ⟨hh, _, heqh, _, _⟩ := hPointH x hx
    exact heqc.trans heqh.symm
  have hGradEq (x : Domain n) (hx : x ∈ Metric.ball (0 : Domain n) theta) :
      fderiv ℝ (Qc q N ∘ m) x = fderiv ℝ (Qh q N ∘ m) x := by
    have hxhalf : x ∈ Metric.ball (0 : Domain n) (1 / 2 : ℝ) :=
      Metric.ball_subset_ball (hθquarter.trans (by norm_num)) hx
    have hEvent : (Qc q N ∘ m) =ᶠ[𝓝 x] (Qh q N ∘ m) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hxhalf] with z hz
      exact hEq hz
    exact hEvent.fderiv_eq
  have hEnergyEq :
      (∫ x in Metric.ball (0 : Domain n) theta,
        hsNormSq (fun i => fderiv ℝ (Qc q N ∘ m) x (EuclideanSpace.single i 1))) =
      ∫ x in Metric.ball (0 : Domain n) theta,
        hsNormSq (fun i => fderiv ℝ (Qh q N ∘ m) x (EuclideanSpace.single i 1)) := by
    apply setIntegral_congr_fun measurableSet_ball
    intro x hx
    dsimp only
    rw [hGradEq x hx]
  rw [hEnergyEq] at hCompare
  have hShell := hShellFirst.trans hShellSecond
  have hInnerInt : IntegrableOn (fun x => hsNormSq (Du x))
      (Metric.ball (0 : Domain n) (theta + delta)) volume :=
    hInt.mono_set (Metric.ball_subset_ball (by linarith only [hQuarter, hd]))
  have hInner : (∫ x in Metric.ball (0 : Domain n) tau, hsNormSq (Du x)) ≤
      ∫ x in Metric.ball (0 : Domain n) (theta + delta), hsNormSq (Du x) :=
    setIntegral_mono_set hInnerInt (Eventually.of_forall fun x => hsNormSq_nonneg (Du x))
      (Eventually.of_forall (Metric.ball_subset_ball (by linarith only [hTauTheta, hd])))
  have hBound := hInner.trans (hCompare.trans (add_le_add hHarmonic
    (mul_le_mul_of_nonneg_left hShell (by norm_num : (0 : ℝ) ≤ 25 / 3))))
  have hθpow : theta ^ n ≤ (2 : ℝ) ^ n * tau ^ n := by
    simpa only [mul_pow] using pow_le_pow_left₀ hθ.le hThetaUpper.le n
  let p : ℝ := tau ^ (2 - (n : ℤ))
  have hp : 0 ≤ p := (zpow_pos htau _).le
  have hBound' : (∫ x in Metric.ball (0 : Domain n) tau, hsNormSq (Du x)) ≤
      C₁ * (η ^ (1 / 4 : ℝ) + (2 : ℝ) ^ n * tau ^ n) * E +
        50 * (delta / tau) * E := by
    refine hBound.trans ?_
    have hmain : C₁ * (η ^ (1 / 4 : ℝ) + theta ^ n) * E ≤
        C₁ * (η ^ (1 / 4 : ℝ) + (2 : ℝ) ^ n * tau ^ n) * E :=
      mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (add_le_add le_rfl hθpow) hC₁.le) hE
    convert add_le_add hmain (le_refl ((25 / 3 : ℝ) * (6 * delta / tau * E))) using 1; ring
  have hIntTau := hInt.mono_set (Metric.ball_subset_ball (hTauSmall.le.trans (by norm_num)))
  rw [dirichletEnergy_toReal hIntTau]
  have hpa : p * η ^ (1 / 4 : ℝ) = η ^ (1 / 4 - gamma * ((n : ℝ) - 2)) := by
    dsimp only [p, tau]
    rw [← Real.rpow_mul_intCast hη.le]
    simp only [Int.cast_sub, Int.cast_ofNat, Int.cast_natCast]
    rw [← Real.rpow_add hη]
    congr 1
    ring
  have hpb : p * tau ^ n = η ^ (2 * gamma) := by
    dsimp only [p, tau]
    rw [← Real.rpow_mul_intCast hη.le, ← Real.rpow_mul_natCast hη.le]
    simp only [Int.cast_sub, Int.cast_ofNat, Int.cast_natCast]
    rw [← Real.rpow_add hη]
    congr 1
    ring
  have hpc : p * delta / tau = η ^ (1 / 8 - gamma * ((n : ℝ) - 1)) := by
    dsimp only [p, delta, tau]
    rw [← Real.rpow_mul_intCast hη.le]
    simp only [Int.cast_sub, Int.cast_ofNat, Int.cast_natCast]
    rw [← Real.rpow_add hη, ← Real.rpow_sub hη]
    congr 1
    ring
  calc
    _ ≤ p * (C₁ * (η ^ (1 / 4 : ℝ) + (2 : ℝ) ^ n * tau ^ n) * E +
        50 * (delta / tau) * E) := mul_le_mul_of_nonneg_left hBound' hp
    _ = C₁ * (p * η ^ (1 / 4 : ℝ)) * E +
        (C₁ * (2 : ℝ) ^ n) * (p * tau ^ n) * E + 50 * (p * delta / tau) * E := by ring
    _ = C₁ * η ^ (1 / 4 - gamma * ((n : ℝ) - 2)) * E +
        (C₁ * (2 : ℝ) ^ n) * η ^ (2 * gamma) * E +
        50 * η ^ (1 / 8 - gamma * ((n : ℝ) - 1)) * E := by rw [hpa, hpb, hpc]
    _ ≤ C₂ * η ^ (1 / 4 - gamma * ((n : ℝ) - 2)) * E +
        C₂ * η ^ (2 * gamma) * E + C₂ * η ^ (1 / 8 - gamma * ((n : ℝ) - 1)) * E :=
      add_le_add (add_le_add
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hFirst
          (Real.rpow_pos_of_pos hη _).le) hE)
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hSecond
          (Real.rpow_pos_of_pos hη _).le) hE))
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hThird
          (Real.rpow_pos_of_pos hη _).le) hE)
    _ = _ := by ring

end HarmonicMaps
end
