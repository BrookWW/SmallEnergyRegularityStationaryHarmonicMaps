module

public import HarmonicMaps.Analysis.VariableMollification
public import HarmonicMaps.Analysis.SobolevPostcomposition
public import HarmonicMaps.Analysis.ProjectedCompetitorComparison
public import HarmonicMaps.Analysis.DirichletSmoothData
public import HarmonicMaps.Frozen.UniformSmoothing
public import HarmonicMaps.Frozen.TubularProjection

/-!
# Complete admissible projected variable-smoothing competitor

The literal tensor columns of variable smoothing pass through the genuine
ambient projection chain rule. Positive scales use the uniform tube-distance
bound; zero scales use the original almost-everywhere target values. The
two plateaux, exact shell factor and native zero-boundary difference yield
the source minimality comparison for the original displayed gradient.
-/

public section

open MeasureTheory Set
open scoped ENNReal ContDiff BigOperators

namespace HarmonicMaps

private theorem projection_extension_spec (q : ℕ) (N : CompactSmoothEmbeddedTarget q) :
    ∃ (r : ℝ) (Q : Ambient q → Ambient q),
      0 < r ∧ r ≤ tubularBaseRadius q N ∧ ContDiff ℝ ∞ Q ∧
      (∃ L : ℝ, 0 < L ∧ ∀ z, ‖fderiv ℝ Q z‖ ≤ L) ∧
      (∀ z ∈ N.carrierSet, Q z = z) ∧
      ∀ z : Ambient q, Metric.infDist z N.carrierSet < r →
        ∃ hz : z ∈ tubularTube q N,
          Q z = (tubularProjection q N ⟨z, hz⟩).val ∧
          Q z ∈ N.carrierSet ∧ ‖fderiv ℝ Q z‖ ≤ 2 := by
  obtain ⟨r, hr, hrbase, hsub, _, _, hfixed, _, hD, _, _, _, _, Q, hQ, hQeq,
    L, _, hL, _, hQL, _⟩ := tubularProjection_complete q N
  have hnear (z : Ambient q) (hz : Metric.infDist z N.carrierSet < r) :
      ∃ ht : z ∈ tubularTube q N,
        Q z = (tubularProjection q N ⟨z, ht⟩).val ∧
        Q z ∈ N.carrierSet ∧ ‖fderiv ℝ Q z‖ ≤ 2 := by
    let V : Set (Ambient q) := {w | Metric.infDist w N.carrierSet < r}
    have hV : IsOpen V := isOpen_lt (Metric.continuous_infDist_pt N.carrierSet) continuous_const
    have hVsub : V ⊆ tubularTube q N := by
      intro w hw
      change Metric.infDist w N.carrierSet < 2 * tubularBaseRadius q N
      change Metric.infDist w N.carrierSet < r at hw
      linarith only [hw, hr, hrbase]
    have ht := hVsub hz
    have heq := hQeq ⟨z, ht⟩ hz
    have hjet := (tubularProjectionDerivative_characterization q N).1
      ⟨z, ht⟩ V Q hV hz hVsub hQ.contDiffOn (fun w hw => hQeq w hw)
    have hwide : z ∈ {w | Metric.infDist w N.carrierSet < 2 * r} := by
      change Metric.infDist z N.carrierSet < 2 * r
      linarith only [hz, hr]
    refine ⟨ht, heq, heq ▸ (tubularProjection q N ⟨z, ht⟩).property, ?_⟩
    rw [hjet]
    exact hD ⟨z, hwide⟩
  refine ⟨r, Q, hr, hrbase, hQ, ⟨L, hL, hQL⟩, ?_, hnear⟩
  intro z hz
  obtain ⟨hp, hP, _⟩ := hfixed ⟨z, hz⟩
  have hzsmall : Metric.infDist z N.carrierSet < r := by
    rw [Metric.infDist_zero_of_mem hz]
    exact hr
  have hEq := hQeq ⟨z, hsub hp⟩ hzsmall
  rw [hP] at hEq
  exact hEq

/-- The actual projected variable integral is an admissible target-valued
competitor with both source plateaux, shell factor 25/3 and the original
minimality comparison. All smoothing and boundary premises are produced. -/
theorem projectedCompetitor_complete :
    ∃ ρ : ∀ (q : ℕ), CompactSmoothEmbeddedTarget q → ℝ,
    ∃ Q : ∀ (q : ℕ), CompactSmoothEmbeddedTarget q → Ambient q → Ambient q,
    (∀ (q : ℕ) (N : CompactSmoothEmbeddedTarget q),
      0 < ρ q N ∧ ρ q N ≤ tubularBaseRadius q N ∧ ContDiff ℝ ∞ (Q q N) ∧
      (∃ L : ℝ, 0 < L ∧ ∀ z, ‖fderiv ℝ (Q q N) z‖ ≤ L) ∧
      (∀ z ∈ N.carrierSet, Q q N z = z) ∧
      ∀ z : Ambient q, Metric.infDist z N.carrierSet < ρ q N →
        ∃ hz : z ∈ tubularTube q N,
          Q q N z = (tubularProjection q N ⟨z, hz⟩).val ∧
          Q q N z ∈ N.carrierSet ∧ ‖fderiv ℝ (Q q N) z‖ ≤ 2) ∧
    ∀ (n : ℕ), 2 ≤ n →
    ∃ C₀ : ℝ, 0 < C₀ ∧
    ∀ (q : ℕ) (N : CompactSmoothEmbeddedTarget q),
    ∀ (η : ℝ), 0 < η → η < 1 → η ^ (1 / 4 : ℝ) ≤ 1 / 4 →
      Real.sqrt (C₀ * η) < ρ q N →
    ∀ (theta delta : ℝ) (s : Domain n → ℝ),
      0 < delta → delta < theta → theta + 2 * delta < 1 / 2 →
      ContDiff ℝ ∞ s → (∀ x z : Domain n, ‖x‖ = ‖z‖ → s x = s z) →
      (∀ x, 0 ≤ s x ∧ s x ≤ η ^ (1 / 4 : ℝ)) →
      (∀ x ∈ Metric.ball (0 : Domain n) theta, s x = η ^ (1 / 4 : ℝ)) →
      (∀ x ∉ Metric.ball (0 : Domain n) (theta + delta), s x = 0) →
      η ^ (1 / 4 : ℝ) ≤ delta → (∀ x, ‖fderiv ℝ s x‖ ≤ 1 / 4) →
    ∀ (u : Domain n → Ambient q) (Du : Domain n → Gradient n q),
      MemW12Loc (ballDomain (0 : Domain n) 1) u Du →
      TakesValuesIn N (ballDomain (0 : Domain n) 1) u →
      IsLocallyEnergyMinimizing N (ballDomain (0 : Domain n) 1) u Du →
      dirichletEnergy Du (Metric.ball (0 : Domain n) 1) ≤ ENNReal.ofReal η →
    let U := Metric.ball (0 : Domain n) (theta + 2 * delta)
    let A := Metric.ball (0 : Domain n) (theta + delta) \ Metric.closedBall 0 theta
    let Aplus := U \ Metric.closedBall 0 (theta - delta)
    let m : Domain n → Ambient q := fun x =>
      ∫ y in Metric.ball (0 : Domain n) 1,
        fixedMollifierKernel n y • u (x - η ^ (1 / 4 : ℝ) • y)
    let T : Domain n → Ambient q := fun x =>
      ∫ y in Metric.ball (0 : Domain n) 1,
        fixedMollifierKernel n y • u (x - s x • y)
    let DT : Domain n → Gradient n q := fun x i =>
      ∫ y in Metric.ball (0 : Domain n) 1,
        fixedMollifierKernel n y • ∑ j : Fin n,
          ((ContinuousLinearMap.id ℝ (Domain n) - (fderiv ℝ s x).smulRight y)
            (EuclideanSpace.single i 1)) j • Du (x - s x • y) j
    let u₀ := Q q N ∘ T
    let Du₀ : Domain n → Gradient n q := fun x i => fderiv ℝ (Q q N) (T x) (DT x i)
    MemW12 (ballDomain (0 : Domain n) (theta + 2 * delta)) u₀ Du₀ ∧
    TakesValuesIn N (ballDomain (0 : Domain n) (theta + 2 * delta)) u₀ ∧
    (∀ x ∈ Metric.ball (0 : Domain n) theta, u₀ x = (Q q N ∘ m) x) ∧
    (∀ᵐ x ∂volume.restrict (U \ Metric.ball 0 (theta + delta)), u₀ x = u x) ∧
    (∀ᵐ x ∂volume.restrict U, ‖fderiv ℝ (Q q N) (T x)‖ ≤ 2) ∧
    (∫ x in A, hsNormSq (Du₀ x)) ≤ (25 / 3 : ℝ) * ∫ x in Aplus, hsNormSq (Du x) ∧
    HasZeroBoundaryDifference (ballDomain (0 : Domain n) (theta + 2 * delta)) u Du u₀ Du₀ ∧
    dirichletEnergy Du U ≤ dirichletEnergy Du₀ U ∧
    (∫ x in Metric.ball (0 : Domain n) (theta + delta), hsNormSq (Du x)) ≤
      (∫ x in Metric.ball (0 : Domain n) theta,
        hsNormSq (fun i => fderiv ℝ (Q q N ∘ m) x (EuclideanSpace.single i 1))) +
      (25 / 3 : ℝ) * ∫ x in Aplus, hsNormSq (Du x) := by
  classical
  choose ρ Q hρ hρbase hQ hQL hQfix hQnear using projection_extension_spec
  refine ⟨ρ, Q, fun q N => ⟨hρ q N, hρbase q N, hQ q N, hQL q N,
    hQfix q N, hQnear q N⟩, ?_⟩
  intro n hn
  obtain ⟨C₀, hC₀, hSmooth⟩ := uniformSmoothing_complete n hn
  refine ⟨C₀, hC₀, ?_⟩
  intro q N η hη _hηone hscale htube theta delta s hd ht hhalf hs hradial
    hvalues hon hoff hhd hDs u Du hu hN hmin hsmall
  let U : Set (Domain n) := Metric.ball 0 (theta + 2 * delta)
  let A : Set (Domain n) := Metric.ball 0 (theta + delta) \ Metric.closedBall 0 theta
  let Aplus : Set (Domain n) := U \ Metric.closedBall 0 (theta - delta)
  let m : Domain n → Ambient q := fun x =>
    ∫ y in Metric.ball (0 : Domain n) 1, fixedMollifierKernel n y • u (x - η ^ (1 / 4 : ℝ) • y)
  let T : Domain n → Ambient q := fun x =>
    ∫ y in Metric.ball (0 : Domain n) 1, fixedMollifierKernel n y • u (x - s x • y)
  let DT : Domain n → Gradient n q := fun x i =>
    ∫ y in Metric.ball (0 : Domain n) 1, fixedMollifierKernel n y • ∑ j : Fin n,
      ((ContinuousLinearMap.id ℝ (Domain n) - (fderiv ℝ s x).smulRight y)
        (EuclideanSpace.single i 1)) j • Du (x - s x • y) j
  let u₀ := Q q N ∘ T
  let Du₀ : Domain n → Gradient n q := fun x i => fderiv ℝ (Q q N) (T x) (DT x i)
  have ht0 : 0 < theta := hd.trans ht
  have hR : 0 < theta + 2 * delta := by linarith only [ht0, hd]
  have hclosed : Metric.closedBall (0 : Domain n) (theta + 2 * delta) ⊆
      Metric.ball 0 1 := Metric.closedBall_subset_ball (by linarith only [hhalf])
  have hUhalf : U ⊆ Metric.ball (0 : Domain n) (1 / 2 : ℝ) :=
    Metric.ball_subset_ball hhalf.le
  have huU := hu.memW12_ball hclosed
  have hNu : TakesValuesIn N (ballDomain (0 : Domain n) (theta + 2 * delta)) u :=
    ae_restrict_of_ae_restrict_of_subset (Metric.ball_subset_closedBall.trans hclosed) hN
  have hfinite : dirichletEnergy Du (Metric.ball (0 : Domain n) 1) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hsmall
  have hEη : (dirichletEnergy Du (Metric.ball (0 : Domain n) 1)).toReal ≤ η :=
    ENNReal.toReal_le_of_le_ofReal hη.le hsmall
  obtain ⟨hTW, _, _, _, _, _, _, _, _, _, hShellT, hTzero, _⟩ :=
    variableMollification_sobolev_estimates hd ht hhalf hs hradial hvalues hon hoff
      hhd hDs (le_rfl : (1 / 4 : ℝ) ≤ 1 / 4) u Du huU
  have hTW' : MemW12 (ballDomain (0 : Domain n) (theta + 2 * delta)) T DT := hTW
  obtain ⟨L, _, hDglobal⟩ := hQL q N
  have hW : MemW12 (ballDomain (0 : Domain n) (theta + 2 * delta)) u₀ Du₀ :=
    hTW'.postcompose hR (Q q N) (hQ q N) L hDglobal
  have hpositive (x : Domain n) (hx : x ∈ U) (hpos : 0 < s x) :
      Metric.infDist (T x) N.carrierSet < ρ q N := by
    obtain ⟨_, hpoint, _⟩ := hSmooth q N u Du hu hN hmin hfinite ⟨s x, hpos⟩
      ((hvalues x).2.trans hscale)
    have hdistance := (hpoint x (hUhalf hx)).1
    change Metric.infDist (T x) N.carrierSet ^ 2 ≤
      C₀ * (dirichletEnergy Du (Metric.ball (0 : Domain n) 1)).toReal at hdistance
    have hsq := hdistance.trans (mul_le_mul_of_nonneg_left hEη hC₀.le)
    have hroot := Real.sq_sqrt (mul_nonneg hC₀.le hη.le)
    have hle : Metric.infDist (T x) N.carrierSet ≤ Real.sqrt (C₀ * η) := by
      nlinarith only [hsq, hroot, Real.sqrt_nonneg (C₀ * η),
        Metric.infDist_nonneg (x := T x) (s := N.carrierSet)]
    exact hle.trans_lt htube
  have hTdist : ∀ᵐ x ∂volume.restrict U, Metric.infDist (T x) N.carrierSet < ρ q N := by
    filter_upwards [ae_restrict_mem measurableSet_ball, hNu] with x hx hxN
    by_cases hz : s x = 0
    · rw [show T x = u x from hTzero x hx hz, Metric.infDist_zero_of_mem hxN]
      exact hρ q N
    · exact hpositive x hx (lt_of_le_of_ne (hvalues x).1 (Ne.symm hz))
  have hNv : TakesValuesIn N (ballDomain (0 : Domain n) (theta + 2 * delta)) u₀ := by
    filter_upwards [hTdist] with x hx
    exact (hQnear q N (T x) hx).choose_spec.2.1
  have hDnear : ∀ᵐ x ∂volume.restrict U, ‖fderiv ℝ (Q q N) (T x)‖ ≤ 2 := by
    filter_upwards [hTdist] with x hx
    exact (hQnear q N (T x) hx).choose_spec.2.2
  have hinner (x : Domain n) (hx : x ∈ Metric.ball (0 : Domain n) theta) :
      u₀ x = (Q q N ∘ m) x := by
    change Q q N (T x) = Q q N (m x)
    congr 1
    dsimp only [T, m]
    rw [hon x hx]
  have houter : ∀ᵐ x ∂volume.restrict (U \ Metric.ball 0 (theta + delta)), u₀ x = u x := by
    filter_upwards [ae_restrict_mem (measurableSet_ball.diff measurableSet_ball),
      ae_restrict_of_ae_restrict_of_subset (sdiff_subset :
        U \ Metric.ball 0 (theta + delta) ⊆ U) hNu] with x hx hxN
    change Q q N (T x) = u x
    rw [show T x = u x from hTzero x hx.1 (hoff x hx.2)]
    exact hQfix q N (u x) hxN
  have hShell : (∫ x in A, hsNormSq (Du₀ x)) ≤
      (25 / 3 : ℝ) * ∫ x in Aplus, hsNormSq (Du x) := by
    have hpoint : ∀ᵐ x ∂volume.restrict A, hsNormSq (Du₀ x) ≤ 4 * hsNormSq (DT x) := by
      filter_upwards [ae_restrict_of_ae_restrict_of_subset
        (sdiff_subset.trans (Metric.ball_subset_ball (by linarith only [hd]) :
          Metric.ball (0 : Domain n) (theta + delta) ⊆ U)) hDnear] with x hx
      unfold hsNormSq
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i _
      have hb : ‖Du₀ x i‖ ≤ 2 * ‖DT x i‖ :=
        (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_right hx (norm_nonneg _))
      nlinarith only [hb, norm_nonneg (Du₀ x i), norm_nonneg (DT x i)]
    have hASub : A ⊆ U := sdiff_subset.trans (Metric.ball_subset_ball (by linarith only [hd]))
    have hInt := integral_mono_ae (hW.integrable_hsNormSq.mono_set hASub)
      ((hTW'.integrable_hsNormSq.mono_set hASub).const_mul 4) hpoint
    rw [integral_const_mul] at hInt
    exact hInt.trans ((mul_le_mul_of_nonneg_left hShellT
      (by norm_num : (0 : ℝ) ≤ 4)).trans_eq (by ring))
  have hcollarSub : U \ Metric.closedBall 0 (theta + delta) ⊆
      U \ Metric.ball 0 (theta + delta) := by
    intro x hx
    exact ⟨hx.1, fun h => hx.2 (Metric.ball_subset_closedBall h)⟩
  have hcollar : u =ᵐ[volume.restrict (U \ Metric.closedBall 0 (theta + delta))] u₀ := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hcollarSub houter] with x hx
    exact hx.symm
  obtain ⟨hzero, hminimal, hcompare⟩ := projectedCompetitor_collar_comparison N
    u u₀ Du Du₀ theta delta hd ht hhalf huU hW hNv hmin hcollar
  obtain ⟨hm, _⟩ := hSmooth q N u Du hu hN hmin hfinite
    ⟨η ^ (1 / 4 : ℝ), Real.rpow_pos_of_pos hη _⟩ hscale
  have hpm : ContDiffOn ℝ ∞ (Q q N ∘ m) (Metric.ball (0 : Domain n) (3 / 4 : ℝ)) :=
    (hQ q N).contDiffOn.comp hm (mapsTo_univ _ _)
  have hpW := dirichlet_smoothData_memW12 ⟨theta, ht0⟩ _ Metric.isOpen_ball
    (Metric.closedBall_subset_ball (by linarith only [hhalf, hd] : theta < 3 / 4))
    (Q q N ∘ m) hpm
  have hinnerSub : Metric.ball (0 : Domain n) theta ⊆ U :=
    Metric.ball_subset_ball (by linarith only [hd])
  have hgradEq := (hW.1.mono hinnerSub).ae_eq_of_ae_eq_map hpW.1
    (show u₀ =ᵐ[volume.restrict (Metric.ball (0 : Domain n) theta)] (Q q N ∘ m) from by
      filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
      exact hinner x hx)
  have hinnerEnergy := integral_congr_ae (hgradEq.fun_comp hsNormSq)
  change (∫ x in Metric.ball (0 : Domain n) theta, hsNormSq (Du₀ x)) =
    (∫ x in Metric.ball (0 : Domain n) theta,
      hsNormSq (fun i => fderiv ℝ (Q q N ∘ m) x (EuclideanSpace.single i 1))) at hinnerEnergy
  have hsmallSub : Metric.ball (0 : Domain n) (theta + delta) ⊆ U :=
    Metric.ball_subset_ball (by linarith only [hd])
  have hsplit := ball_integral_split_closed_collar ht0
    (by linarith only [hd] : theta < theta + delta) (fun x => hsNormSq (Du₀ x))
    (hW.integrable_hsNormSq.mono_set hsmallSub)
  rw [hsplit, hinnerEnergy] at hcompare
  exact ⟨hW, hNv, hinner, houter, hDnear, hShell, hzero, hminimal,
    hcompare.trans (add_le_add le_rfl hShell)⟩

end HarmonicMaps
end
