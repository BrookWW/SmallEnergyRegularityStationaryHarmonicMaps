module

public import HolderToCK.Analysis.Harmonic.SmoothReplacement
public import HolderToCK.Analysis.Harmonic.ReplacementLimits
public import HolderToCK.Analysis.ZeroBoundaryClosure
public import HolderToCK.Analysis.ContinuousMollification
public import HolderToCK.Analysis.Poisson.WeakHarmonicSmooth
public import HarmonicMaps.Analysis.InteriorSobolevApproximation
public import HarmonicMaps.Analysis.SobolevAECongruence
public import HarmonicMaps.Analysis.AffineZeroBoundary
public import Mathlib.Analysis.Normed.Module.Ball.Pointwise

/-! # Harmonic replacement of a continuous Sobolev datum

The smooth Poisson replacements of the actual interior mollifications converge
uniformly on the closed ball and strongly in each L2 gradient column. Their
native zero-boundary differences pass to the graph limit. The same continuous
limit is weakly harmonic and hence smooth in the open ball.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped ContDiff Topology ENNReal

namespace HolderToCK

theorem exists_larger_closedBall_subset_open {n : ℕ} (Ω : OpenDomain n)
    (a : Domain n) (r : PositiveRadius) (hclosed : Metric.closedBall a r.val ⊆ Ω.val) :
    ∃ R : ℝ, r.val < R ∧ Metric.closedBall a R ⊆ Ω.val := by
  obtain ⟨δ, hδ, hδsub⟩ := (isCompact_closedBall a r.val).exists_cthickening_subset_open
    Ω.property hclosed
  rw [cthickening_closedBall hδ.le r.property.le a] at hδsub
  exact ⟨δ + r.val, by linarith only [hδ], hδsub⟩

theorem sobolev_harmonic_replacement_mollification_limit_centered {n q : ℕ}
    (hn : 2 ≤ n) (r : PositiveRadius) {R : ℝ} (hrR : r.val < R)
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12 (ballDomain (0 : Domain n) R) u Du)
    (hcont : ContinuousOn u (Metric.ball (0 : Domain n) R)) :
    let scale : ℕ → PositiveRadius := fun k =>
      ⟨(R - r.val) / ((k : ℝ) + 1), by positivity⟩
    let m : ℕ → Domain n → Ambient q := fun k =>
      euclideanMollification (ballDomain (0 : Domain n) R) u hu.integrable_ball (scale k)
    ∃ w : Domain n → Ambient q, ∃ Dw : Domain n → Gradient n q,
      ∃ W : ℕ → Domain n → Ambient q,
      ContinuousOn w (Metric.closedBall (0 : Domain n) r.val) ∧
      (∀ x ∈ Metric.sphere (0 : Domain n) r.val, w x = u x) ∧
      MemW12 (ballDomain (0 : Domain n) r.val) w Dw ∧
      HasZeroBoundaryValues (ballDomain (0 : Domain n) r.val) (u - w)
        (fun x i => Du x i - Dw x i) ∧
      WeakPoissonOn (ballDomain (0 : Domain n) r.val) Dw (fun _ => 0) ∧
      (∀ k, ContDiffOn ℝ ∞ (W k) (Metric.closedBall (0 : Domain n) r.val)) ∧
      (∀ k x, x ∈ Metric.sphere (0 : Domain n) r.val → W k x = m k x) ∧
      (∀ k x, x ∈ Metric.ball (0 : Domain n) r.val → Laplacian.laplacian (W k) x = 0) ∧
      (∀ k, MemW12 (ballDomain (0 : Domain n) r.val) (W k)
        (fun x i => fderiv ℝ (W k) x (EuclideanSpace.single i 1))) ∧
      (∀ k, HasZeroBoundaryValues (ballDomain (0 : Domain n) r.val) (m k - W k)
        (fun x i => fderiv ℝ (m k) x (EuclideanSpace.single i 1) -
          fderiv ℝ (W k) x (EuclideanSpace.single i 1))) ∧
      (∀ k, WeakPoissonOn (ballDomain (0 : Domain n) r.val)
        (fun x i => fderiv ℝ (W k) x (EuclideanSpace.single i 1)) (fun _ => 0)) ∧
      TendstoUniformlyOn W w atTop (Metric.closedBall (0 : Domain n) r.val) ∧
      (∀ i : Fin n, Tendsto (fun k => eLpNorm
        (fun x => fderiv ℝ (W k) x (EuclideanSpace.single i 1) - Dw x i) 2
        (volume.restrict (Metric.ball (0 : Domain n) r.val))) atTop (𝓝 0)) := by
  classical
  let scale : ℕ → PositiveRadius := fun k =>
    ⟨(R - r.val) / ((k : ℝ) + 1), by positivity⟩
  let m : ℕ → Domain n → Ambient q := fun k =>
    euclideanMollification (ballDomain (0 : Domain n) R) u hu.integrable_ball (scale k)
  have hm (k : ℕ) : ContDiff ℝ ∞ (m k) :=
    euclideanMollification_contDiff _ u hu.integrable_ball (scale k)
  have hscale : Tendsto (fun k => (scale k).val) atTop (𝓝 0) := by
    simpa only [scale, div_eq_mul_inv, one_mul, mul_zero] using
      (tendsto_const_nhds (x := R - r.val)).mul tendsto_one_div_add_atTop_nhds_zero_nat
  have hscaleFilter : Tendsto scale atTop
      (comap (fun h : PositiveRadius => h.val) (𝓝 (0 : ℝ))) :=
    tendsto_comap_iff.mpr hscale
  have hmW (k : ℕ) : MemW12 (ballDomain (0 : Domain n) r.val) (m k)
      (fun x i => fderiv ℝ (m k) x (EuclideanSpace.single i 1)) :=
    dirichlet_smoothData_memW12 r univ isOpen_univ (subset_univ _) (m k) (hm k).contDiffOn
  have hclosed : Metric.closedBall (0 : Domain n) r.val ⊆ Metric.ball 0 R :=
    Metric.closedBall_subset_ball hrR
  have huSmall := hu.to_memW12Loc.memW12_ball hclosed
  have hmL2 : Tendsto (fun k => eLpNorm (m k - u) 2
      (volume.restrict (Metric.ball (0 : Domain n) r.val))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, m, Pi.sub_def] using
      (hu.tendsto_eLpNorm_mollification_inner_ball hrR).comp hscaleFilter
  have hDmL2 (i : Fin n) : Tendsto (fun k => eLpNorm
      (fun x => fderiv ℝ (m k) x (EuclideanSpace.single i 1) - Du x i) 2
      (volume.restrict (Metric.ball (0 : Domain n) r.val))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, m, coordinateDerivative] using
      (hu.tendsto_eLpNorm_mollification_column_inner_ball hrR i).comp hscaleFilter
  let s : ℝ := (R + r.val) / 2
  have hrs : r.val < s := by dsimp only [s]; linarith only [hrR]
  have hsR : s < R := by dsimp only [s]; linarith only [hrR]
  have hclosedS : Metric.closedBall (0 : Domain n) s ⊆ Metric.ball 0 R :=
    Metric.closedBall_subset_ball hsR
  have hmUniform : TendstoUniformlyOn m u atTop (Metric.closedBall (0 : Domain n) r.val) :=
    euclideanMollification_tendstoUniformlyOn_closedBall_of_continuous
      (ballDomain (0 : Domain n) R) u hu.integrable_ball 0 hrs hclosedS
      (hcont.mono hclosedS) scale hscale
  choose W hWs hWb hWh hWW hWzero hWEq using
    fun k => smooth_harmonic_replacement_exists hn r (m k) (hm k)
  have hWCauchy : UniformCauchySeqOn W atTop (Metric.closedBall (0 : Domain n) r.val) := by
    apply Metric.uniformCauchySeqOn_iff.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.uniformCauchySeqOn_iff.mp hmUniform.uniformCauchySeqOn
      (ε / 2) (half_pos hε)
    refine ⟨N, fun k hk l hl x hx => ?_⟩
    have hbound : ∀ y ∈ Metric.sphere (0 : Domain n) r.val,
        ‖m k y - m l y‖ ≤ ε / 2 := by
      intro y hy
      exact (show ‖m k y - m l y‖ < ε / 2 by
        simpa only [dist_eq_norm] using hN k hk l hl y (Metric.sphere_subset_closedBall hy)).le
    have hWbound := smooth_harmonic_replacements_sup_contraction hn r
      (m k) (m l) (W k) (W l) (hm k) (hm l) (hWs k) (hWs l)
      (hWb k) (hWb l) (hWh k) (hWh l) (ε / 2) hbound x hx
    rw [dist_eq_norm]
    exact hWbound.trans_lt (half_lt_self hε)
  obtain ⟨v, hv⟩ := exists_uniform_limit_on_carrier hWCauchy
  let w : Domain n → Ambient q := fun x =>
    if hx : x ∈ Metric.closedBall (0 : Domain n) r.val then v ⟨x, hx⟩ else u x
  have hWUniform : TendstoUniformlyOn W w atTop (Metric.closedBall (0 : Domain n) r.val) := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    have hsub := Metric.tendstoUniformlyOn_iff.mp (hv.tendstoUniformlyOn (s := univ)) ε hε
    filter_upwards [hsub] with k hk x hx
    simpa only [w, dif_pos hx] using hk ⟨x, hx⟩ (mem_univ _)
  have hwcont : ContinuousOn w (Metric.closedBall (0 : Domain n) r.val) :=
    hWUniform.continuousOn (Frequently.of_forall (fun k => (hWs k).continuousOn))
  have hwLp := continuousOn_closedBall_memLp_two (0 : Domain n) r.val hwcont
  let μ := volume.restrict (Metric.ball (0 : Domain n) r.val)
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  letI : IsFiniteMeasure (volume.restrict (ballDomain (0 : Domain n) r.val).val) :=
    isFiniteMeasure_restrict.mpr measure_ball_ne_top
  have hwL2 : Tendsto (fun k => eLpNorm (W k - w) 2 μ) atTop (𝓝 0) :=
    tendsto_L2_of_tendstoUniformlyOn volume measurableSet_ball
      (fun k => (hWW k).2.1) hwLp (hWUniform.mono Metric.ball_subset_closedBall)
  obtain ⟨Dw, hDw, hDwL2⟩ := exists_columns_L2_limit_of_hs_energy_contraction μ
    (fun k i => (hmW k).2.2 i) (fun k i => (hWW k).2.2 i) huSmall.2.2 hDmL2
    (fun k l => smooth_harmonic_replacements_gradient_contraction hn r
      (m k) (m l) (W k) (W l) (hm k) (hm l) (hWs k) (hWs l)
      (hWb k) (hWb l) (hWh k) (hWh l))
  have hwW : MemW12 (ballDomain (0 : Domain n) r.val) w Dw :=
    MemW12.of_L2_limit hWW hwLp hDw hwL2 hDwL2
  have hwEq : WeakPoissonOn (ballDomain (0 : Domain n) r.val) Dw (fun _ => 0) :=
    WeakPoissonOn.harmonic_of_columns_L2_limit hWEq (fun k i => (hWW k).2.2 i) hDw hDwL2
  have hzero : HasZeroBoundaryValues (ballDomain (0 : Domain n) r.val) (u - w)
      (fun x i => Du x i - Dw x i) := by
    apply hasZeroBoundaryValues_of_L2_limit_ball 0 r.val hWzero
      (huSmall.2.1.sub hwLp) (fun i => (huSmall.2.2 i).sub (hDw i))
    · have hsum : Tendsto (fun k => eLpNorm (m k - u) 2 μ + eLpNorm (W k - w) 2 μ)
          atTop (𝓝 0) := by simpa only [add_zero] using hmL2.add hwL2
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
        (fun _ => bot_le)
      intro k
      dsimp only
      have heq : (m k - W k) - (u - w) = (m k - u) - (W k - w) := by abel
      rw [heq]
      exact eLpNorm_sub_le ((hmW k).2.1.sub huSmall.2.1).aestronglyMeasurable
        ((hWW k).2.1.sub hwLp).aestronglyMeasurable (by norm_num)
    · intro i
      have hsum : Tendsto (fun k => eLpNorm
          (fun x => fderiv ℝ (m k) x (EuclideanSpace.single i 1) - Du x i) 2 μ +
          eLpNorm (fun x => fderiv ℝ (W k) x (EuclideanSpace.single i 1) - Dw x i) 2 μ)
          atTop (𝓝 0) := by simpa only [add_zero] using (hDmL2 i).add (hDwL2 i)
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
        (fun _ => bot_le)
      intro k
      dsimp only
      have heq : (fun x =>
          (fderiv ℝ (m k) x (EuclideanSpace.single i 1) -
            fderiv ℝ (W k) x (EuclideanSpace.single i 1)) - (Du x i - Dw x i)) =
          (fun x => fderiv ℝ (m k) x (EuclideanSpace.single i 1) - Du x i) -
            (fun x => fderiv ℝ (W k) x (EuclideanSpace.single i 1) - Dw x i) := by
        funext x
        simp only [Pi.sub_apply]
        abel
      simp only [Pi.sub_apply]
      rw [heq]
      exact eLpNorm_sub_le ((hmW k).2.2 i |>.sub (huSmall.2.2 i)).aestronglyMeasurable
        ((hWW k).2.2 i |>.sub (hDw i)).aestronglyMeasurable (by norm_num)
  have hboundary : ∀ x ∈ Metric.sphere (0 : Domain n) r.val, w x = u x := by
    intro x hx
    have hwAt := hWUniform.tendsto_at (Metric.sphere_subset_closedBall hx)
    have hmAt := hmUniform.tendsto_at (Metric.sphere_subset_closedBall hx)
    exact tendsto_nhds_unique hwAt (hmAt.congr (fun k => (hWb k x hx).symm))
  exact ⟨w, Dw, W, hwcont, hboundary, hwW, hzero, hwEq,
    hWs, hWb, hWh, hWW, hWzero, hWEq, hWUniform, hDwL2⟩

theorem continuous_sobolev_harmonic_replacement_centered {n q : ℕ}
    (hn : 2 ≤ n) (r : PositiveRadius) {R : ℝ} (hrR : r.val < R)
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12 (ballDomain (0 : Domain n) R) u Du)
    (hcont : ContinuousOn u (Metric.ball (0 : Domain n) R)) :
    ∃ w : Domain n → Ambient q,
      ContinuousOn w (Metric.closedBall (0 : Domain n) r.val) ∧
      (∀ x ∈ Metric.sphere (0 : Domain n) r.val, w x = u x) ∧
      ContDiffOn ℝ ∞ w (Metric.ball (0 : Domain n) r.val) ∧
      (∀ x ∈ Metric.ball (0 : Domain n) r.val, Laplacian.laplacian w x = 0) ∧
      MemW12 (ballDomain (0 : Domain n) r.val) w
        (fun x i => fderiv ℝ w x (EuclideanSpace.single i 1)) ∧
      HasZeroBoundaryValues (ballDomain (0 : Domain n) r.val) (u - w)
        (fun x i => Du x i - fderiv ℝ w x (EuclideanSpace.single i 1)) ∧
      WeakPoissonOn (ballDomain (0 : Domain n) r.val)
        (fun x i => fderiv ℝ w x (EuclideanSpace.single i 1)) (fun _ => 0) ∧
      (∫ x in Metric.ball (0 : Domain n) r.val, hsNormSq (Du x)) =
        (∫ x in Metric.ball (0 : Domain n) r.val,
          hsNormSq (fun i => fderiv ℝ w x (EuclideanSpace.single i 1))) +
        (∫ x in Metric.ball (0 : Domain n) r.val,
          hsNormSq (fun i => Du x i - fderiv ℝ w x (EuclideanSpace.single i 1))) := by
  obtain ⟨w, Dw, _, hwcont, hwb, hwW, hzero, hwEq, _⟩ :=
    sobolev_harmonic_replacement_mollification_limit_centered hn r hrR hu hcont
  obtain ⟨hws, hwh⟩ := hwEq.contDiffOn_of_continuous_weak_harmonic hn
    (ballDomain (0 : Domain n) r.val) hwW.to_memW12Loc
    (hwcont.mono Metric.ball_subset_closedBall)
  have hclassical := hasWeakGradient_of_contDiffOn_one (ballDomain (0 : Domain n) r.val)
    (hws.of_le (WithTop.coe_le_coe.mpr (show (1 : ℕ∞) ≤ ⊤ from le_top)))
  have hsame := hwW.1.ae_eq hclassical
  have hwW' := hwW.congr_ae (EventuallyEq.refl _ _) hsame
  have hzero' : HasZeroBoundaryValues (ballDomain (0 : Domain n) r.val) (u - w)
      (fun x i => Du x i - fderiv ℝ w x (EuclideanSpace.single i 1)) := by
    apply hzero.congr_ae (EventuallyEq.refl _ _)
    filter_upwards [hsame] with x hx
    funext i
    rw [congrFun hx i]
  have hwEq' := hwEq.congr hsame (EventuallyEq.refl _ _)
  have huSmall := hu.to_memW12Loc.memW12_ball (Metric.closedBall_subset_ball hrR)
  have horth := weak_harmonic_replacement_energy_orthogonality
    (ballDomain (0 : Domain n) r.val) huSmall hwW' hwEq' hzero'
  exact ⟨w, hwcont, hwb, hws, hwh, hwW', hzero', hwEq', horth.1⟩

theorem continuous_sobolev_harmonic_replacement {n q : ℕ}
    (hn : 2 ≤ n) (a : Domain n) (r : PositiveRadius) {R : ℝ} (hrR : r.val < R)
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12 (ballDomain a R) u Du) (hcont : ContinuousOn u (Metric.ball a R)) :
    ∃ w : Domain n → Ambient q,
      ContinuousOn w (Metric.closedBall a r.val) ∧
      (∀ x ∈ Metric.sphere a r.val, w x = u x) ∧
      ContDiffOn ℝ ∞ w (Metric.ball a r.val) ∧
      (∀ x ∈ Metric.ball a r.val, Laplacian.laplacian w x = 0) ∧
      MemW12 (ballDomain a r.val) w
        (fun x i => fderiv ℝ w x (EuclideanSpace.single i 1)) ∧
      HasZeroBoundaryValues (ballDomain a r.val) (u - w)
        (fun x i => Du x i - fderiv ℝ w x (EuclideanSpace.single i 1)) ∧
      WeakPoissonOn (ballDomain a r.val)
        (fun x i => fderiv ℝ w x (EuclideanSpace.single i 1)) (fun _ => 0) ∧
      (∫ x in Metric.ball a r.val, hsNormSq (Du x)) =
        (∫ x in Metric.ball a r.val,
          hsNormSq (fun i => fderiv ℝ w x (EuclideanSpace.single i 1))) +
        (∫ x in Metric.ball a r.val,
          hsNormSq (fun i => Du x i - fderiv ℝ w x (EuclideanSpace.single i 1))) := by
  let u₀ : Domain n → Ambient q := fun z => u (a + z)
  let Du₀ : Domain n → Gradient n q := fun z i => Du (a + z) i
  have hu₀ : MemW12 (ballDomain (0 : Domain n) R) u₀ Du₀ := by
    simpa only [sub_zero] using hu.translate_ball (0 : Domain n)
  have hcont₀ : ContinuousOn u₀ (Metric.ball (0 : Domain n) R) := by
    apply hcont.comp (continuous_const.add continuous_id).continuousOn
    intro z hz
    simpa only [Pi.add_apply, id_eq, Metric.mem_ball, dist_eq_norm,
      add_sub_cancel_left, sub_zero] using hz
  obtain ⟨w₀, hwcont₀, hwb₀, hws₀, hwh₀, hwW₀, hzero₀, _, _⟩ :=
    continuous_sobolev_harmonic_replacement_centered hn r hrR hu₀ hcont₀
  let w : Domain n → Ambient q := fun x => w₀ (x - a)
  have hmap (x : Domain n) (hx : x ∈ Metric.ball a r.val) :
      x - a ∈ Metric.ball (0 : Domain n) r.val := by
    simpa only [Metric.mem_ball, dist_eq_norm, sub_zero] using hx
  have hwcont : ContinuousOn w (Metric.closedBall a r.val) := by
    apply hwcont₀.comp (continuous_id.sub continuous_const).continuousOn
    intro x hx
    simpa only [Pi.sub_apply, id_eq, Metric.mem_closedBall, dist_eq_norm, sub_zero] using hx
  have hws : ContDiffOn ℝ ∞ w (Metric.ball a r.val) :=
    hws₀.comp (contDiff_id.sub contDiff_const).contDiffOn hmap
  have hwh : ∀ x ∈ Metric.ball a r.val, Laplacian.laplacian w x = 0 := by
    intro x hx
    have heq : Laplacian.laplacian w x = Laplacian.laplacian w₀ (x - a) := by
      rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis w
        (EuclideanSpace.basisFun (Fin n) ℝ),
        InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis w₀
          (EuclideanSpace.basisFun (Fin n) ℝ)]
      apply Finset.sum_congr rfl
      intro i _
      rw [iteratedFDeriv_comp_sub]
    rw [heq]
    exact hwh₀ _ (hmap x hx)
  have hwW : MemW12 (ballDomain a r.val) w
      (fun x i => fderiv ℝ w x (EuclideanSpace.single i 1)) := by
    simpa only [w, zero_add, fderiv_comp_sub] using hwW₀.translate_ball a
  have hzero : HasZeroBoundaryValues (ballDomain a r.val) (u - w)
      (fun x i => Du x i - fderiv ℝ w x (EuclideanSpace.single i 1)) := by
    simpa only [one_smul, div_one, zero_add, Pi.sub_def, u₀, Du₀, add_sub_cancel,
      w, fderiv_comp_sub] using hzero₀.affineBall_pullback a (by norm_num : (0 : ℝ) < 1)
  have hwEq := weakPoissonOn_of_contDiffOn_two (ballDomain a r.val)
    (hws.of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)))
  have hwEq' : WeakPoissonOn (ballDomain a r.val)
      (fun x i => fderiv ℝ w x (EuclideanSpace.single i 1)) (fun _ => 0) := by
    apply hwEq.congr (EventuallyEq.refl _ _)
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    exact hwh x hx
  have huSmall := hu.to_memW12Loc.memW12_ball (Metric.closedBall_subset_ball hrR)
  have horth := weak_harmonic_replacement_energy_orthogonality
    (ballDomain a r.val) huSmall hwW hwEq' hzero
  refine ⟨w, hwcont, ?_, hws, hwh, hwW, hzero, hwEq', horth.1⟩
  intro x hx
  have hx₀ : x - a ∈ Metric.sphere (0 : Domain n) r.val := by
    simpa only [Metric.mem_sphere, dist_eq_norm, sub_zero] using hx
  simpa only [w, u₀, add_sub_cancel] using hwb₀ (x - a) hx₀

theorem continuous_sobolev_harmonic_replacement_on {n q : ℕ}
    (hn : 2 ≤ n) (Ω : OpenDomain n) (a : Domain n) (r : PositiveRadius)
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12Loc Ω u Du) (hcont : ContinuousOn u Ω.val)
    (hclosed : Metric.closedBall a r.val ⊆ Ω.val) :
    ∃ w : Domain n → Ambient q,
      ContinuousOn w (Metric.closedBall a r.val) ∧
      (∀ x ∈ Metric.sphere a r.val, w x = u x) ∧
      ContDiffOn ℝ ∞ w (Metric.ball a r.val) ∧
      (∀ x ∈ Metric.ball a r.val, Laplacian.laplacian w x = 0) ∧
      MemW12 (ballDomain a r.val) w
        (fun x i => fderiv ℝ w x (EuclideanSpace.single i 1)) ∧
      HasZeroBoundaryValues (ballDomain a r.val) (u - w)
        (fun x i => Du x i - fderiv ℝ w x (EuclideanSpace.single i 1)) ∧
      WeakPoissonOn (ballDomain a r.val)
        (fun x i => fderiv ℝ w x (EuclideanSpace.single i 1)) (fun _ => 0) ∧
      (∫ x in Metric.ball a r.val, hsNormSq (Du x)) =
        (∫ x in Metric.ball a r.val,
          hsNormSq (fun i => fderiv ℝ w x (EuclideanSpace.single i 1))) +
        (∫ x in Metric.ball a r.val,
          hsNormSq (fun i => Du x i - fderiv ℝ w x (EuclideanSpace.single i 1))) := by
  obtain ⟨R, hrR, hRclosed⟩ := exists_larger_closedBall_subset_open Ω a r hclosed
  exact continuous_sobolev_harmonic_replacement hn a r hrR (hu.memW12_ball hRclosed)
    (hcont.mono (Metric.ball_subset_closedBall.trans hRclosed))

end HolderToCK
end
