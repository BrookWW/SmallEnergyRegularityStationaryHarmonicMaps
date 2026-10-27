module

public import HolderToCK.Analysis.Harmonic.SobolevReplacement
public import HolderToCK.Analysis.Harmonic.WeakGradientError
public import HolderToCK.Analysis.HolderMollification
public import HolderToCK.Analysis.Harmonic.ReplacementTranslation

/-! # Exact quadratic-forcing error of the harmonic replacement

The smooth Poisson differences have the negative Green identity. Positivity of
the mollifier and the harmonic maximum estimate bound their amplitude by the
Holder oscillation. Strong gradient convergence and continuity of the original
energy on decreasing radius neighborhoods give the stated radius power.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped ContDiff Topology ENNReal

namespace HolderToCK

theorem mollification_norm_sub_center_le_of_holder {n q : ℕ}
    (a : Domain n) {R : ℝ} (r h : PositiveRadius) (hMargin : r.val + h.val ≤ R)
    {u : Domain n → Ambient q} (hInt : IntegrableOn u (Metric.ball a R) volume)
    {α H : ℝ} (hα : 0 ≤ α) (hH : 0 ≤ H)
    (hHolder : HolderBoundOn (Metric.ball a R) u α H) :
    ∀ x ∈ Metric.closedBall a r.val,
      ‖euclideanMollification (ballDomain a R) u hInt h x - u a‖ ≤
        H * Real.rpow (r.val + h.val) α := by
  have ha : a ∈ Metric.ball a R :=
    Metric.mem_ball_self (lt_of_lt_of_le (add_pos r.property h.property) hMargin)
  have hsupport : Function.support (scaledMollifierKernel n h) ⊆
      Metric.ball (0 : Domain n) h.val :=
    (subset_tsupport _).trans ((scaledMollifierKernel_tsupport_subset_halfBall n h).trans
      (Metric.closedBall_subset_ball (by linarith only [h.property])))
  intro x hx
  have hbound : ∀ y ∈ Metric.ball x h.val,
      dist (zeroExtensionOn (ballDomain a R) u y) (u a) ≤
        H * Real.rpow (r.val + h.val) α := by
    intro y hy
    have hxa : dist x a ≤ r.val := hx
    have hyx : dist y x < h.val := hy
    have hya : dist y a < r.val + h.val :=
      lt_of_le_of_lt (dist_triangle y x a) (by linarith only [hxa, hyx])
    have hyR : y ∈ Metric.ball a R := hya.trans_le hMargin
    rw [zeroExtensionOn, indicator_of_mem (show y ∈ (ballDomain a R).val from hyR), dist_eq_norm]
    exact (hHolder y hyR a ha).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow dist_nonneg hya.le hα) hH)
  change dist (euclideanMollification (ballDomain a R) u hInt h x) (u a) ≤ _
  exact dist_convolution_le
    (mul_nonneg hH (Real.rpow_nonneg (add_pos r.property h.property).le _)) hsupport
    (scaledMollifierKernel_nonneg n h) (scaledMollifierKernel_integral_one n h)
    (zeroExtensionOn_integrable (ballDomain a R) u hInt).aestronglyMeasurable hbound

theorem quadratic_harmonic_replacement_exists_centered {n q : ℕ}
    (hn : 2 ≤ n) (r : PositiveRadius) {R : ℝ} (hrR : r.val < R)
    {u F : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12 (ballDomain (0 : Domain n) R) u Du)
    (hEq : WeakPoissonOn (ballDomain (0 : Domain n) R) Du F)
    {α H K : ℝ} (hα : 0 < α) (hH : 0 ≤ H) (_hK : 0 ≤ K)
    (hHolder : HolderBoundOn (Metric.ball (0 : Domain n) R) u α H)
    (hBound : ∀ᵐ x ∂volume.restrict (Metric.ball (0 : Domain n) R),
      ‖F x‖ ≤ K * hsNormSq (Du x)) :
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
          hsNormSq (fun i => Du x i - fderiv ℝ w x (EuclideanSpace.single i 1))) ∧
      (∫ x in Metric.ball (0 : Domain n) r.val,
        hsNormSq (fun i => Du x i - fderiv ℝ w x (EuclideanSpace.single i 1))) ≤
        2 * K * H * Real.rpow r.val α * ∫ x in Metric.ball (0 : Domain n) r.val, hsNormSq (Du x) := by
  let scale : ℕ → PositiveRadius := fun k =>
    ⟨(R - r.val) / ((k : ℝ) + 1), by positivity⟩
  let m : ℕ → Domain n → Ambient q := fun k =>
    euclideanMollification (ballDomain (0 : Domain n) R) u hu.integrable_ball (scale k)
  have hm (k : ℕ) : ContDiff ℝ ∞ (m k) :=
    euclideanMollification_contDiff _ u hu.integrable_ball (scale k)
  have hmW (k : ℕ) : MemW12 (ballDomain (0 : Domain n) r.val) (m k)
      (fun x i => fderiv ℝ (m k) x (EuclideanSpace.single i 1)) :=
    dirichlet_smoothData_memW12 r univ isOpen_univ (subset_univ _) (m k) (hm k).contDiffOn
  have hcont := hHolder.continuousOn hα
  obtain ⟨w, Dw, W, hwcont, hwb, hwW, hzero, hwEq,
    hWs, hWb, hWh, hWW, hWzero, hWEq, _, hDWlim⟩ :=
    sobolev_harmonic_replacement_mollification_limit_centered hn r hrR hu hcont
  have hscale : Tendsto (fun k => (scale k).val) atTop (𝓝 0) := by
    simpa only [scale, div_eq_mul_inv, one_mul, mul_zero] using
      (tendsto_const_nhds (x := R - r.val)).mul tendsto_one_div_add_atTop_nhds_zero_nat
  have hscaleFilter : Tendsto scale atTop
      (comap (fun h : PositiveRadius => h.val) (𝓝 (0 : ℝ))) := tendsto_comap_iff.mpr hscale
  have hscaleLe (k : ℕ) : (scale k).val ≤ R - r.val := by
    change (R - r.val) / ((k : ℝ) + 1) ≤ R - r.val
    apply (div_le_iff₀ (by positivity : 0 < (k : ℝ) + 1)).mpr
    nlinarith only [sub_pos.mpr hrR, Nat.cast_nonneg (α := ℝ) k]
  have hDmL2 (i : Fin n) : Tendsto (fun k => eLpNorm
      (fun x => fderiv ℝ (m k) x (EuclideanSpace.single i 1) - Du x i) 2
      (volume.restrict (Metric.ball (0 : Domain n) r.val))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, m, coordinateDerivative] using
      (hu.tendsto_eLpNorm_mollification_column_inner_ball hrR i).comp hscaleFilter
  let μ := volume.restrict (Metric.ball (0 : Domain n) r.val)
  letI : IsFiniteMeasure (volume.restrict (ballDomain (0 : Domain n) r.val).val) :=
    isFiniteMeasure_restrict.mpr measure_ball_ne_top
  have huSmall := hu.to_memW12Loc.memW12_ball (Metric.closedBall_subset_ball hrR)
  have herrorSmooth (k : ℕ) : (∫ x in Metric.ball (0 : Domain n) r.val,
      hsNormSq (fun i => fderiv ℝ (m k) x (EuclideanSpace.single i 1) -
        fderiv ℝ (W k) x (EuclideanSpace.single i 1))) ≤
      2 * K * H * Real.rpow (r.val + (scale k).val) α *
        ∫ x in Metric.ball (0 : Domain n) (r.val + (scale k).val), hsNormSq (Du x) := by
    have hMargin : r.val + (scale k).val ≤ R := by linarith only [hscaleLe k]
    have hForce := hEq.mollification_poisson_and_forcing_energy hu K hBound (scale k) hMargin
    have hosc : ∀ x ∈ Metric.closedBall (0 : Domain n) r.val,
        ‖m k x - u 0‖ ≤ H * Real.rpow (r.val + (scale k).val) α :=
      mollification_norm_sub_center_le_of_holder 0 r (scale k) hMargin
        hu.integrable_ball hα.le hH hHolder
    have hWosc := smooth_harmonic_norm_sub_le_boundary hn r (m k) (W k)
      (hm k) (hWs k) (hWb k) (hWh k) (u 0)
      (H * Real.rpow (r.val + (scale k).val) α)
      (fun x hx => hosc x (Metric.sphere_subset_closedBall hx))
    have hdiff : ∀ x ∈ (ballDomain (0 : Domain n) r.val).val,
        ‖(m k - W k) x‖ ≤ 2 * H * Real.rpow (r.val + (scale k).val) α := by
      intro x hx
      calc
        _ = ‖(m k x - u 0) - (W k x - u 0)‖ := by
          change ‖m k x - W k x‖ = _
          congr 1
          abel
        _ ≤ ‖m k x - u 0‖ + ‖W k x - u 0‖ := norm_sub_le _ _
        _ ≤ (H * Real.rpow (r.val + (scale k).val) α) +
            (H * Real.rpow (r.val + (scale k).val) α) :=
          add_le_add (hosc x (Metric.ball_subset_closedBall hx))
            (hWosc x (Metric.ball_subset_closedBall hx))
        _ = _ := by ring
    have hmEq := weakPoissonOn_of_contDiffOn_two (ballDomain (0 : Domain n) r.val)
      ((hm k).of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))).contDiffOn
    have hLapCont : ContinuousOn (Laplacian.laplacian (m k)) (Metric.closedBall (0 : Domain n) r.val) :=
      (continuousOn_laplacian_of_contDiffOn_two ⟨univ, isOpen_univ⟩
        ((hm k).of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))).contDiffOn).mono
        (subset_univ _)
    have hLapLp := continuousOn_closedBall_memLp_two (0 : Domain n) r.val hLapCont
    have hgreen := weak_harmonic_difference_error_le hmEq (hWEq k) hLapLp (hWzero k)
      (2 * H * Real.rpow (r.val + (scale k).val) α) hdiff
    have hLapForce : (∫ x in Metric.ball (0 : Domain n) r.val, ‖Laplacian.laplacian (m k) x‖) ≤
        K * ∫ x in Metric.ball (0 : Domain n) (r.val + (scale k).val), hsNormSq (Du x) := by
      calc
        _ = ∫ x in Metric.ball (0 : Domain n) r.val,
            ‖∫ y, scaledMollifierKernel n (scale k) y • F (x - y)‖ :=
          setIntegral_congr_fun measurableSet_ball (fun x hx => congrArg norm (hForce.2.1 x hx))
        _ ≤ _ := hForce.2.2.2
    calc
      _ ≤ (2 * H * Real.rpow (r.val + (scale k).val) α) *
          (∫ x in Metric.ball (0 : Domain n) r.val, ‖Laplacian.laplacian (m k) x‖) := hgreen
      _ ≤ (2 * H * Real.rpow (r.val + (scale k).val) α) *
          (K * ∫ x in Metric.ball (0 : Domain n) (r.val + (scale k).val), hsNormSq (Du x)) :=
        mul_le_mul_of_nonneg_left hLapForce
          (mul_nonneg (mul_nonneg (by norm_num) hH)
            (Real.rpow_nonneg (add_nonneg r.property.le (scale k).property.le) _))
      _ = _ := by ring
  have hDerror (i : Fin n) : Tendsto (fun k => eLpNorm
      (fun x => (fderiv ℝ (m k) x (EuclideanSpace.single i 1) -
        fderiv ℝ (W k) x (EuclideanSpace.single i 1)) - (Du x i - Dw x i)) 2 μ)
      atTop (𝓝 0) := by
    simpa only [Pi.sub_def, ballDomain] using tendsto_eLpNorm_sub_of_L2 (μ := μ)
      (fun k => (hmW k).2.2 i) (fun k => (hWW k).2.2 i) (huSmall.2.2 i) (hwW.2.2 i)
      (by simpa only [Pi.sub_def, ballDomain] using hDmL2 i)
      (by simpa only [Pi.sub_def, ballDomain] using hDWlim i)
  have herrorLim : Tendsto (fun k => ∫ x in Metric.ball (0 : Domain n) r.val,
      hsNormSq (fun i => fderiv ℝ (m k) x (EuclideanSpace.single i 1) -
        fderiv ℝ (W k) x (EuclideanSpace.single i 1))) atTop
      (𝓝 (∫ x in Metric.ball (0 : Domain n) r.val, hsNormSq (fun i => Du x i - Dw x i))) := by
    simpa only [Pi.sub_apply, ballDomain] using tendsto_integral_hsNormSq_of_columns_L2
      (fun k i => ((hmW k).2.2 i).sub ((hWW k).2.2 i))
      (fun i => (huSmall.2.2 i).sub (hwW.2.2 i)) hDerror
  have hradiusLim : Tendsto (fun k => r.val + (scale k).val) atTop (𝓝 r.val) := by
    simpa only [add_zero] using (tendsto_const_nhds (x := r.val)).add hscale
  have hradiusAnti : Antitone (fun k => r.val + (scale k).val) := by
    intro k l hkl
    change r.val + ((R - r.val) / ((l : ℝ) + 1)) ≤
      r.val + ((R - r.val) / ((k : ℝ) + 1))
    apply add_le_add le_rfl
    apply div_le_div_of_nonneg_left (sub_pos.mpr hrR).le (by positivity)
    exact add_le_add (Nat.cast_le.mpr hkl) le_rfl
  have henergyLim := tendsto_setIntegral_ball_of_antitone_radius (0 : Domain n) r
    hradiusAnti (fun k => lt_add_of_pos_right r.val (scale k).property) hradiusLim
    (hu.integrable_hsNormSq.mono_set (Metric.ball_subset_ball (by
      simp only [scale, Nat.cast_zero, zero_add, div_one]
      exact le_of_eq (by ring))))
  have hpowerAt : ContinuousAt (fun t : ℝ => Real.rpow t α) r.val :=
    continuousAt_id.rpow_const (Or.inl r.property.ne')
  have hboundLim := (((tendsto_const_nhds (x := 2 * K * H)).mul
    (hpowerAt.tendsto.comp hradiusLim)).mul henergyLim)
  have herror : (∫ x in Metric.ball (0 : Domain n) r.val,
      hsNormSq (fun i => Du x i - Dw x i)) ≤
      2 * K * H * Real.rpow r.val α * ∫ x in Metric.ball (0 : Domain n) r.val, hsNormSq (Du x) :=
    le_of_tendsto_of_tendsto herrorLim hboundLim (Eventually.of_forall herrorSmooth)
  obtain ⟨hws, hwh⟩ := hwEq.contDiffOn_of_continuous_weak_harmonic hn
    (ballDomain (0 : Domain n) r.val) hwW.to_memW12Loc (hwcont.mono Metric.ball_subset_closedBall)
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
  have horth := weak_harmonic_replacement_energy_orthogonality
    (ballDomain (0 : Domain n) r.val) huSmall hwW' hwEq' hzero'
  refine ⟨w, hwcont, hwb, hws, hwh, hwW', hzero', hwEq', horth.1, ?_⟩
  have heq : (∫ x in Metric.ball (0 : Domain n) r.val,
      hsNormSq (fun i => Du x i - fderiv ℝ w x (EuclideanSpace.single i 1))) =
      ∫ x in Metric.ball (0 : Domain n) r.val, hsNormSq (fun i => Du x i - Dw x i) := by
    apply integral_congr_ae
    filter_upwards [hsame] with x hx
    exact congrArg (fun d : Gradient n q => hsNormSq (fun i => Du x i - d i)) hx.symm
  rw [heq]
  exact herror

theorem quadratic_harmonic_replacement_exists {n q : ℕ}
    (hn : 2 ≤ n) (a : Domain n) (r : PositiveRadius) {R : ℝ} (hrR : r.val < R)
    {u F : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12 (ballDomain a R) u Du) (hEq : WeakPoissonOn (ballDomain a R) Du F)
    {α H K : ℝ} (hα : 0 < α) (hH : 0 ≤ H) (hK : 0 ≤ K)
    (hHolder : HolderBoundOn (Metric.ball a R) u α H)
    (hBound : ∀ᵐ x ∂volume.restrict (Metric.ball a R), ‖F x‖ ≤ K * hsNormSq (Du x)) :
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
          hsNormSq (fun i => Du x i - fderiv ℝ w x (EuclideanSpace.single i 1))) ∧
      (∫ x in Metric.ball a r.val,
        hsNormSq (fun i => Du x i - fderiv ℝ w x (EuclideanSpace.single i 1))) ≤
        2 * K * H * Real.rpow r.val α * ∫ x in Metric.ball a r.val, hsNormSq (Du x) := by
  let u₀ : Domain n → Ambient q := fun z => u (a + z)
  let Du₀ : Domain n → Gradient n q := fun z i => Du (a + z) i
  let F₀ : Domain n → Ambient q := fun z => F (a + z)
  have hu₀ : MemW12 (ballDomain (0 : Domain n) R) u₀ Du₀ := by
    simpa only [sub_zero] using hu.translate_ball (0 : Domain n)
  have hEq₀ : WeakPoissonOn (ballDomain (0 : Domain n) R) Du₀ F₀ := by
    simpa only [sub_zero] using hEq.translate_ball_of_quadratic_bound hu K hBound (0 : Domain n)
  have hmapR (z : Domain n) (hz : z ∈ Metric.ball (0 : Domain n) R) :
      a + z ∈ Metric.ball a R := by
    simpa only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, sub_zero] using hz
  have hHolder₀ : HolderBoundOn (Metric.ball (0 : Domain n) R) u₀ α H := by
    intro z hz y hy
    simpa only [u₀, dist_add_left] using hHolder (a + z) (hmapR z hz) (a + y) (hmapR y hy)
  have hBound₀ : ∀ᵐ z ∂volume.restrict (Metric.ball (0 : Domain n) R),
      ‖F₀ z‖ ≤ K * hsNormSq (Du₀ z) := by
    simpa only [div_one, one_smul, sub_zero] using
      ae_affineBall a (0 : Domain n) (by norm_num : (0 : ℝ) < 1) R hBound
  obtain ⟨w₀, hwcont₀, hwb₀, hws₀, hwh₀, hwW₀, hzero₀, _, _, herror₀⟩ :=
    quadratic_harmonic_replacement_exists_centered hn r hrR hu₀ hEq₀ hα hH hK hHolder₀ hBound₀
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
  have horth := weak_harmonic_replacement_energy_orthogonality (ballDomain a r.val)
    huSmall hwW hwEq' hzero
  refine ⟨w, hwcont, ?_, hws, hwh, hwW, hzero, hwEq', horth.1, ?_⟩
  · intro x hx
    have hx₀ : x - a ∈ Metric.sphere (0 : Domain n) r.val := by
      simpa only [Metric.mem_sphere, dist_eq_norm, sub_zero] using hx
    simpa only [w, u₀, add_sub_cancel] using hwb₀ (x - a) hx₀
  · have hErrorTransport : (∫ z in Metric.ball (0 : Domain n) r.val,
        hsNormSq (fun i => Du₀ z i - fderiv ℝ w₀ z (EuclideanSpace.single i 1))) =
        ∫ x in Metric.ball a r.val,
          hsNormSq (fun i => Du x i - fderiv ℝ w x (EuclideanSpace.single i 1)) := by
      simpa only [one_smul, div_one, one_pow, inv_one, sub_zero, w, Du₀,
        fderiv_comp_sub, add_sub_cancel_left] using
        integral_affineBall a (0 : Domain n) (by norm_num : (0 : ℝ) < 1) r.val
          (fun x => hsNormSq (fun i => Du x i - fderiv ℝ w x (EuclideanSpace.single i 1)))
    have hEnergyTransport : (∫ z in Metric.ball (0 : Domain n) r.val, hsNormSq (Du₀ z)) =
        ∫ x in Metric.ball a r.val, hsNormSq (Du x) := by
      simpa only [one_smul, div_one, one_pow, inv_one, sub_zero, Du₀] using
        integral_affineBall a (0 : Domain n) (by norm_num : (0 : ℝ) < 1) r.val
          (fun x => hsNormSq (Du x))
    rw [← hErrorTransport, ← hEnergyTransport]
    exact herror₀

theorem quadratic_harmonic_replacement_exists_on {n q : ℕ}
    (hn : 2 ≤ n) (Ω : OpenDomain n) (a : Domain n) (r : PositiveRadius)
    {u F : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12Loc Ω u Du) (hEq : WeakPoissonOn Ω Du F)
    {α H K : ℝ} (hα : 0 < α) (hH : 0 ≤ H) (hK : 0 ≤ K)
    (hHolder : HolderBoundOn Ω.val u α H)
    (hBound : ∀ᵐ x ∂volume.restrict Ω.val, ‖F x‖ ≤ K * hsNormSq (Du x))
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
          hsNormSq (fun i => Du x i - fderiv ℝ w x (EuclideanSpace.single i 1))) ∧
      (∫ x in Metric.ball a r.val,
        hsNormSq (fun i => Du x i - fderiv ℝ w x (EuclideanSpace.single i 1))) ≤
        2 * K * H * Real.rpow r.val α * ∫ x in Metric.ball a r.val, hsNormSq (Du x) := by
  obtain ⟨R, hrR, hRclosed⟩ := exists_larger_closedBall_subset_open Ω a r hclosed
  have hsub : (ballDomain a R).val ⊆ Ω.val := Metric.ball_subset_closedBall.trans hRclosed
  exact quadratic_harmonic_replacement_exists hn a r hrR (hu.memW12_ball hRclosed)
    (hEq.mono hsub) hα hH hK (fun x hx y hy => hHolder x (hsub hx) y (hsub hy))
    (ae_restrict_of_ae_restrict_of_subset hsub hBound)

end HolderToCK
end
