module

public import HolderToCK.Analysis.L2PairingContinuity
public import HolderToCK.Foundation.WeakPoisson
public import HarmonicMaps.EnergyLemmas
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.Topology.MetricSpace.Cauchy
public import Mathlib.Topology.UniformSpace.UniformApproximation
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! # Strong limits of harmonic replacement gradients

Hilbert--Schmidt contraction makes every gradient column a Cauchy sequence in
the complete L2 space. Uniform convergence on a finite carrier also gives
strong L2 convergence of the maps. Both statements use the original functions
and explicit columns, rather than a change of Sobolev representatives.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped Topology ENNReal

namespace HolderToCK

theorem integral_norm_sq_eq_L2_norm_sq {n q : ℕ} {μ : Measure (Domain n)}
    {f : Domain n → Ambient q} (hf : MemLp f 2 μ) :
    (∫ x, ‖f x‖ ^ 2 ∂μ) = ‖hf.toLp f‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  simpa only [real_inner_self_eq_norm_sq] using integral_inner_eq_L2_inner hf hf

theorem tendsto_integral_norm_sq_of_L2 {n q : ℕ} {μ : Measure (Domain n)}
    {f : ℕ → Domain n → Ambient q} {u : Domain n → Ambient q}
    (hf : ∀ k, MemLp (f k) 2 μ) (hu : MemLp u 2 μ)
    (hconv : Tendsto (fun k => eLpNorm (f k - u) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ x, ‖f k x‖ ^ 2 ∂μ) atTop (𝓝 (∫ x, ‖u x‖ ^ 2 ∂μ)) := by
  have hLp := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hf u hu).mpr hconv
  simpa only [← integral_norm_sq_eq_L2_norm_sq] using hLp.norm.pow 2

theorem tendsto_integral_hsNormSq_of_columns_L2 {n q : ℕ}
    {μ : Measure (Domain n)} {D : ℕ → Domain n → Gradient n q}
    {Du : Domain n → Gradient n q}
    (hD : ∀ k (i : Fin n), MemLp (fun x => D k x i) 2 μ)
    (hDu : ∀ i : Fin n, MemLp (fun x => Du x i) 2 μ)
    (hconv : ∀ i : Fin n, Tendsto
      (fun k => eLpNorm (fun x => D k x i - Du x i) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ x, hsNormSq (D k x) ∂μ) atTop
      (𝓝 (∫ x, hsNormSq (Du x) ∂μ)) := by
  have hsum := tendsto_finsetSum Finset.univ (fun i _ =>
    tendsto_integral_norm_sq_of_L2 (fun k => hD k i) (hDu i) (hconv i))
  have hEq (k : ℕ) : (∫ x, hsNormSq (D k x) ∂μ) =
      ∑ i : Fin n, ∫ x, ‖D k x i‖ ^ 2 ∂μ :=
    integral_finsetSum _ (fun i _ => (hD k i).integrable_norm_pow (by decide))
  have hEqU : (∫ x, hsNormSq (Du x) ∂μ) =
      ∑ i : Fin n, ∫ x, ‖Du x i‖ ^ 2 ∂μ :=
    integral_finsetSum _ (fun i _ => (hDu i).integrable_norm_pow (by decide))
  simpa only [hEq, hEqU] using hsum

theorem exists_columns_L2_limit_of_hs_energy_contraction {n q : ℕ}
    (μ : Measure (Domain n))
    {D W : ℕ → Domain n → Gradient n q} {Du : Domain n → Gradient n q}
    (hD : ∀ k (i : Fin n), MemLp (fun x => D k x i) 2 μ)
    (hW : ∀ k (i : Fin n), MemLp (fun x => W k x i) 2 μ)
    (hDu : ∀ i : Fin n, MemLp (fun x => Du x i) 2 μ)
    (hconv : ∀ i : Fin n, Tendsto
      (fun k => eLpNorm (fun x => D k x i - Du x i) 2 μ) atTop (𝓝 0))
    (hcontract : ∀ k l : ℕ,
      (∫ x, hsNormSq (fun i => W k x i - W l x i) ∂μ) ≤
        ∫ x, hsNormSq (fun i => D k x i - D l x i) ∂μ) :
    ∃ Dw : Domain n → Gradient n q,
      (∀ i : Fin n, MemLp (fun x => Dw x i) 2 μ) ∧
      ∀ i : Fin n, Tendsto
        (fun k => eLpNorm (fun x => W k x i - Dw x i) 2 μ) atTop (𝓝 0) := by
  classical
  have hfst : Tendsto (fun p : ℕ × ℕ => p.1) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_fst
  have hsnd : Tendsto (fun p : ℕ × ℕ => p.2) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_snd
  have hDlp (i : Fin n) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun k x => D k x i)
      (fun k => hD k i) (fun x => Du x i) (hDu i)).mpr (hconv i)
  have hDpair (i : Fin n) : Tendsto
      (fun p : ℕ × ℕ => ∫ x, ‖D p.1 x i - D p.2 x i‖ ^ 2 ∂μ) atTop (𝓝 0) := by
    have hdiff := ((hDlp i).comp hfst).sub ((hDlp i).comp hsnd)
    have hsquare := hdiff.norm.pow 2
    simpa only [Function.comp_def, ← MemLp.toLp_sub, ← integral_norm_sq_eq_L2_norm_sq,
      Pi.sub_apply, sub_self, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] using hsquare
  have henergy : Tendsto
      (fun p : ℕ × ℕ => ∫ x, hsNormSq (fun i => D p.1 x i - D p.2 x i) ∂μ)
      atTop (𝓝 0) := by
    have hsum := tendsto_finsetSum Finset.univ (fun i _ => hDpair i)
    have heq (p : ℕ × ℕ) :
        (∫ x, hsNormSq (fun i => D p.1 x i - D p.2 x i) ∂μ) =
          ∑ i : Fin n, ∫ x, ‖D p.1 x i - D p.2 x i‖ ^ 2 ∂μ :=
      integral_finsetSum _ (fun i _ => ((hD p.1 i).sub (hD p.2 i)).integrable_norm_pow
        (by decide))
    simpa only [heq, Finset.sum_const_zero] using hsum
  have hCauchy (i : Fin n) : CauchySeq
      (fun k => (hW k i).toLp (fun x => W k x i)) := by
    apply cauchySeq_iff_tendsto_dist_atTop_0.mpr
    have hsquare : Tendsto (fun p : ℕ × ℕ =>
        ‖(hW p.1 i).toLp (fun x => W p.1 x i) -
          (hW p.2 i).toLp (fun x => W p.2 x i)‖ ^ 2) atTop (𝓝 0) := by
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds henergy
        (fun _ => sq_nonneg _)
      intro p
      dsimp only
      rw [← MemLp.toLp_sub, ← integral_norm_sq_eq_L2_norm_sq]
      apply le_trans _ (hcontract p.1 p.2)
      apply integral_mono
      · exact ((hW p.1 i).sub (hW p.2 i)).integrable_norm_pow (by decide)
      · exact integrable_hsNormSq_of_memLp_columns (fun j => (hW p.1 j).sub (hW p.2 j))
      · intro x
        exact Finset.single_le_sum (fun j _ => sq_nonneg ‖W p.1 x j - W p.2 x j‖)
          (Finset.mem_univ i)
    have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hsquare
    simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _), Real.sqrt_zero,
      dist_eq_norm] using hsqrt
  obtain ⟨d, hd⟩ : ∃ d : Fin n → Lp (Ambient q) 2 μ,
      ∀ i : Fin n, Tendsto (fun k => (hW k i).toLp (fun x => W k x i)) atTop (𝓝 (d i)) := by
    choose d hd using fun i => cauchySeq_tendsto_of_complete (hCauchy i)
    exact ⟨d, hd⟩
  refine ⟨fun x i => d i x, fun i => Lp.memLp (d i), ?_⟩
  intro i
  have hlim := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'
    (fun k => (hW k i).toLp (fun x => W k x i)) (d i)).mp (hd i)
  apply hlim.congr
  intro k
  apply eLpNorm_congr_ae
  filter_upwards [(hW k i).coeFn_toLp] with x hx
  simp only [Pi.sub_apply]
  rw [hx]

theorem tendsto_L2_of_tendstoUniformlyOn {n q : ℕ}
    (μ : Measure (Domain n)) {s : Set (Domain n)} (hs : MeasurableSet s)
    [IsFiniteMeasure (μ.restrict s)]
    {f : ℕ → Domain n → Ambient q} {u : Domain n → Ambient q}
    (hf : ∀ k, MemLp (f k) 2 (μ.restrict s)) (hu : MemLp u 2 (μ.restrict s))
    (hconv : TendstoUniformlyOn f u atTop s) :
    Tendsto (fun k => eLpNorm (f k - u) 2 (μ.restrict s)) atTop (𝓝 0) := by
  have hfinite (k : ℕ) : eLpNorm (f k - u) 2 (μ.restrict s) ≠ ⊤ :=
    ((hf k).sub hu).eLpNorm_lt_top.ne
  apply (ENNReal.tendsto_toReal_zero_iff hfinite).mp
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall (fun _ => ha.trans_le ENNReal.toReal_nonneg)
  · intro ε hε
    let C : ℝ := (((μ.restrict s) univ) ^ ((2 : ℝ≥0∞).toReal⁻¹)).toReal
    let δ : ℝ := ε / (C + 1)
    have hC : 0 ≤ C := ENNReal.toReal_nonneg
    have hδ : 0 < δ := div_pos hε (by linarith only [hC])
    have hbound := (Metric.tendstoUniformlyOn_iff.mp hconv) δ hδ
    filter_upwards [hbound] with k hk
    have hle : eLpNorm (f k - u) 2 (μ.restrict s) ≤
        ((μ.restrict s) univ) ^ ((2 : ℝ≥0∞).toReal⁻¹) * ENNReal.ofReal δ := by
      apply eLpNorm_le_of_ae_bound
      filter_upwards [ae_restrict_mem hs] with x hx
      have hxnorm : ‖f k x - u x‖ < δ := by
        simpa only [dist_eq_norm, norm_sub_rev] using hk x hx
      exact hxnorm.le
    have htop : ((μ.restrict s) univ) ^ ((2 : ℝ≥0∞).toReal⁻¹) *
        ENNReal.ofReal δ ≠ ⊤ := by finiteness
    have hreal := ENNReal.toReal_mono htop hle
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hδ.le] at hreal
    have hδeq : (C + 1) * δ = ε := by
      dsimp only [δ]
      exact mul_div_cancel₀ _ (by linarith only [hC])
    exact hreal.trans_lt (by change C * δ < ε; nlinarith only [hδeq, hδ])

theorem continuousOn_closedBall_memLp_two {n q : ℕ} (a : Domain n) (r : ℝ)
    {u : Domain n → Ambient q} (hu : ContinuousOn u (Metric.closedBall a r)) :
    MemLp u 2 (volume.restrict (Metric.ball a r)) := by
  let K := Metric.closedBall a r
  have hK : IsCompact K := isCompact_closedBall a r
  letI : IsFiniteMeasure (volume.restrict K) :=
    isFiniteMeasure_restrict.mpr hK.measure_ne_top
  obtain ⟨C, hC⟩ := (hK.image_of_continuousOn hu).isBounded.exists_norm_le
  have hLp : MemLp u 2 (volume.restrict K) := by
    apply MemLp.of_bound (hu.aestronglyMeasurable hK.measurableSet) C
    filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
    exact hC _ (mem_image_of_mem u hx)
  exact hLp.mono_measure (Measure.restrict_mono_set _ Metric.ball_subset_closedBall)

theorem WeakPoissonOn.harmonic_of_columns_L2_limit {n q : ℕ} {Ω : OpenDomain n}
    {D : ℕ → Domain n → Gradient n q} {Du : Domain n → Gradient n q}
    (hEq : ∀ k, WeakPoissonOn Ω (D k) (fun _ => 0))
    (hD : ∀ k (i : Fin n), MemLp (fun x => D k x i) 2 (volume.restrict Ω.val))
    (hDu : ∀ i : Fin n, MemLp (fun x => Du x i) 2 (volume.restrict Ω.val))
    (hconv : ∀ i : Fin n, Tendsto
      (fun k => eLpNorm (fun x => D k x i - Du x i) 2 (volume.restrict Ω.val))
      atTop (𝓝 0)) :
    WeakPoissonOn Ω Du (fun _ => 0) := by
  refine ⟨locallyIntegrableOn_zero, ?_⟩
  intro ψ hψ hcψ hsψ
  have hdψ (i : Fin n) : MemLp
      (fun x => fderiv ℝ ψ x (EuclideanSpace.single i 1)) 2
      (volume.restrict Ω.val) :=
    ((hψ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hcψ.fderiv_apply ℝ (EuclideanSpace.single i 1))
  have hpair (i : Fin n) := integrable_inner_of_memLp_two (hDu i) (hdψ i)
  have hlim := tendsto_finsetSum Finset.univ (fun i _ =>
    tendsto_integral_inner_of_L2 (fun k => hD k i) (hDu i) (hdψ i) (hconv i))
  have hseq (k : ℕ) : (∑ i : Fin n, ∫ x in Ω.val,
      inner ℝ (fderiv ℝ ψ x (EuclideanSpace.single i 1)) (D k x i)) = 0 := by
    rw [← integral_finsetSum _ (fun i _ => integrable_inner_of_memLp_two (hdψ i) (hD k i))]
    have heq : (∫ x in Ω.val, ∑ i : Fin n,
        inner ℝ (fderiv ℝ ψ x (EuclideanSpace.single i 1)) (D k x i)) =
        ∫ x in Ω.val, ∑ i : Fin n,
          inner ℝ (D k x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1)) := by
      apply setIntegral_congr_fun Ω.property.measurableSet
      intro x _
      exact Finset.sum_congr rfl (fun i _ =>
        (real_inner_comm (fderiv ℝ ψ x (EuclideanSpace.single i 1)) (D k x i)).symm)
    rw [heq]
    simpa only [inner_zero_left, integral_zero, neg_zero] using (hEq k).2 ψ hψ hcψ hsψ |>.2.2
  refine ⟨integrable_finsetSum _ (fun i _ => hpair i),
    (by
      simp only [inner_zero_left]
      change Integrable (0 : Domain n → ℝ) (volume.restrict Ω.val)
      exact integrable_zero _ _ _), ?_⟩
  simp only [inner_zero_left, integral_zero, neg_zero]
  rw [integral_finsetSum _ (fun i _ => hpair i)]
  have hzero : (∑ i : Fin n, ∫ x in Ω.val,
      inner ℝ (fderiv ℝ ψ x (EuclideanSpace.single i 1)) (Du x i)) = 0 :=
    tendsto_nhds_unique hlim (by simpa only [hseq] using tendsto_const_nhds (x := (0 : ℝ)))
  simpa only [real_inner_comm] using hzero

theorem exists_uniform_limit_on_carrier {n q : ℕ}
    {s : Set (Domain n)} {f : ℕ → Domain n → Ambient q}
    (hCauchy : UniformCauchySeqOn f atTop s) :
    ∃ v : s → Ambient q,
      TendstoUniformly (fun k (x : s) => f k x.val) v atTop := by
  choose v hv using fun x : s => cauchySeq_tendsto_of_complete (hCauchy.cauchySeq x.property)
  refine ⟨v, tendstoUniformlyOn_univ.mp ?_⟩
  have hC := (hCauchy.comp (fun x : s => x.val)).mono (show univ ⊆
      (fun x : s => x.val) ⁻¹' s from fun x _ => x.property)
  exact hC.tendstoUniformlyOn_of_tendsto (fun x _ => hv x)

theorem tendsto_setIntegral_ball_of_antitone_radius {n : ℕ} (a : Domain n)
    (r : PositiveRadius) {ρ : ℕ → ℝ} (hρ : Antitone ρ)
    (hρr : ∀ k, r.val < ρ k) (hlim : Tendsto ρ atTop (𝓝 r.val))
    {f : Domain n → ℝ} (hf : IntegrableOn f (Metric.ball a (ρ 0))) :
    Tendsto (fun k => ∫ x in Metric.ball a (ρ k), f x) atTop
      (𝓝 (∫ x in Metric.ball a r.val, f x)) := by
  have hinter : (⋂ k, Metric.ball a (ρ k)) = Metric.closedBall a r.val := by
    ext x
    simp only [mem_iInter, Metric.mem_ball, Metric.mem_closedBall]
    constructor
    · intro hx
      exact le_of_tendsto_of_tendsto tendsto_const_nhds hlim
        (Eventually.of_forall fun k => (hx k).le)
    · intro hx k
      exact hx.trans_lt (hρr k)
  have hclosed_ball : Metric.closedBall a r.val =ᵐ[volume] Metric.ball a r.val := by
    have hnot : ∀ᵐ x ∂(volume : Measure (Domain n)), x ∉ Metric.sphere a r.val :=
      measure_eq_zero_iff_ae_notMem.mp
        (Measure.addHaar_sphere_of_ne_zero volume a r.property.ne')
    filter_upwards [hnot] with x hx
    apply propext
    constructor
    · intro hxc
      have hne : dist x a ≠ r.val := by simpa only [Metric.mem_sphere] using hx
      exact lt_of_le_of_ne hxc hne
    · intro hxb
      exact hxb.le
  have hset := tendsto_setIntegral_of_antitone (fun _ => measurableSet_ball)
    (fun k l hkl => Metric.ball_subset_ball (hρ hkl)) ⟨0, hf⟩
  rw [hinter, setIntegral_congr_set hclosed_ball] at hset
  exact hset

theorem tendsto_eLpNorm_sub_of_L2 {n q : ℕ} {μ : Measure (Domain n)}
    {f g : ℕ → Domain n → Ambient q} {u v : Domain n → Ambient q}
    (hf : ∀ k, MemLp (f k) 2 μ) (hg : ∀ k, MemLp (g k) 2 μ)
    (hu : MemLp u 2 μ) (hv : MemLp v 2 μ)
    (hfu : Tendsto (fun k => eLpNorm (f k - u) 2 μ) atTop (𝓝 0))
    (hgv : Tendsto (fun k => eLpNorm (g k - v) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun k => eLpNorm ((f k - g k) - (u - v)) 2 μ) atTop (𝓝 0) := by
  have hsum : Tendsto (fun k => eLpNorm (f k - u) 2 μ + eLpNorm (g k - v) 2 μ)
      atTop (𝓝 0) := by simpa only [add_zero] using hfu.add hgv
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => bot_le)
  intro k
  dsimp only
  have heq : (f k - g k) - (u - v) = (f k - u) - (g k - v) := by abel
  rw [heq]
  exact eLpNorm_sub_le ((hf k).sub hu).aestronglyMeasurable
    ((hg k).sub hv).aestronglyMeasurable (by norm_num)

end HolderToCK
end
