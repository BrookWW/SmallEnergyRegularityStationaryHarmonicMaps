module

public import StationaryHarmonicMaps.Analysis.LocalLpCriticalCutoff
public import StationaryHarmonicMaps.Analysis.LocalDivCurlContinuousPairing
public import StationaryHarmonicMaps.Analysis.NeumannGradientSpace
public import HarmonicMaps.Analysis.SobolevLocality

/-!
# Actual local Lp-controlled div--curl integrals

The original critical Lp growth produces its own centered global BMO
cutoff. On the test ball this cutoff is exactly the original observable
minus its original outer mean. Genuine solenoidal cancellation removes
that constant. The resulting ordinary original integral is controlled
by the original local Lp amplitude, with no BMO-extension premise.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped ContDiff Topology

namespace StationaryHarmonicMaps.Analysis

/-- Original local critical Lp growth and original solenoidal L2 data control the true div--curl integral against the original uncentered scalar observable. -/
theorem exists_local_lp_divcurl_integral_bound (n : ℕ) (hn : 2≤n)
    (p : ℝ) (hp₁ : 1≤p) (hp₂ : p≤2) :
    ∃ C : ℝ,0<C ∧ ∀ (m : ℕ) (a : Domain n) (t : ℝ),0<t →
      ∀ (u : Domain n → Ambient m) (Du : Domain n → Gradient n m) (K : ℝ),
        MemW12Loc (⟨univ,isOpen_univ⟩ : OpenDomain n) u Du → 0≤K →
        (∀ (x : Domain n) (r : ℝ),0<r → r≤8*t →
          (∫ y in Metric.ball x r,(Real.sqrt (hsNormSq (Du y)))^p)≤K^p*r^((n : ℝ)-p)) →
        ∀ (L : Ambient m →L[ℝ] ℝ) (q : ℕ) (Z : Domain n → Gradient n q),
          (∀ i,MemLp (fun x=>Z x i) 2 (volume.restrict (Metric.ball a (t/2)))) →
          HolderToCK.WeakPoissonOn (ballDomain a (t/2)) Z (fun _=>(0 : Ambient q)) →
          ∀ (w : Domain n → Ambient q),ContDiff ℝ ∞ w → HasCompactSupport w →
            tsupport w⊆Metric.ball a (t/2) →
            let Dw := fun x i=>fderiv ℝ w x (EuclideanSpace.single i 1)
            IntegrableOn (fun x=>(∑ i : Fin n,inner ℝ (Z x i) (Dw x i))*L (u x))
              (Metric.ball a (t/2)) volume ∧
            |∫ x in Metric.ball a (t/2),(∑ i : Fin n,inner ℝ (Z x i) (Dw x i))*L (u x)|≤
              C*‖L‖*K*Real.sqrt (∫ x in Metric.ball a (t/2),hsNormSq (Z x))*
                Real.sqrt (∫ x in Metric.ball a (t/2),hsNormSq (Dw x)) := by
  obtain ⟨D,hD,Hpair⟩ := existsUnique_local_divcurl_continuous_pairing n hn
  obtain ⟨B,hB,Hcut⟩ := exists_local_lp_critical_cutoff_scalar_mean_oscillation_bound n p hp₁ hp₂
  let C := D*B
  refine ⟨C,mul_pos hD hB,?_⟩
  intro m a t ht u Du K hu hK hGrowth L q Z hZ hDiv w hw hcw hsw Dw
  obtain ⟨χ,hχ,_hcχ,_hsχ,hOne,_hχBound,Hb⟩ := Hcut m a t ht u Du K hu hK hGrowth
  let c := ⨍ y in Metric.ball a (8*t),u y
  let b := fun x=>L (χ x • (u x-c))
  obtain ⟨hbMeas,hBMO⟩ := Hb L
  let μ := volume.restrict (Metric.ball a (t/2))
  let F := fun x=>∑ i : Fin n,inner ℝ (Z x i) (Dw x i)
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  have hwNative : MemW12 (ballDomain a (t/2)) w Dw :=
    memW12_ball_of_ambient_c1 a (t/2) w (hw.of_le (by simp))
  have hwZero : HasZeroBoundaryValues (ballDomain a (t/2)) w Dw :=
    hwNative.zeroBoundary_of_compactSupport_ball (half_pos ht) hcw hsw
  have hTerm (i : Fin n) : MemLp (fun x=>inner ℝ (Z x i) (Dw x i)) 2 μ := by
    have hDCont : Continuous (fun x=>Dw x i) := (hw.continuous_fderiv (by simp)).clm_apply continuous_const
    obtain ⟨M,hM⟩ := (hcw.fderiv_apply ℝ (EuclideanSpace.single i 1)).exists_bound_of_continuous hDCont
    apply (hZ i).norm.of_le_mul (c := M)
      ((hZ i).aestronglyMeasurable.inner hDCont.aestronglyMeasurable)
    exact Eventually.of_forall fun x=>by
      simpa only [norm_norm,mul_comm] using (norm_inner_le_norm (Z x i) (Dw x i)).trans
        (mul_le_mul_of_nonneg_left (hM x) (norm_nonneg (Z x i)))
  have hFLp : MemLp F 2 μ := memLp_finsetSum _ (fun i _=>hTerm i)
  have hFI : Integrable F μ := hFLp.integrable (by norm_num)
  have hULp : MemLp u 2 μ := (hu.memW12_ball (subset_univ _)).2.1
  have hObsLp : MemLp (fun x=>L (u x)) 2 μ := L.lipschitz.comp_memLp (map_zero L) hULp
  have hOriginalI : Integrable (fun x=>F x*L (u x)) μ := hFLp.integrable_mul hObsLp
  have hMeanZero : (∫ x,F x ∂μ)=0 :=
    (divergence_free_zeroBoundary_test (ballDomain a (t/2)) Z hZ hDiv hwZero).2
  have hInside (x : Domain n) (hx : x∈Metric.ball a (t/2)) : b x=L (u x)-L c := by
    dsimp only [b]
    rw [hOne x (Metric.ball_subset_closedBall hx),one_smul,L.map_sub]
  have hProductEq : (fun x=>F x*b x)=ᵐ[μ](fun x=>F x*L (u x)-F x*L c) := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    rw [hInside x hx]
    ring
  have hProduct : Integrable (fun x=>F x*b x) μ :=
    (hOriginalI.sub (hFI.mul_const (L c))).congr hProductEq.symm
  have hIntegral : (∫ x,F x*b x ∂μ)=(∫ x,F x*L (u x) ∂μ) := by
    rw [integral_congr_ae hProductEq,integral_sub hOriginalI (hFI.mul_const (L c)),
      integral_mul_const,hMeanZero,zero_mul,sub_zero]
  obtain ⟨l,⟨_hAllI,_hLimit,hEstimate,hAgree⟩,_hUnique⟩ := Hpair q a (t/2) (half_pos ht)
    Z hZ hDiv w Dw hwZero b (B*‖L‖*K) hbMeas (by positivity) hBMO
  have hL : l=(∫ x,F x*L (u x) ∂μ) := (hAgree hProduct).trans hIntegral
  rw [hL] at hEstimate
  exact ⟨hOriginalI,hEstimate.trans_eq (by dsimp only [C];ring)⟩

end StationaryHarmonicMaps.Analysis

end
