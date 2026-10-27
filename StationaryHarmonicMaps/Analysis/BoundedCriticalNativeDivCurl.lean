module

public import StationaryHarmonicMaps.Analysis.CutoffGlobalMeanOscillation
public import StationaryHarmonicMaps.Analysis.LocalDivCurlContinuousPairing
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Native compensated tests for bounded critical Sobolev fields

A fixed interior cutoff produces the global BMO observable from the
original critical gradient. The original essential bound makes the native
zero-boundary pairing an ordinary integral. Solenoidal cancellation removes
the constant mean. The estimate is independent of the essential bound.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped ContDiff Topology

namespace StationaryHarmonicMaps.Analysis

/-- The original bounded critical graph controls every native W0 div-curl test on each ball contained in the half unit ball. -/
theorem exists_bounded_critical_native_divcurl_bound (n : ℕ) (hn : 2≤n) :
    ∃ C : ℝ,0<C ∧ ∀ (m : ℕ) (u : Domain n → Ambient m)
      (Du : Domain n → Gradient n m) (η M : ℝ),
      MemW12 (ballDomain (0 : Domain n) 1) u Du → 0≤η →
      (∀ᵐ x ∂volume.restrict (ball (0 : Domain n) 1),‖u x‖≤M) →
      criticalGradientMorreySquare Du (ball (0 : Domain n) 1)≤ENNReal.ofReal (η^2) →
      ∀ (a : Domain n) (r : ℝ),0<r → ball a r⊆ball (0 : Domain n) (1/2 : ℝ) →
        ∀ (L : Ambient m →L[ℝ] ℝ) (q : ℕ) (Z : Domain n → Gradient n q),
          (∀ i,MemLp (fun x=>Z x i) 2 (volume.restrict (ball a r))) →
          HolderToCK.WeakPoissonOn (ballDomain a r) Z (fun _=>(0 : Ambient q)) →
          ∀ (w : Domain n → Ambient q) (Dw : Domain n → Gradient n q),
            HasZeroBoundaryValues (ballDomain a r) w Dw →
            IntegrableOn (fun x=>(∑i : Fin n,inner ℝ (Z x i) (Dw x i))*L (u x))
              (ball a r) volume ∧
            |∫x in ball a r,(∑i : Fin n,inner ℝ (Z x i) (Dw x i))*L (u x)|≤
              C*‖L‖*η*Real.sqrt (∫x in ball a r,hsNormSq (Z x))*
                Real.sqrt (∫x in ball a r,hsNormSq (Dw x)) := by
  let χ : ContDiffBump (0 : Domain n) := ⟨1/2,3/4,by norm_num,by norm_num⟩
  have hχ : ContDiff ℝ ∞ (χ : Domain n → ℝ) := χ.contDiff
  obtain ⟨B,hB⟩ := (χ.hasCompactSupport.fderiv ℝ).exists_bound_of_continuous
    (hχ.continuous_fderiv (by simp))
  let B₀ := |B|
  have hDχ (x : Domain n) (i : Fin n) :
      |fderiv ℝ (χ : Domain n → ℝ) x (EuclideanSpace.single i 1)|≤B₀ := by
    calc
      _≤‖fderiv ℝ (χ : Domain n → ℝ) x‖*‖EuclideanSpace.single i (1 : ℝ)‖ :=
        (fderiv ℝ (χ : Domain n → ℝ) x).le_opNorm _
      _=‖fderiv ℝ (χ : Domain n → ℝ) x‖ := by simp
      _≤B₀ := (hB x).trans (le_abs_self B)
  have hsχ : tsupport (χ : Domain n → ℝ)⊆closedBall (0 : Domain n) (3/4 : ℝ) := by
    rw [χ.tsupport_eq]
  have hχOne (x : Domain n) (hx : x∈ball (0 : Domain n) (1/2 : ℝ)) : χ x=1 :=
    χ.one_of_mem_closedBall (ball_subset_closedBall hx)
  obtain ⟨K,hK,Hcut⟩ := exists_cutoff_global_scalar_mean_oscillation_bound n hn 1 B₀
    (by norm_num) (abs_nonneg B)
  obtain ⟨D,hD,Hpair⟩ := existsUnique_local_divcurl_continuous_pairing n hn
  refine ⟨D*K,mul_pos hD hK,?_⟩
  intro m u Du η M hu hη huBound hCritical a r hr hBall L q Z hZ hDiv w Dw hw
  let μ := volume.restrict (ball a r)
  let c := ⨍y in ball (0 : Domain n) 1,u y
  let b := fun x=>L (χ x • (u x-c))
  let F := fun x=>∑i : Fin n,inner ℝ (Z x i) (Dw x i)
  obtain ⟨hbMeas,_hInside,hBMO⟩ := Hcut m u Du η hu hη hCritical χ χ.contDiff
    χ.hasCompactSupport hsχ (fun x=>by rw [abs_of_nonneg χ.nonneg];exact χ.le_one) hDχ L
  have hSub : ball a r⊆ball (0 : Domain n) 1 :=
    hBall.trans (ball_subset_ball (by norm_num))
  have hULp : MemLp u 2 μ := hu.2.1.mono_measure (Measure.restrict_mono_set volume hSub)
  have hObsMeas : AEStronglyMeasurable (fun x=>L (u x)) μ :=
    L.continuous.comp_aestronglyMeasurable hULp.aestronglyMeasurable
  have hObsBound : ∀ᵐ x ∂μ,‖L (u x)‖≤‖L‖*M := by
    filter_upwards [huBound.filter_mono (ae_mono (Measure.restrict_mono_set volume hSub))] with x hx
    exact (L.le_opNorm (u x)).trans (mul_le_mul_of_nonneg_left hx (norm_nonneg _))
  obtain ⟨hFI,hZero⟩ := divergence_free_zeroBoundary_test (ballDomain a r) Z hZ hDiv hw
  change Integrable F μ at hFI
  change (∫x,F x ∂μ)=0 at hZero
  have hOriginalI : Integrable (fun x=>F x*L (u x)) μ := hFI.mul_bdd hObsMeas hObsBound
  have hInside : ∀ᵐ x ∂μ,b x=L (u x)-L c := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    dsimp only [b]
    rw [hχOne x (hBall hx),one_smul,L.map_sub]
  have hEq : (fun x=>F x*b x)=ᵐ[μ](fun x=>F x*L (u x)-F x*L c) := by
    filter_upwards [hInside] with x hx
    rw [hx]
    ring
  have hProduct : Integrable (fun x=>F x*b x) μ :=
    (hOriginalI.sub (hFI.mul_const (L c))).congr hEq.symm
  have hIntegral : (∫x,F x*b x ∂μ)=(∫x,F x*L (u x) ∂μ) := by
    rw [integral_congr_ae hEq,integral_sub hOriginalI (hFI.mul_const (L c)),
      integral_mul_const,hZero,zero_mul,sub_zero]
  obtain ⟨l,⟨_hAllI,_hLimit,hEstimate,hAgree⟩,_hUnique⟩ :=
    Hpair q a r hr Z hZ hDiv w Dw hw b (K*‖L‖*η) hbMeas (by positivity) hBMO
  rw [(hAgree hProduct).trans hIntegral] at hEstimate
  exact ⟨hOriginalI,hEstimate.trans_eq (by ring)⟩

end StationaryHarmonicMaps.Analysis

end
