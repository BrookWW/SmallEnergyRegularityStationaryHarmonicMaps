module

public import StationaryHarmonicMaps.Analysis.GeometricIteration
public import StationaryHarmonicMaps.Analysis.LinearFluxEnergyDecay
public import StationaryHarmonicMaps.Analysis.CriticalMorreyIntegralBounds
public import HolderToCK.Analysis.WeakPoissonLocality
public import HarmonicMaps.SobolevRestriction
public import HarmonicMaps.Analysis.SobolevDifference

/-! # Actual localized forcing splits of zero-boundary linear solutions

A genuine Dirichlet response to the literal restricted original field is
subtracted from the same original solution. The remainder retains zero
trace and has forcing identically zero in the same query ball. All
localized energies refer to the original fields.
-/

public section

open HarmonicMaps MeasureTheory Filter Set

namespace StationaryHarmonicMaps.Analysis

private theorem exists_zeroBoundary_flux_response {n q : ℕ} (hn : 1≤n)
    (F : Domain n → Gradient n q)
    (hF : ∀ i,MemLp (fun x => F x i) 2 (volume.restrict (Metric.ball (0 : Domain n) 1))) :
    ∃ (w : Domain n → Ambient q) (Dw : Domain n → Gradient n q),
      HasZeroBoundaryValues (ballDomain (0 : Domain n) 1) w Dw ∧
      (∫ x in Metric.ball (0 : Domain n) 1,hsNormSq (Dw x))≤
        ∫ x in Metric.ball (0 : Domain n) 1,hsNormSq (F x) ∧
      HolderToCK.WeakPoissonOn (ballDomain (0 : Domain n) 1)
        (fun x i => Dw x i+F x i) (fun _ => (0 : Ambient q)) := by
  let G := fun x i => -F x i
  obtain ⟨w,Dw,hw,hEnergy,hTests⟩ := exists_dirichlet_gradient_projection hn
    (0 : Domain n) (by norm_num : (0 : ℝ)<1) G (fun i => (hF i).neg)
  refine ⟨w,Dw,hw,?_,locallyIntegrableOn_zero,?_⟩
  · simpa only [G,hsNormSq,norm_neg] using hEnergy
  · intro ψ hψ hc hs
    have H := hTests ψ hψ hc hs
    have hPair (x : Domain n) :
        (∑ i : Fin n,inner ℝ (Dw x i+F x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1)))=
        (∑ i : Fin n,inner ℝ (Dw x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1)))-
          (∑ i : Fin n,inner ℝ (G x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1))) := by
      simp only [G,inner_add_left,inner_neg_left,Finset.sum_add_distrib,
        Finset.sum_neg_distrib,sub_neg_eq_add]
    refine ⟨(H.1.sub H.2.1).congr (Eventually.of_forall fun x => (hPair x).symm),?_,?_⟩
    · simp only [inner_zero_left]
      exact integrable_zero _ _ _
    · simp only [inner_zero_left,integral_zero,neg_zero]
      change (∫ x in Metric.ball (0 : Domain n) 1,
        ∑ i : Fin n,inner ℝ (Dw x i+F x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1)))=0
      rw [integral_congr_ae (Eventually.of_forall hPair),integral_sub H.1 H.2.1,H.2.2,sub_self]

/-- Every actual zero-boundary linear solution admits a real restricted-forcing response and a same-query off-support zero-boundary remainder. -/
theorem exists_localized_dirichlet_forcing_split {n q : ℕ} (hn : 1≤n)
    (f : Domain n → Ambient q) (Df F : Domain n → Gradient n q)
    (hf : HasZeroBoundaryValues (ballDomain (0 : Domain n) 1) f Df)
    (hF : ∀ i,MemLp (fun x => F x i) 2 (volume.restrict (Metric.ball (0 : Domain n) 1)))
    (hEquation : HolderToCK.WeakPoissonOn (ballDomain (0 : Domain n) 1)
      (fun x i => Df x i+F x i) (fun _ => (0 : Ambient q)))
    (a : Domain n) (r : ℝ) :
    let F₁ := (Metric.ball a r).indicator F
    ∃ (w : Domain n → Ambient q) (Dw : Domain n → Gradient n q),
      HasZeroBoundaryValues (ballDomain (0 : Domain n) 1) w Dw ∧
      (∫ x in Metric.ball (0 : Domain n) 1,hsNormSq (Dw x))≤
        ∫ x in Metric.ball a r∩Metric.ball (0 : Domain n) 1,hsNormSq (F x) ∧
      HolderToCK.WeakPoissonOn (ballDomain (0 : Domain n) 1)
        (fun x i => Dw x i+F₁ x i) (fun _ => (0 : Ambient q)) ∧
      let h := f-w
      let Dh := fun x i => Df x i-Dw x i
      let G := fun x i => F₁ x i-F x i
      HasZeroBoundaryValues (ballDomain (0 : Domain n) 1) h Dh ∧
      (∀ i,MemLp (fun x => G x i) 2 (volume.restrict (Metric.ball (0 : Domain n) 1))) ∧
      HolderToCK.WeakPoissonOn (ballDomain (0 : Domain n) 1)
        (fun x i => Dh x i-G x i) (fun _ => (0 : Ambient q)) ∧
      (∀ x∈Metric.ball a r,G x=0) ∧
      (∫ x in Metric.ball a r∩Metric.ball (0 : Domain n) 1,hsNormSq (Dh x))≤
        2*(∫ x in Metric.ball a r∩Metric.ball (0 : Domain n) 1,hsNormSq (Df x))+
          2*(∫ x in Metric.ball a r∩Metric.ball (0 : Domain n) 1,hsNormSq (F x)) := by
  classical
  dsimp only
  let F₁ := (Metric.ball a r).indicator F
  have hF₁ (i : Fin n) : MemLp (fun x => F₁ x i) 2 (volume.restrict (Metric.ball (0 : Domain n) 1)) := by
    have H : MemLp ((Metric.ball a r).indicator (fun x => F x i)) 2
        (volume.restrict (Metric.ball (0 : Domain n) 1)) := (hF i).indicator measurableSet_ball
    apply (memLp_congr_ae (f := (Metric.ball a r).indicator (fun x => F x i))
      (g := fun x => F₁ x i) ?_).mp H
    exact Eventually.of_forall fun x => by
      by_cases hx : x∈Metric.ball a r
      · simp only [F₁,indicator_of_mem hx]
      · simp only [F₁,indicator_of_notMem hx,Pi.zero_apply]
  obtain ⟨w,Dw,hw,hEnergy,hWEq⟩ := exists_zeroBoundary_flux_response hn F₁ hF₁
  have hEnergyEq : (∫ x in Metric.ball (0 : Domain n) 1,hsNormSq (F₁ x))=
      ∫ x in Metric.ball a r∩Metric.ball (0 : Domain n) 1,hsNormSq (F x) := by
    have hPoint : (fun x => hsNormSq (F₁ x))=(Metric.ball a r).indicator (fun x => hsNormSq (F x)) := by
      funext x
      by_cases hx : x∈Metric.ball a r
      · simp only [F₁,indicator_of_mem hx]
      · simp only [F₁,indicator_of_notMem hx,hsNormSq,Pi.zero_apply,norm_zero,zero_pow (by decide : (2 : ℕ)≠0),Finset.sum_const_zero]
    rw [hPoint,setIntegral_indicator measurableSet_ball,inter_comm]
  have hWE : (∫ x in Metric.ball (0 : Domain n) 1,hsNormSq (Dw x))≤
      ∫ x in Metric.ball a r∩Metric.ball (0 : Domain n) 1,hsNormSq (F x) :=
    hEnergy.trans_eq hEnergyEq
  let h := f-w
  let Dh := fun x i => Df x i-Dw x i
  let G := fun x i => F₁ x i-F x i
  have hh : HasZeroBoundaryValues (ballDomain (0 : Domain n) 1) h Dh := zeroBoundary_sub hf hw
  have hGEq : HolderToCK.WeakPoissonOn (ballDomain (0 : Domain n) 1)
      (fun x i => Dh x i-G x i) (fun _ => (0 : Ambient q)) := by
    have H := hEquation.sub hWEq
    apply H.congr
    · exact Eventually.of_forall fun x => by funext i;dsimp only [Dh,G];abel
    · exact Eventually.of_forall fun _ => sub_zero _
  refine ⟨w,Dw,hw,hWE,hWEq,hh,(fun i => (hF₁ i).sub (hF i)),hGEq,?_,?_⟩
  · intro x hx
    funext i
    simp only [indicator_of_mem hx,sub_self,Pi.zero_apply]
  · let S := Metric.ball a r∩Metric.ball (0 : Domain n) 1
    have hDfI : IntegrableOn (fun x => hsNormSq (Df x)) S volume :=
      hf.1.integrable_hsNormSq.mono_set inter_subset_right
    have hDwI : IntegrableOn (fun x => hsNormSq (Dw x)) S volume :=
      hw.1.integrable_hsNormSq.mono_set inter_subset_right
    have hDhI : IntegrableOn (fun x => hsNormSq (Dh x)) S volume :=
      hh.1.integrable_hsNormSq.mono_set inter_subset_right
    have hPoint (x : Domain n) : hsNormSq (Dh x)≤2*hsNormSq (Df x)+2*hsNormSq (Dw x) := by
      have HC (i : Fin n) : ‖Dh x i‖^2≤2*‖Df x i‖^2+2*‖Dw x i‖^2 := by
        dsimp only [Dh]
        rw [norm_sub_sq_real]
        nlinarith only [neg_le_abs (inner ℝ (Df x i) (Dw x i)),
          abs_real_inner_le_norm (Df x i) (Dw x i),sq_nonneg (‖Df x i‖-‖Dw x i‖)]
      calc
        _ ≤ ∑ i : Fin n,(2*‖Df x i‖^2+2*‖Dw x i‖^2) := Finset.sum_le_sum fun i _ => HC i
        _ = _ := by simp only [Finset.sum_add_distrib,Finset.mul_sum,hsNormSq]
    have hLocalW : (∫ x in S,hsNormSq (Dw x))≤∫ x in Metric.ball (0 : Domain n) 1,hsNormSq (Dw x) :=
      setIntegral_mono_set hw.1.integrable_hsNormSq (Eventually.of_forall fun _ => hsNormSq_nonneg _)
        (Eventually.of_forall fun _ hx => hx.2)
    calc
      _ ≤ ∫ x in S,2*hsNormSq (Df x)+2*hsNormSq (Dw x) :=
        integral_mono hDhI ((hDfI.const_mul 2).add (hDwI.const_mul 2)) hPoint
      _ = 2*(∫ x in S,hsNormSq (Df x))+2*(∫ x in S,hsNormSq (Dw x)) := by
        rw [integral_add (hDfI.const_mul 2) (hDwI.const_mul 2),integral_const_mul,integral_const_mul]
      _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left (hLocalW.trans hWE) (by norm_num))

end StationaryHarmonicMaps.Analysis
end
