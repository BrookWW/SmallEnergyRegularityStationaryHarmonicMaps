module

public import StationaryHarmonicMaps.Analysis.HodgeDirichletUniqueness
public import HarmonicMaps.Analysis.SobolevDifference
public import HolderToCK.Analysis.WeakPoissonLocality

/-!
# Actual harmonic decomposition of a native linear flux solution

The true zero-boundary response is constructed from minus the original
L2 forcing field. The original zero-divergence flux equation therefore
leaves a genuine native harmonic remainder. Testing its actual equation
against the produced W0 response gives exact energy orthogonality and
the coefficient-one decomposition of the original Dirichlet energy.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped ContDiff

namespace StationaryHarmonicMaps.Analysis

/-- A genuine native solution of div(DV+F)=0 has an actual W0 response to -F and a same-map harmonic remainder, with exact orthogonal energy decomposition. -/
theorem exists_linear_flux_harmonic_decomposition_ball {n q : ℕ} (hn : 1≤n)
    (a : Domain n) (R : PositiveRadius)
    (V : Domain n → Ambient q) (DV F : Domain n → Gradient n q)
    (hV : MemW12 (ballDomain a R.val) V DV)
    (hF : ∀ i,MemLp (fun x => F x i) 2 (volume.restrict (Metric.ball a R.val)))
    (hEquation : HolderToCK.WeakPoissonOn (ballDomain a R.val)
      (fun x i => DV x i+F x i) (fun _ => (0 : Ambient q))) :
    ∃ (f : Domain n → Ambient q) (Df : Domain n → Gradient n q),
      HasZeroBoundaryValues (ballDomain a R.val) f Df ∧
      (∫ x in Metric.ball a R.val,hsNormSq (Df x))≤∫ x in Metric.ball a R.val,hsNormSq (F x) ∧
      let h := V-f
      let Dh := fun x i => DV x i-Df x i
      MemW12 (ballDomain a R.val) h Dh ∧
      HolderToCK.WeakPoissonOn (ballDomain a R.val) (fun x i => Df x i+F x i) (fun _ => (0 : Ambient q)) ∧
      HolderToCK.WeakPoissonOn (ballDomain a R.val) Dh (fun _ => (0 : Ambient q)) ∧
      IntegrableOn (fun x => ∑ i : Fin n,inner ℝ (Dh x i) (Df x i)) (Metric.ball a R.val) volume ∧
      (∫ x in Metric.ball a R.val,∑ i : Fin n,inner ℝ (Dh x i) (Df x i))=0 ∧
      (∫ x in Metric.ball a R.val,hsNormSq (DV x))=
        (∫ x in Metric.ball a R.val,hsNormSq (Dh x))+(∫ x in Metric.ball a R.val,hsNormSq (Df x)) := by
  let Ω := ballDomain a R.val
  let μ := volume.restrict (Metric.ball a R.val)
  let G := fun x i => -F x i
  obtain ⟨f,Df,hf,hEf,hTests⟩ := exists_dirichlet_gradient_projection hn a R.property G (fun i => (hF i).neg)
  have hEfBound : (∫ x in Metric.ball a R.val,hsNormSq (Df x))≤∫ x in Metric.ball a R.val,hsNormSq (F x) := by
    simpa only [G,hsNormSq,norm_neg] using hEf
  let h := V-f
  let Dh := fun x i => DV x i-Df x i
  have hh : MemW12 Ω h Dh := hV.sub hf.1
  have hHarmonic : HolderToCK.WeakPoissonOn Ω Dh (fun _ => (0 : Ambient q)) := by
    refine ⟨locallyIntegrableOn_zero,?_⟩
    intro ψ hψ hc hs
    have hDψ (i : Fin n) : MemLp (fun x => fderiv ℝ ψ x (EuclideanSpace.single i 1)) 2 μ :=
      (((hψ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
        (hc.fderiv_apply ℝ (EuclideanSpace.single i 1))).mono_measure Measure.restrict_le_self
    have hIV : Integrable (fun x => ∑ i : Fin n,inner ℝ (DV x i)
        (fderiv ℝ ψ x (EuclideanSpace.single i 1))) μ :=
      integrable_finsetSum _ (fun i _ => HolderToCK.integrable_inner_of_memLp_two (hV.2.2 i) (hDψ i))
    have hIF : Integrable (fun x => ∑ i : Fin n,inner ℝ (F x i)
        (fderiv ℝ ψ x (EuclideanSpace.single i 1))) μ :=
      integrable_finsetSum _ (fun i _ => HolderToCK.integrable_inner_of_memLp_two (hF i) (hDψ i))
    have Hf := hTests ψ hψ hc hs
    have HV := hEquation.2 ψ hψ hc hs
    have hDfEq : (∫ x in Metric.ball a R.val,∑ i : Fin n,inner ℝ (Df x i)
        (fderiv ℝ ψ x (EuclideanSpace.single i 1)))=
        -(∫ x in Metric.ball a R.val,∑ i : Fin n,inner ℝ (F x i)
          (fderiv ℝ ψ x (EuclideanSpace.single i 1))) := by
      rw [Hf.2.2]
      simp only [G,inner_neg_left,Finset.sum_neg_distrib,integral_neg]
    have hVZero : (∫ x in Metric.ball a R.val,∑ i : Fin n,inner ℝ (DV x i)
        (fderiv ℝ ψ x (EuclideanSpace.single i 1)))+
        (∫ x in Metric.ball a R.val,∑ i : Fin n,inner ℝ (F x i)
          (fderiv ℝ ψ x (EuclideanSpace.single i 1)))=0 := by
      have H := HV.2.2
      simp only [inner_add_left,Finset.sum_add_distrib,inner_zero_left,integral_zero,neg_zero] at H
      change (∫ x,(∑ i : Fin n,inner ℝ (DV x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1)))+
        (∑ i : Fin n,inner ℝ (F x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1))) ∂μ)=0 at H
      rw [integral_add hIV hIF] at H
      exact H
    have hPair (x : Domain n) :
        (∑ i : Fin n,inner ℝ (Dh x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1)))=
        (∑ i : Fin n,inner ℝ (DV x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1)))-
          (∑ i : Fin n,inner ℝ (Df x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1))) := by
      simp only [Dh,inner_sub_left,Finset.sum_sub_distrib]
    refine ⟨(hIV.sub Hf.1).congr (Eventually.of_forall fun x => (hPair x).symm),?_,?_⟩
    · simp only [inner_zero_left]
      exact integrable_zero _ _ _
    · simp only [inner_zero_left,integral_zero,neg_zero]
      change (∫ x,∑ i : Fin n,inner ℝ (Dh x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1)) ∂μ)=0
      have hDfInt : Integrable (fun x => ∑ i : Fin n,inner ℝ (Df x i)
          (fderiv ℝ ψ x (EuclideanSpace.single i 1))) μ := Hf.1
      change (∫ x,∑ i : Fin n,inner ℝ (Df x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1)) ∂μ)=
        -(∫ x,∑ i : Fin n,inner ℝ (F x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1)) ∂μ) at hDfEq
      rw [integral_congr_ae (Eventually.of_forall hPair),integral_sub hIV hDfInt,hDfEq]
      simpa only [inner_zero_left,integral_zero,neg_zero,sub_neg_eq_add] using hVZero
  have hResponse : HolderToCK.WeakPoissonOn Ω (fun x i => Df x i+F x i) (fun _ => (0 : Ambient q)) := by
    have H := hEquation.sub hHarmonic
    apply H.congr
    · exact Eventually.of_forall fun x => by funext i;dsimp only [Dh];abel
    · exact Eventually.of_forall fun _ => sub_zero _
  have hCross := gradient_pairing_eq_on_zeroBoundary_of_smooth Ω Dh (fun _ _ => (0 : Ambient q))
    hh.2.2 (fun _ => MemLp.zero) (fun ψ hψ hc hs => by
      have H := (hHarmonic.2 ψ hψ hc hs).2.2
      simpa only [inner_zero_left,Finset.sum_const_zero,integral_zero,neg_zero] using H) hf
  have hCrossZero : (∫ x in Metric.ball a R.val,∑ i : Fin n,inner ℝ (Dh x i) (Df x i))=0 := by
    have H := hCross.2.2
    change (∫ x in Metric.ball a R.val,∑ i : Fin n,inner ℝ (Dh x i) (Df x i))=
      (∫ x in Metric.ball a R.val,∑ i : Fin n,inner ℝ (0 : Ambient q) (Df x i)) at H
    simpa only [inner_zero_left,Finset.sum_const_zero,integral_zero] using H
  have hCrossI : IntegrableOn (fun x => ∑ i : Fin n,inner ℝ (Dh x i) (Df x i))
      (Metric.ball a R.val) volume := hCross.1
  have hDhI : IntegrableOn (fun x => hsNormSq (Dh x)) (Metric.ball a R.val) volume := hh.integrable_hsNormSq
  have hFirstI : IntegrableOn (fun x => hsNormSq (Dh x)+
      2*(∑ i : Fin n,inner ℝ (Dh x i) (Df x i))) (Metric.ball a R.val) volume :=
    (hDhI.add (hCrossI.const_mul 2)).congr (Eventually.of_forall fun _ => rfl)
  have hPoint (x : Domain n) : hsNormSq (DV x)=hsNormSq (Dh x)+
      2*(∑ i : Fin n,inner ℝ (Dh x i) (Df x i))+hsNormSq (Df x) := by
    have H (i : Fin n) : DV x i=Dh x i+Df x i := by dsimp only [Dh];abel
    simp only [hsNormSq,H,norm_add_sq_real,Finset.sum_add_distrib,Finset.mul_sum]
  have hEnergy : (∫ x in Metric.ball a R.val,hsNormSq (DV x))=
      (∫ x in Metric.ball a R.val,hsNormSq (Dh x))+(∫ x in Metric.ball a R.val,hsNormSq (Df x)) := by
    rw [integral_congr_ae (Eventually.of_forall hPoint),
      integral_add hFirstI hf.1.integrable_hsNormSq,
      integral_add hDhI (hCrossI.const_mul 2),integral_const_mul,hCrossZero,mul_zero,add_zero]
  exact ⟨f,Df,hf,hEfBound,hh,hResponse,hHarmonic,hCross.1,hCrossZero,hEnergy⟩

end StationaryHarmonicMaps.Analysis

end
