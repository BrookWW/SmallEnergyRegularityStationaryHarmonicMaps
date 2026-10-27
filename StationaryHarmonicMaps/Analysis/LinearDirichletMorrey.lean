module

public import StationaryHarmonicMaps.Analysis.LinearFluxMorrey

/-! # An actual zero-boundary response with interior critical control

The Dirichlet gradient projection of minus the original field produces
an actual native zero-boundary solution of div(Df+F)=0. The same response
retains its constant-one total energy bound and the proved interior
complete critical estimate.
-/

public section

open HarmonicMaps MeasureTheory Filter Set

namespace StationaryHarmonicMaps.Analysis

/-- Original L2 critical forcing produces a genuine W0 response with the correct flux sign and the same response's interior complete bound. -/
theorem exists_linear_dirichlet_response_interior_criticalMorrey (n : ℕ) (hn : 2≤n) :
    ∃ C : ℝ,0<C ∧ ∀ (q : ℕ) (F : Domain n → Gradient n q) (K : ℝ),
      (∀ i,MemLp (fun x => F x i) 2 (volume.restrict (Metric.ball (0 : Domain n) 1))) →
      0≤K → criticalGradientMorreySquare F (Metric.ball (0 : Domain n) 1)≤ENNReal.ofReal K →
      ∃ (f : Domain n → Ambient q) (Df : Domain n → Gradient n q),
        HasZeroBoundaryValues (ballDomain (0 : Domain n) 1) f Df ∧
        (∫ x in Metric.ball (0 : Domain n) 1,hsNormSq (Df x))≤
          ∫ x in Metric.ball (0 : Domain n) 1,hsNormSq (F x) ∧
        HolderToCK.WeakPoissonOn (ballDomain (0 : Domain n) 1)
          (fun x i => Df x i+F x i) (fun _ => (0 : Ambient q)) ∧
        criticalGradientMorreySquare Df (Metric.ball (0 : Domain n) (1/4 : ℝ))≤ENNReal.ofReal (C*K) := by
  obtain ⟨C₀,hC₀,hMorrey⟩ := exists_linear_flux_interior_criticalMorrey_bound n hn
  refine ⟨2*C₀,by positivity,?_⟩
  intro q F K hF hK hCritical
  let U := Metric.ball (0 : Domain n) 1
  let G := fun x i => -F x i
  obtain ⟨f,Df,hf,hEnergy,hTests⟩ := exists_dirichlet_gradient_projection
    (by omega : 1≤n) (0 : Domain n) (by norm_num : (0 : ℝ)<1) G (fun i => (hF i).neg)
  have hEnergyF : (∫ x in U,hsNormSq (Df x))≤∫ x in U,hsNormSq (F x) := by
    simpa only [G,hsNormSq,norm_neg] using hEnergy
  have hEquation : HolderToCK.WeakPoissonOn (ballDomain (0 : Domain n) 1)
      (fun x i => Df x i+F x i) (fun _ => (0 : Ambient q)) := by
    refine ⟨locallyIntegrableOn_zero,?_⟩
    intro ψ hψ hc hs
    have H := hTests ψ hψ hc hs
    have hPair (x : Domain n) :
        (∑ i : Fin n,inner ℝ (Df x i+F x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1)))=
        (∑ i : Fin n,inner ℝ (Df x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1)))-
          (∑ i : Fin n,inner ℝ (G x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1))) := by
      simp only [G,inner_add_left,inner_neg_left,Finset.sum_add_distrib,
        Finset.sum_neg_distrib,sub_neg_eq_add]
    refine ⟨(H.1.sub H.2.1).congr (Eventually.of_forall fun x => (hPair x).symm),?_,?_⟩
    · simp only [inner_zero_left]
      exact integrable_zero _ _ _
    · simp only [inner_zero_left,integral_zero,neg_zero]
      change (∫ x in Metric.ball (0 : Domain n) 1,
        ∑ i : Fin n,inner ℝ (Df x i+F x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1)))=0
      rw [integral_congr_ae (Eventually.of_forall hPair),integral_sub H.1 H.2.1,H.2.2,sub_self]
  have hForce : (∫ x in U,hsNormSq (F x))≤K := by
    have H := integral_hsNormSq_le_of_criticalMorrey F
      (Metric.mem_ball_self (by norm_num : (0 : ℝ)<1)) (by norm_num : (0 : ℝ)<1) hK
      (subset_inter (Subset.refl U) (Subset.refl U)) hF hCritical
    simpa only [Real.one_rpow,mul_one] using H
  have hBound := hMorrey q f Df F K hf.1 hF hK hCritical hEquation
  refine ⟨f,Df,hf,hEnergyF,hEquation,hBound.trans ?_⟩
  apply ENNReal.ofReal_le_ofReal
  have H : (∫ x in U,hsNormSq (Df x))+K≤2*K := by linarith only [hEnergyF,hForce]
  exact (mul_le_mul_of_nonneg_left H hC₀.le).trans_eq (by ring)

end StationaryHarmonicMaps.Analysis
end
