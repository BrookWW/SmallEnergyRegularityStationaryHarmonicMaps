module

public import StationaryHarmonicMaps.Analysis.CoulombBoundaryCriticalMorrey

/-!
# One a priori threshold for the critical and stronger Morrey exponents

The same given Coulomb frame and connection satisfy both boundary bounds.
A common threshold is chosen before the original frame; its stronger-class
finite growth is used only to initiate absorption at that stronger exponent.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- One positive threshold controls the same original frame at the critical
and stronger exponents, with the original connection sizes on the right. -/
theorem exists_coulomb_critical_and_stronger_boundary_absorption (n : ℕ) (hn : 2≤n) (q : ℕ)
    (E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient (q*q))
    (R : Ambient (q*q) →L[ℝ] (Ambient q →L[ℝ] Ambient q))
    (hRE : ∀T,R (E T)=T) (hER : ∀z,E (R z)=z)
    (hE : ∀T : Ambient q →L[ℝ] Ambient q,‖E T‖^2=∑j : Fin q,‖T (EuclideanSpace.single j 1)‖^2)
    (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2) :
    ∃δ C : ℝ,0<δ ∧ 0<C ∧ ∀ (p : Domain n → Ambient (q*q)) (Dp : Domain n → Gradient n (q*q))
      (A : Domain n → Fin n → (Ambient q →L[ℝ] Ambient q)) (J K₀ K₁ : ℝ),
      MemW12 (ballDomain (0 : Domain n) 1) p Dp →
      (∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),star (R (p x))*R (p x)=1) →
      (∀i,MemLp (fun x=>A x i) 2 (volume.restrict (ball (0 : Domain n) 1))) →
      (∀i,∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),star (A x i)= -A x i) →
      criticalGradientMorreySquare Dp (ball (0 : Domain n) 1)≤ENNReal.ofReal (δ^2) →
      (∀a∈ball (0 : Domain n) 1,∀r : ℝ,0<r →
        (∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (Dp x))≤J*r^((n : ℝ)-2+γ)) →
      0≤K₀ → 0≤K₁ →
      criticalGradientMorreySquare (fun x i=>E (A x i)) (ball (0 : Domain n) 1)≤ENNReal.ofReal K₀ →
      (∀a∈ball (0 : Domain n) 1,∀r : ℝ,0<r →
        (∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (fun i=>E (A x i)))≤K₁*r^((n : ℝ)-2+γ)) →
      let Z := fun x i=>star (R (p x))*R (Dp x i)+star (R (p x))*A x i*R (p x)
      (∀ (ψ : Domain n → Ambient (q*q)) (Dψ : Domain n → Gradient n (q*q)),
        MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ →
        (∫x in ball (0 : Domain n) 1,∑i : Fin n,inner ℝ (E (Z x i)) (Dψ x i))=0) →
      (criticalGradientMorreySquare Dp (ball (0 : Domain n) 1)+
        criticalGradientMorreySquare (fun x i=>E (Z x i)) (ball (0 : Domain n) 1)≤ENNReal.ofReal (C*K₀)) ∧
      ∀a∈ball (0 : Domain n) 1,∀r : ℝ,0<r →
        ((∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (Dp x))≤C*K₁*r^((n : ℝ)-2+γ)) ∧
        ((∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (fun i=>E (Z x i)))≤C*K₁*r^((n : ℝ)-2+γ)) := by
  have hnR : (2 : ℝ)≤n := by exact_mod_cast hn
  obtain ⟨δ₀,C₀,hδ₀,hC₀,H₀⟩ := exists_coulomb_boundary_complete_criticalMorrey_bound n hn q E R hRE hER hE
  obtain ⟨δ₁,C₁,hδ₁,hC₁,H₁⟩ := exists_coulomb_boundary_joint_power_growth_absorption n hn q E R hRE hER hE
    ((n : ℝ)-2+γ) (by linarith only [hnR,hγ]) (by linarith only [hγTwo])
  let δ := min δ₀ δ₁
  let C := max C₀ C₁
  have hδ : 0<δ := lt_min hδ₀ hδ₁
  have hC : 0<C := hC₀.trans_le (le_max_left _ _)
  refine ⟨δ,C,hδ,hC,?_⟩
  intro p Dp A J K₀ K₁ hp hOrth hA hAskew hCritical hInitial hK₀ hK₁ hACritical hAGrowth Z hNatural
  have hSmall₀ : criticalGradientMorreySquare Dp (ball (0 : Domain n) 1)≤ENNReal.ofReal (δ₀^2) :=
    hCritical.trans (ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hδ.le (min_le_left _ _) 2))
  have hSmall₁ : criticalGradientMorreySquare Dp (ball (0 : Domain n) 1)≤ENNReal.ofReal (δ₁^2) :=
    hCritical.trans (ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hδ.le (min_le_right _ _) 2))
  constructor
  · exact (H₀ p Dp A K₀ hp hOrth hA hAskew hSmall₀ hK₀ hACritical hNatural).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _) hK₀))
  · intro a ha r hr
    have H := H₁ p Dp A J K₁ hp hOrth hA hAskew hSmall₁ hInitial hK₁ hAGrowth hNatural a ha r hr
    have hCoeff : C₁*K₁*r^((n : ℝ)-2+γ)≤C*K₁*r^((n : ℝ)-2+γ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) hK₁)
        (Real.rpow_nonneg hr.le _)
    exact ⟨H.1.trans hCoeff,H.2.trans hCoeff⟩

@[expose] def effectiveCoulombTwoExponentConstant (n : ℕ) : ℚ :=
  effectiveCoulombCriticalConstant n

theorem effectiveCoulombTwoExponentConstant_pos (n : ℕ) (hn : 1 ≤ n) :
    0 < effectiveCoulombTwoExponentConstant n := effectiveCoulombCriticalConstant_pos n hn

/-- One positive threshold controls the same original frame at the critical
and stronger exponents, with the original connection sizes on the right. -/
theorem effective_coulomb_critical_and_stronger_boundary_absorption (n : ℕ) (hn : 2≤n) (q : ℕ)
    (E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient (q*q))
    (R : Ambient (q*q) →L[ℝ] (Ambient q →L[ℝ] Ambient q))
    (hRE : ∀T,R (E T)=T) (hER : ∀z,E (R z)=z)
    (hE : ∀T : Ambient q →L[ℝ] Ambient q,‖E T‖^2=∑j : Fin q,‖T (EuclideanSpace.single j 1)‖^2)
    :
    ∀ (p : Domain n → Ambient (q*q)) (Dp : Domain n → Gradient n (q*q))
      (A : Domain n → Fin n → (Ambient q →L[ℝ] Ambient q)) (J K₀ K₁ : ℝ),
      MemW12 (ballDomain (0 : Domain n) 1) p Dp →
      (∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),star (R (p x))*R (p x)=1) →
      (∀i,MemLp (fun x=>A x i) 2 (volume.restrict (ball (0 : Domain n) 1))) →
      (∀i,∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),star (A x i)= -A x i) →
      criticalGradientMorreySquare Dp (ball (0 : Domain n) 1)≤ENNReal.ofReal ((effectiveCoulombAbsorptionAmplitude n q : ℝ)^2) →
      (∀a∈ball (0 : Domain n) 1,∀r : ℝ,0<r →
        (∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (Dp x))≤J*r^((n : ℝ)-1)) →
      0≤K₀ → 0≤K₁ →
      criticalGradientMorreySquare (fun x i=>E (A x i)) (ball (0 : Domain n) 1)≤ENNReal.ofReal K₀ →
      (∀a∈ball (0 : Domain n) 1,∀r : ℝ,0<r →
        (∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (fun i=>E (A x i)))≤K₁*r^((n : ℝ)-1)) →
      let Z := fun x i=>star (R (p x))*R (Dp x i)+star (R (p x))*A x i*R (p x)
      (∀ (ψ : Domain n → Ambient (q*q)) (Dψ : Domain n → Gradient n (q*q)),
        MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ →
        (∫x in ball (0 : Domain n) 1,∑i : Fin n,inner ℝ (E (Z x i)) (Dψ x i))=0) →
      (criticalGradientMorreySquare Dp (ball (0 : Domain n) 1)+
        criticalGradientMorreySquare (fun x i=>E (Z x i)) (ball (0 : Domain n) 1)≤ENNReal.ofReal ((effectiveCoulombTwoExponentConstant n : ℝ)*K₀)) ∧
      ∀a∈ball (0 : Domain n) 1,∀r : ℝ,0<r →
        ((∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (Dp x))≤(effectiveCoulombTwoExponentConstant n : ℝ)*K₁*r^((n : ℝ)-1)) ∧
        ((∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (fun i=>E (Z x i)))≤(effectiveCoulombTwoExponentConstant n : ℝ)*K₁*r^((n : ℝ)-1)) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have H₀ := effective_coulomb_boundary_complete_criticalMorrey_bound n hn q E R hRE hER hE
  have H₁ := effective_coulomb_boundary_joint_power_growth_absorption n hn q E R hRE hER hE
    ((n : ℝ) - 1) (by linarith only [hnR]) (by linarith)
  have hC₁ : 0 ≤ (effectiveCoulombJointConstant n : ℝ) := by
    exact_mod_cast (effectiveCoulombJointConstant_pos n (by omega)).le
  have hCoeff : (effectiveCoulombJointConstant n : ℝ) ≤ (effectiveCoulombTwoExponentConstant n : ℝ) := by
    simp only [effectiveCoulombTwoExponentConstant, effectiveCoulombCriticalConstant,
      Rat.cast_mul, Rat.cast_ofNat]
    linarith only [hC₁]
  intro p Dp A J K₀ K₁ hp hOrth hA hAskew hCritical hInitial hK₀ hK₁ hACritical hAGrowth Z hNatural
  constructor
  · exact H₀ p Dp A K₀ hp hOrth hA hAskew hCritical hK₀ hACritical hNatural
  · intro a ha r hr
    have H := H₁ p Dp A J K₁ hp hOrth hA hAskew hCritical hInitial hK₁ hAGrowth hNatural a ha r hr
    have hScale := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCoeff hK₁)
      (Real.rpow_nonneg hr.le ((n : ℝ) - 1))
    exact ⟨H.1.trans hScale, H.2.trans hScale⟩

end StationaryHarmonicMaps.Analysis

end
