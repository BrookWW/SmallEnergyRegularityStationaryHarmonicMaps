module

public import StationaryHarmonicMaps.Analysis.CoulombBoundaryAbsorption
public import StationaryHarmonicMaps.Analysis.CriticalMorreyPowerGrowth

/-!
# The full critical a priori bound for the original natural Coulomb frame

The original critical supremum itself supplies finite critical growth.
Boundary absorption then controls the same original gradient and same
connection on every truncated ball, and returns the joint literal full
critical supremum bound on the entire unit ball.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- An original native natural Coulomb frame with small original critical
norm has its complete gradient and connection critical squares controlled
by the original connection data. The frame is an a priori input. -/
theorem exists_coulomb_boundary_complete_criticalMorrey_bound (n : ℕ) (hn : 2≤n) (q : ℕ)
    (E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient (q*q))
    (R : Ambient (q*q) →L[ℝ] (Ambient q →L[ℝ] Ambient q))
    (hRE : ∀T,R (E T)=T) (hER : ∀z,E (R z)=z)
    (hE : ∀T : Ambient q →L[ℝ] Ambient q,‖E T‖^2=∑j : Fin q,‖T (EuclideanSpace.single j 1)‖^2) :
    ∃δ C : ℝ,0<δ ∧ 0<C ∧ ∀ (p : Domain n → Ambient (q*q)) (Dp : Domain n → Gradient n (q*q))
      (A : Domain n → Fin n → (Ambient q →L[ℝ] Ambient q)) (K : ℝ),
      MemW12 (ballDomain (0 : Domain n) 1) p Dp →
      (∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),star (R (p x))*R (p x)=1) →
      (∀i,MemLp (fun x=>A x i) 2 (volume.restrict (ball (0 : Domain n) 1))) →
      (∀i,∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),star (A x i)= -A x i) →
      criticalGradientMorreySquare Dp (ball (0 : Domain n) 1)≤ENNReal.ofReal (δ^2) → 0≤K →
      criticalGradientMorreySquare (fun x i=>E (A x i)) (ball (0 : Domain n) 1)≤ENNReal.ofReal K →
      let Z := fun x i=>star (R (p x))*R (Dp x i)+star (R (p x))*A x i*R (p x)
      (∀ (ψ : Domain n → Ambient (q*q)) (Dψ : Domain n → Gradient n (q*q)),
        MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ →
        (∫x in ball (0 : Domain n) 1,∑i : Fin n,inner ℝ (E (Z x i)) (Dψ x i))=0) →
      criticalGradientMorreySquare Dp (ball (0 : Domain n) 1)+
        criticalGradientMorreySquare (fun x i=>E (Z x i)) (ball (0 : Domain n) 1)≤
          ENNReal.ofReal (C*K) := by
  have hnR : (2 : ℝ)≤n := by exact_mod_cast hn
  obtain ⟨δ,C,hδ,hC,H⟩ := exists_coulomb_boundary_joint_power_growth_absorption n hn q E R hRE hER hE
    ((n : ℝ)-2) (by linarith only [hnR]) (by linarith)
  refine ⟨δ,2*C,hδ,by positivity,?_⟩
  intro p Dp A K hp hOrth hA hAskew hCritical hK hACritical Z hNatural
  have hDpGrowth (a : Domain n) (ha : a∈ball (0 : Domain n) 1) (r : ℝ) (hr : 0<r) :
      (∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (Dp x))≤δ^2*r^((n : ℝ)-2) :=
    integral_hsNormSq_le_of_criticalMorrey Dp ha hr (sq_nonneg δ) (Subset.refl _)
      (fun i=>(hp.2.2 i).mono_measure (Measure.restrict_mono_set volume inter_subset_right)) hCritical
  have hEA (i : Fin n) : MemLp (fun x=>E (A x i)) 2 (volume.restrict (ball (0 : Domain n) 1)) :=
    E.lipschitz.comp_memLp (map_zero E) (hA i)
  have hAGrowth (a : Domain n) (ha : a∈ball (0 : Domain n) 1) (r : ℝ) (hr : 0<r) :
      (∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (fun i=>E (A x i)))≤K*r^((n : ℝ)-2) :=
    integral_hsNormSq_le_of_criticalMorrey _ ha hr hK (Subset.refl _)
      (fun i=>(hEA i).mono_measure (Measure.restrict_mono_set volume inter_subset_right)) hACritical
  have hJoint := H p Dp A (δ^2) K hp hOrth hA hAskew hCritical hDpGrowth hK hAGrowth hNatural
  obtain ⟨_hZ,hEZ,_hSkew⟩ := frame_connection_memLp_and_skew E R hER hE p Dp hp hOrth A hA hAskew
  have hDpBound := criticalGradientMorreySquare_le_of_truncated_power_growth Dp
    (ball (0 : Domain n) 1) hp.2.2 (C*K) (fun a ha r hr=>(hJoint a ha r hr).1)
  have hZBound := criticalGradientMorreySquare_le_of_truncated_power_growth (fun x i=>E (Z x i))
    (ball (0 : Domain n) 1) hEZ (C*K) (fun a ha r hr=>(hJoint a ha r hr).2)
  exact (add_le_add hDpBound hZBound).trans_eq (by
    rw [←ENNReal.ofReal_add (by positivity : 0≤C*K) (by positivity : 0≤C*K)]
    congr 1
    ring)

@[expose] def effectiveCoulombCriticalConstant (n : ℕ) : ℚ :=
  2 * effectiveCoulombJointConstant n

theorem effectiveCoulombCriticalConstant_pos (n : ℕ) (hn : 1 ≤ n) :
    0 < effectiveCoulombCriticalConstant n := by
  have H := effectiveCoulombJointConstant_pos n hn
  unfold effectiveCoulombCriticalConstant
  positivity

/-- An original native natural Coulomb frame with small original critical
norm has its complete gradient and connection critical squares controlled
by the original connection data. The frame is an a priori input. -/
theorem effective_coulomb_boundary_complete_criticalMorrey_bound (n : ℕ) (hn : 2≤n) (q : ℕ)
    (E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient (q*q))
    (R : Ambient (q*q) →L[ℝ] (Ambient q →L[ℝ] Ambient q))
    (hRE : ∀T,R (E T)=T) (hER : ∀z,E (R z)=z)
    (hE : ∀T : Ambient q →L[ℝ] Ambient q,‖E T‖^2=∑j : Fin q,‖T (EuclideanSpace.single j 1)‖^2) :
    ∀ (p : Domain n → Ambient (q*q)) (Dp : Domain n → Gradient n (q*q))
      (A : Domain n → Fin n → (Ambient q →L[ℝ] Ambient q)) (K : ℝ),
      MemW12 (ballDomain (0 : Domain n) 1) p Dp →
      (∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),star (R (p x))*R (p x)=1) →
      (∀i,MemLp (fun x=>A x i) 2 (volume.restrict (ball (0 : Domain n) 1))) →
      (∀i,∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),star (A x i)= -A x i) →
      criticalGradientMorreySquare Dp (ball (0 : Domain n) 1)≤ENNReal.ofReal ((effectiveCoulombAbsorptionAmplitude n q : ℝ)^2) → 0≤K →
      criticalGradientMorreySquare (fun x i=>E (A x i)) (ball (0 : Domain n) 1)≤ENNReal.ofReal K →
      let Z := fun x i=>star (R (p x))*R (Dp x i)+star (R (p x))*A x i*R (p x)
      (∀ (ψ : Domain n → Ambient (q*q)) (Dψ : Domain n → Gradient n (q*q)),
        MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ →
        (∫x in ball (0 : Domain n) 1,∑i : Fin n,inner ℝ (E (Z x i)) (Dψ x i))=0) →
      criticalGradientMorreySquare Dp (ball (0 : Domain n) 1)+
        criticalGradientMorreySquare (fun x i=>E (Z x i)) (ball (0 : Domain n) 1)≤
          ENNReal.ofReal ((effectiveCoulombCriticalConstant n : ℝ)*K) := by
  have hnR : (2 : ℝ)≤n := by exact_mod_cast hn
  let δ : ℝ := effectiveCoulombAbsorptionAmplitude n q
  let C : ℝ := effectiveCoulombJointConstant n
  have hC : 0 < C := by
    change 0 < (effectiveCoulombJointConstant n : ℝ)
    exact_mod_cast effectiveCoulombJointConstant_pos n (by omega)
  have H := effective_coulomb_boundary_joint_power_growth_absorption n hn q E R hRE hER hE
    ((n : ℝ)-2) (by linarith only [hnR]) (by linarith)
  have hEq : (effectiveCoulombCriticalConstant n : ℝ) = 2 * C := by
    simp only [effectiveCoulombCriticalConstant, Rat.cast_mul, Rat.cast_ofNat, C]
  rw [hEq]
  intro p Dp A K hp hOrth hA hAskew hCritical hK hACritical Z hNatural
  have hDpGrowth (a : Domain n) (ha : a∈ball (0 : Domain n) 1) (r : ℝ) (hr : 0<r) :
      (∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (Dp x))≤δ^2*r^((n : ℝ)-2) :=
    integral_hsNormSq_le_of_criticalMorrey Dp ha hr (sq_nonneg δ) (Subset.refl _)
      (fun i=>(hp.2.2 i).mono_measure (Measure.restrict_mono_set volume inter_subset_right)) hCritical
  have hEA (i : Fin n) : MemLp (fun x=>E (A x i)) 2 (volume.restrict (ball (0 : Domain n) 1)) :=
    E.lipschitz.comp_memLp (map_zero E) (hA i)
  have hAGrowth (a : Domain n) (ha : a∈ball (0 : Domain n) 1) (r : ℝ) (hr : 0<r) :
      (∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (fun i=>E (A x i)))≤K*r^((n : ℝ)-2) :=
    integral_hsNormSq_le_of_criticalMorrey _ ha hr hK (Subset.refl _)
      (fun i=>(hEA i).mono_measure (Measure.restrict_mono_set volume inter_subset_right)) hACritical
  have hJoint := H p Dp A (δ^2) K hp hOrth hA hAskew hCritical hDpGrowth hK hAGrowth hNatural
  obtain ⟨_hZ,hEZ,_hSkew⟩ := frame_connection_memLp_and_skew E R hER hE p Dp hp hOrth A hA hAskew
  have hDpBound := criticalGradientMorreySquare_le_of_truncated_power_growth Dp
    (ball (0 : Domain n) 1) hp.2.2 (C*K) (fun a ha r hr=>(hJoint a ha r hr).1)
  have hZBound := criticalGradientMorreySquare_le_of_truncated_power_growth (fun x i=>E (Z x i))
    (ball (0 : Domain n) 1) hEZ (C*K) (fun a ha r hr=>(hJoint a ha r hr).2)
  exact (add_le_add hDpBound hZBound).trans_eq (by
    rw [←ENNReal.ofReal_add (by positivity : 0≤C*K) (by positivity : 0≤C*K)]
    congr 1
    ring)

end StationaryHarmonicMaps.Analysis

end
