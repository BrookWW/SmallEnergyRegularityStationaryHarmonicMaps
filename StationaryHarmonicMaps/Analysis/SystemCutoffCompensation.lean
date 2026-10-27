/- Copyright (c) 2026. All rights reserved. -/
module

public import StationaryHarmonicMaps.Analysis.SystemNativeMatrixPairing
public import StationaryHarmonicMaps.Analysis.CompactTargetNativeDivCurl

/-!
# Finite-index compensation for the actual matrix cutoff forcing

The actual compact-target cutoff supplies the original scalar component
observables. Each genuine rank-one matrix W0 test is paired with the
same encoded matrix divergence-free field. Summation controls the literal
ordered forcing without replacing it by a scalar-weighted vector flux.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology ENNReal ContDiff

namespace StationaryHarmonicMaps.Analysis

/-- The original compact-target cutoff and original matrix system give
the ordinary compensated forcing pairing with the true finite family
of native matrix tests. Their actual derivative energies remain explicit. -/
theorem exists_system_cutoff_compensated_pairing_bound_explicit (n : ℕ) (hn : 2≤n)
    (p : ℝ) (hpOne : 1≤p) (hpTwo : p≤2)
    (A B : ℝ) (hA : 0≤A) (hB : 0≤B) :
    ∃C : ℝ,0<C ∧ C=(effectiveCompactTargetEnvelopePairingConstant n:ℝ) ∧ ∀(q : ℕ) (N : CompactC2EmbeddedTarget q)
      (u : Domain n → Ambient q) (Du : Domain n → Gradient n q) (η : ℝ),
      MemW12 (ballDomain (0:Domain n) 1) u Du →
      (∀ᵐx∂volume.restrict (ball (0:Domain n) 1),u x∈N.carrierSet) → 0≤η →
      criticalGradientMorreySquare Du (ball (0:Domain n) 1)≤ENNReal.ofReal (η^2) →
      ∀χ : Domain n → ℝ,ContDiff ℝ ∞ χ → HasCompactSupport χ →
        tsupport χ⊆closedBall (0:Domain n) (3/4:ℝ) →
        (∀x,|χ x|≤A) → (∀(x : Domain n) (i : Fin n),|fderiv ℝ χ x (EuclideanSpace.single i 1)|≤B) →
        let c := ⨍y in ball (0:Domain n) 1,u y
        let v := fun x=>χ x • (u x-c)
        let Dv := fun x i=>χ x • Du x i+fderiv ℝ χ x (EuclideanSpace.single i 1) • (u x-c)
        let Φ := fun (x : Domain n) (r : ℝ)=>r^(p-(n:ℝ))*∫y in ball x r,(Real.sqrt (hsNormSq (Dv y)))^p
        let Ψ := fun t : ℝ=>sSup {z : ℝ | ∃x r,0<r ∧ r≤t ∧ z=Φ x r}
        ∀(a : Domain n) (t : ℝ),0<t → t≤1/128 → ∀m : ℕ,
        ∀(E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient (q*q))
          (R : Ambient m →L[ℝ] (Ambient q →L[ℝ] Ambient q)),
          (∀T : Ambient q →L[ℝ] Ambient q,‖E T‖^2=∑j : Fin q,‖T (EuclideanSpace.single j 1)‖^2) →
          ∀(P : Domain n → Ambient m) (DP : Domain n → Gradient n m),
          MemW12 (ballDomain a (t/2)) P DP → ∀M : ℝ,
          (∀ᵐx∂volume.restrict (ball a (t/2)),‖P x‖≤M) →
          ∀Z : Domain n → Fin n → (Ambient q →L[ℝ] Ambient q),
            (∀i,MemLp (fun x=>E (Z x i)) 2 (volume.restrict (ball a (t/2)))) →
            HolderToCK.WeakPoissonOn (ballDomain a (t/2)) (fun x i=>E (Z x i)) (fun _=>0) →
            ∀(φ : Domain n → Ambient q) (Dφ : Domain n → Gradient n q),
              HasZeroBoundaryValues (ballDomain a (t/2)) φ Dφ → ∀H : ℝ,
              (∀ᵐx∂volume.restrict (ball a (t/2)),‖φ x‖≤H) →
              let T := fun (j : Fin q) x=>systemMatrixTestCoefficient E R j (P x) (φ x)
              let DT := fun (j : Fin q) x i=>systemMatrixTestCoefficient E R j (DP x i) (φ x)+
                systemMatrixTestCoefficient E R j (P x) (Dφ x i)
              let W := fun x=>∑i : Fin n,Z x i (star (R (P x)) (Dv x i))
              MemW12 (ballDomain a (t/2)) v Dv ∧
              (∀j,HasZeroBoundaryValues (ballDomain a (t/2)) (T j) (DT j)) ∧
              IntegrableOn (fun x=>inner ℝ (W x) (φ x)) (ball a (t/2)) volume ∧
              |∫x in ball a (t/2),inner ℝ (W x) (φ x)|≤
                C*(Ψ (8*t))^(1/p)*Real.sqrt (∫x in ball a (t/2),hsNormSq (fun i=>E (Z x i)))*
                  (∑j : Fin q,‖PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin q=>ℝ) j‖*
                    Real.sqrt (∫x in ball a (t/2),hsNormSq (DT j x))) := by
  obtain ⟨C,hC,hCEq,Hpair⟩ := exists_compact_target_capped_envelope_native_divcurl_bound_explicit n hn p hpOne hpTwo A B hA hB
  refine ⟨C,hC,hCEq,?_⟩
  intro q N u Du η hu hTarget hη hCritical χ hχ hcχ hsχ hχA hDχ c v Dv Φ Ψ
    a t ht htCap m E R hE P DP hP M hPBound Z hZ hDiv φ Dφ hφ H hφBound T DT W
  obtain ⟨hV,_hPsi,_hGrowth⟩ := cutoff_capped_envelope_lp_growth n hn p hpOne hpTwo A B hA hB
    q u Du η hu hη hCritical χ hχ hcχ hsχ hχA hDχ t ht htCap
  have hVBall : MemW12 (ballDomain a (t/2)) v Dv := memW12_of_openDomain_subset hV (subset_univ _)
  have hsInside : tsupport χ⊆ball (0:Domain n) 1 := hsχ.trans (closedBall_subset_ball (by norm_num))
  obtain ⟨Nv,_hNv,hBoundV⟩ := exists_ae_bound_cutoff_of_compact_target N u hTarget c χ hsInside A hA hχA
  obtain ⟨hT,_hK,hWI,_hCI,hEq⟩ := native_system_matrix_compensated_pairing_ball a (t/2) (half_pos ht)
    E R hE P DP hP M hPBound v Dv hVBall Nv (ae_restrict_of_ae hBoundV) φ Dφ hφ H hφBound
    Z hZ hDiv 0
  have hEach (j : Fin q) : |∫x in ball a (t/2),(v x) j*(∑i : Fin n,inner ℝ (E (Z x i)) (DT j x i))|≤
      C*(Ψ (8*t))^(1/p)*Real.sqrt (∫x in ball a (t/2),hsNormSq (fun i=>E (Z x i)))*
        (‖PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin q=>ℝ) j‖*
          Real.sqrt (∫x in ball a (t/2),hsNormSq (DT j x))) := by
    obtain ⟨_hI,Hj⟩ := Hpair q N u Du η hu hTarget hη hCritical χ hχ hcχ hsχ hχA hDχ
      a t ht htCap (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin q=>ℝ) j) (q*q)
      (fun x i=>E (Z x i)) hZ hDiv (T j) (DT j) (hT j)
    have hOriginal : |∫x in ball a (t/2),(v x) j*(∑i : Fin n,inner ℝ (E (Z x i)) (DT j x i))|=
        |∫x in ball a (t/2),(∑i : Fin n,inner ℝ (E (Z x i)) (DT j x i))*(v x) j| := by
      congr 1
      apply integral_congr_ae
      exact Eventually.of_forall fun x=>mul_comm _ _
    rw [hOriginal]
    exact Hj.trans_eq (by ring)
  refine ⟨hVBall,hT,hWI,?_⟩
  rw [hEq,abs_neg]
  simp only [sub_zero] at *
  calc
    _≤∑j : Fin q,|∫x in ball a (t/2),(v x) j*(∑i : Fin n,inner ℝ (E (Z x i)) (DT j x i))| :=
      Finset.abs_sum_le_sum_abs _ _
    _≤∑j : Fin q,C*(Ψ (8*t))^(1/p)*Real.sqrt (∫x in ball a (t/2),hsNormSq (fun i=>E (Z x i)))*
        (‖PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin q=>ℝ) j‖*
          Real.sqrt (∫x in ball a (t/2),hsNormSq (DT j x))) := Finset.sum_le_sum fun j _=>hEach j
    _=_ := (Finset.mul_sum _ _ _).symm

theorem exists_system_cutoff_compensated_pairing_bound (n : ℕ) (hn : 2≤n)
    (p : ℝ) (hpOne : 1≤p) (hpTwo : p≤2)
    (A B : ℝ) (hA : 0≤A) (hB : 0≤B) :
    ∃C : ℝ,0<C ∧ ∀(q : ℕ) (N : CompactC2EmbeddedTarget q)
      (u : Domain n → Ambient q) (Du : Domain n → Gradient n q) (η : ℝ),
      MemW12 (ballDomain (0:Domain n) 1) u Du →
      (∀ᵐx∂volume.restrict (ball (0:Domain n) 1),u x∈N.carrierSet) → 0≤η →
      criticalGradientMorreySquare Du (ball (0:Domain n) 1)≤ENNReal.ofReal (η^2) →
      ∀χ : Domain n → ℝ,ContDiff ℝ ∞ χ → HasCompactSupport χ →
        tsupport χ⊆closedBall (0:Domain n) (3/4:ℝ) →
        (∀x,|χ x|≤A) → (∀(x : Domain n) (i : Fin n),|fderiv ℝ χ x (EuclideanSpace.single i 1)|≤B) →
        let c := ⨍y in ball (0:Domain n) 1,u y
        let v := fun x=>χ x • (u x-c)
        let Dv := fun x i=>χ x • Du x i+fderiv ℝ χ x (EuclideanSpace.single i 1) • (u x-c)
        let Φ := fun (x : Domain n) (r : ℝ)=>r^(p-(n:ℝ))*∫y in ball x r,(Real.sqrt (hsNormSq (Dv y)))^p
        let Ψ := fun t : ℝ=>sSup {z : ℝ | ∃x r,0<r ∧ r≤t ∧ z=Φ x r}
        ∀(a : Domain n) (t : ℝ),0<t → t≤1/128 → ∀m : ℕ,
        ∀(E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient (q*q))
          (R : Ambient m →L[ℝ] (Ambient q →L[ℝ] Ambient q)),
          (∀T : Ambient q →L[ℝ] Ambient q,‖E T‖^2=∑j : Fin q,‖T (EuclideanSpace.single j 1)‖^2) →
          ∀(P : Domain n → Ambient m) (DP : Domain n → Gradient n m),
          MemW12 (ballDomain a (t/2)) P DP → ∀M : ℝ,
          (∀ᵐx∂volume.restrict (ball a (t/2)),‖P x‖≤M) →
          ∀Z : Domain n → Fin n → (Ambient q →L[ℝ] Ambient q),
            (∀i,MemLp (fun x=>E (Z x i)) 2 (volume.restrict (ball a (t/2)))) →
            HolderToCK.WeakPoissonOn (ballDomain a (t/2)) (fun x i=>E (Z x i)) (fun _=>0) →
            ∀(φ : Domain n → Ambient q) (Dφ : Domain n → Gradient n q),
              HasZeroBoundaryValues (ballDomain a (t/2)) φ Dφ → ∀H : ℝ,
              (∀ᵐx∂volume.restrict (ball a (t/2)),‖φ x‖≤H) →
              let T := fun (j : Fin q) x=>systemMatrixTestCoefficient E R j (P x) (φ x)
              let DT := fun (j : Fin q) x i=>systemMatrixTestCoefficient E R j (DP x i) (φ x)+
                systemMatrixTestCoefficient E R j (P x) (Dφ x i)
              let W := fun x=>∑i : Fin n,Z x i (star (R (P x)) (Dv x i))
              MemW12 (ballDomain a (t/2)) v Dv ∧
              (∀j,HasZeroBoundaryValues (ballDomain a (t/2)) (T j) (DT j)) ∧
              IntegrableOn (fun x=>inner ℝ (W x) (φ x)) (ball a (t/2)) volume ∧
              |∫x in ball a (t/2),inner ℝ (W x) (φ x)|≤
                C*(Ψ (8*t))^(1/p)*Real.sqrt (∫x in ball a (t/2),hsNormSq (fun i=>E (Z x i)))*
                  (∑j : Fin q,‖PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin q=>ℝ) j‖*
                    Real.sqrt (∫x in ball a (t/2),hsNormSq (DT j x))) := by
  obtain ⟨C,hC,_hCEq,H⟩ := exists_system_cutoff_compensated_pairing_bound_explicit n hn p hpOne hpTwo A B hA hB
  exact ⟨C,hC,H⟩

end StationaryHarmonicMaps.Analysis

end
