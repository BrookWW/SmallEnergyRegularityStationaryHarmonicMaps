module

public import StationaryHarmonicMaps.Analysis.SkewStrongerMorreyApproximation
public import StationaryHarmonicMaps.Analysis.SpecialOrthogonalNaturalCompactness
public import StationaryHarmonicMaps.Analysis.SkewConnectionAndTests
public import StationaryHarmonicMaps.Analysis.StrongerNativeCoulombExistence

/-!
# Native Coulomb frames for original critical connections

The stronger Morrey existence theorem at exponent n-1 supplies actual frames
for the original skew mollifications. One joint compactness limit retains
the same native weak gradient, special orthogonality, the literal rough
connection, both complete critical bounds and every whole-ball native test.
The critical threshold and bound are uniform before the original connection.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology ENNReal ContDiff
noncomputable section
namespace StationaryHarmonicMaps.Analysis

private theorem critical_mono_domain {n k : ℕ} (F : Domain n→Gradient n k)
    {S T : Set (Domain n)} (hST : S⊆T) :
    criticalGradientMorreySquare F S≤criticalGradientMorreySquare F T := by
  unfold criticalGradientMorreySquare
  refine iSup_le fun a=>iSup_le fun r=>?_
  have hEnergy : dirichletEnergy F (ball a.val r.val∩S)≤
      dirichletEnergy F (ball a.val r.val∩T) :=
    lintegral_mono_set (inter_subset_inter_right _ hST)
  exact (mul_le_mul_right hEnergy _).trans
    (le_iSup_of_le (⟨a.val,hST a.property⟩ : T) (le_iSup_of_le r le_rfl))

private theorem mollifier_amplitude_square (n : ℕ) (η : ℝ) :
    (Real.sqrt ((2:ℝ)^(n-2))*η)^2=(2:ℝ)^(n-2)*η^2 := by
  rw [mul_pow,Real.sq_sqrt (pow_nonneg (by norm_num : (0:ℝ)≤2) _)]

private theorem mollifier_amplitude_threshold (n : ℕ) (κ : ℝ) (hκ : 0<κ) :
    0<κ/Real.sqrt ((2:ℝ)^(n-2)) ∧
    ∀η : ℝ,0≤η → η≤κ/Real.sqrt ((2:ℝ)^(n-2)) →
      0≤Real.sqrt ((2:ℝ)^(n-2))*η ∧ Real.sqrt ((2:ℝ)^(n-2))*η≤κ := by
  have hD : 0<(2:ℝ)^(n-2) := pow_pos (by norm_num) _
  have hρ : 0<Real.sqrt ((2:ℝ)^(n-2)) := Real.sqrt_pos.mpr hD
  refine ⟨div_pos hκ hρ,?_⟩
  intro η hη hηle
  exact ⟨mul_nonneg hρ.le hη,by simpa only [mul_comm] using (le_div_iff₀ hρ).mp hηle⟩

private theorem actual_critical_approximant_data {n q : ℕ} (hn : 2≤n)
    (E : (Ambient q→L[ℝ]Ambient q)→L[ℝ]Ambient (q*q))
    (R : Ambient (q*q)→L[ℝ](Ambient q→L[ℝ]Ambient q))
    (hRE : ∀T,R (E T)=T) (hER : ∀z,E (R z)=z)
    (A : Domain n→Fin n→(Ambient q→L[ℝ]Ambient q))
    (hA : ∀i,MemLp (fun x=>A x i) 2 (volume.restrict (ball (0:Domain n) 1)))
    (hSkew : ∀i,∀ᵐx∂volume.restrict (ball (0:Domain n) 1),star (A x i)= -(A x i))
    (η : ℝ)
    (hCritical : criticalGradientMorreySquare (fun x i=>E (A x i)) (ball (0:Domain n) 1)≤ENNReal.ofReal (η^2)) :
    ∃B : ℕ→Domain n→Fin n→(Ambient q→L[ℝ]Ambient q),
      (∀j i,MemLp (fun x=>B j x i) 2 (volume.restrict (ball (0:Domain n) 1))) ∧
      (∀j i,∀ᵐx∂volume.restrict (ball (0:Domain n) 1),star (B j x i)= -(B j x i)) ∧
      (∀j,criticalGradientMorreySquare (fun x i=>E (B j x i)) (ball (0:Domain n) 1)≤
        ENNReal.ofReal ((Real.sqrt ((2:ℝ)^(n-2))*η)^2)) ∧
      (∀j,∃KB : ℝ,0<KB ∧ ∀a∈ball (0:Domain n) 1,∀r : ℝ,0<r →
        (∫x in ball a r∩ball (0:Domain n) 1,hsNormSq (fun i=>E (B j x i)))≤KB*r^((n:ℝ)-1)) ∧
      (∀i,Tendsto (fun j=>eLpNorm (fun x=>E (B j x i)-E (A x i)) 2
        (volume.restrict (ball (0:Domain n) 1))) atTop (𝓝 0)) := by
  have hData := exists_stronger_class_skew_critical_approximation_unitBall hn E R hRE hER A hA hSkew
    (η^2) (sq_nonneg η) hCritical
  let B := hData.choose
  have hB := hData.choose_spec
  refine ⟨B,?_,?_,?_,?_,hB.2.2.2.2⟩
  · exact fun j i=>((hB.1 j i).2).restrict _
  · exact fun j i=>Eventually.of_forall fun x=>hB.2.1 j x i
  · intro j
    have H := (critical_mono_domain (fun x i=>E (B j x i)) (subset_univ (ball (0:Domain n) 1))).trans (hB.2.2.1 j)
    rw [mollifier_amplitude_square]
    exact H
  · intro j
    have hKData := hB.2.2.2.1 j
    refine ⟨hKData.choose,hKData.choose_spec.1,?_⟩
    exact fun a _ha r hr=>hKData.choose_spec.2 a r hr

private theorem critical_native_coulomb_passage_of_stronger
    (n : ℕ) (hn : 2≤n) (q : ℕ)
    (E : (Ambient q→L[ℝ]Ambient q)→L[ℝ]Ambient (q*q))
    (R : Ambient (q*q)→L[ℝ](Ambient q→L[ℝ]Ambient q))
    (hRE : ∀T,R (E T)=T) (hER : ∀z,E (R z)=z)
    (hE : ∀T : Ambient q→L[ℝ]Ambient q,‖E T‖^2=∑j : Fin q,‖T (EuclideanSpace.single j 1)‖^2)
    (κ C : ℝ) (hκ : 0<κ) (hC : 0<C)
    (hHigher : ∀(B : Domain n→Fin n→(Ambient q→L[ℝ]Ambient q)) (η KB : ℝ),
      (∀i,MemLp (fun x=>B x i) 2 (volume.restrict (ball (0:Domain n) 1))) →
      (∀i,∀ᵐx∂volume.restrict (ball (0:Domain n) 1),star (B x i)= -(B x i)) →
      0≤η → η≤κ →
      criticalGradientMorreySquare (fun x i=>E (B x i)) (ball (0:Domain n) 1)≤ENNReal.ofReal (η^2) →
      (∀a∈ball (0:Domain n) 1,∀r : ℝ,0<r →
        (∫x in ball a r∩ball (0:Domain n) 1,hsNormSq (fun i=>E (B x i)))≤KB*r^((n:ℝ)-1)) →
      ∃(p : Domain n→Ambient (q*q)) (Dp : Domain n→Gradient n (q*q)),
        MemW12 (ballDomain (0:Domain n) 1) p Dp ∧
        (∀ᵐx∂volume.restrict (ball (0:Domain n) 1),star (R (p x))*R (p x)=1) ∧
        (∀ᵐx∂volume.restrict (ball (0:Domain n) 1),(R (p x)).det=1) ∧
        let Z := fun x i=>E (star (R (p x))*R (Dp x i)+star (R (p x))*B x i*R (p x))
        (∀i,MemLp (fun x=>Z x i) 2 (volume.restrict (ball (0:Domain n) 1))) ∧
        (criticalGradientMorreySquare Dp (ball (0:Domain n) 1)+
          criticalGradientMorreySquare Z (ball (0:Domain n) 1)≤ENNReal.ofReal (C*η^2)) ∧
        (∀a∈ball (0:Domain n) 1,∀r : ℝ,0<r →
          (∫x in ball a r∩ball (0:Domain n) 1,hsNormSq (Dp x))≤C*KB*r^((n:ℝ)-1) ∧
          (∫x in ball a r∩ball (0:Domain n) 1,hsNormSq (Z x))≤C*KB*r^((n:ℝ)-1)) ∧
        (∀(ψ : Domain n→Ambient (q*q)) (Dψ : Domain n→Gradient n (q*q)),
          MemW12 (ballDomain (0:Domain n) 1) ψ Dψ →
          IntegrableOn (fun x=>∑i : Fin n,inner ℝ (Z x i) (Dψ x i)) (ball (0:Domain n) 1) volume ∧
          (∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (Z x i) (Dψ x i))=0)) :
    ∃κ₀ C₀ : ℝ,0<κ₀ ∧ 0<C₀ ∧
      ∀(A : Domain n→Fin n→(Ambient q→L[ℝ]Ambient q)) (η : ℝ),
        (∀i,MemLp (fun x=>A x i) 2 (volume.restrict (ball (0:Domain n) 1))) →
        (∀i,∀ᵐx∂volume.restrict (ball (0:Domain n) 1),star (A x i)= -(A x i)) →
        0≤η → η≤κ₀ →
        criticalGradientMorreySquare (fun x i=>E (A x i)) (ball (0:Domain n) 1)≤ENNReal.ofReal (η^2) →
        ∃(p : Domain n→Ambient (q*q)) (Dp : Domain n→Gradient n (q*q)),
          MemW12 (ballDomain (0:Domain n) 1) p Dp ∧
          (∀ᵐx∂volume.restrict (ball (0:Domain n) 1),star (R (p x))*R (p x)=1) ∧
          (∀ᵐx∂volume.restrict (ball (0:Domain n) 1),(R (p x)).det=1) ∧
          let Zop := fun x i=>star (R (p x))*R (Dp x i)+star (R (p x))*A x i*R (p x)
          let Z := fun x i=>E (Zop x i)
          (∀i,MemLp (fun x=>Z x i) 2 (volume.restrict (ball (0:Domain n) 1))) ∧
          (∀ᵐx∂volume.restrict (ball (0:Domain n) 1),∀i,star (Zop x i)= -(Zop x i)) ∧
          (criticalGradientMorreySquare Dp (ball (0:Domain n) 1)+
            criticalGradientMorreySquare Z (ball (0:Domain n) 1)≤ENNReal.ofReal (C₀*η^2)) ∧
          (∀(ψ : Domain n→Ambient (q*q)) (Dψ : Domain n→Gradient n (q*q)),
            MemW12 (ballDomain (0:Domain n) 1) ψ Dψ →
            IntegrableOn (fun x=>∑i : Fin n,inner ℝ (Z x i) (Dψ x i)) (ball (0:Domain n) 1) volume ∧
            (∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (Z x i) (Dψ x i))=0) := by
  let ρ := Real.sqrt ((2:ℝ)^(n-2))
  let κ₀ := κ/ρ
  let C₀ := 2*C*(2:ℝ)^(n-2)
  have hD : 0<(2:ℝ)^(n-2) := pow_pos (by norm_num) _
  have hκ₀ : 0<κ₀ := (mollifier_amplitude_threshold n κ hκ).1
  have hC₀ : 0<C₀ := mul_pos (mul_pos (by norm_num) hC) hD
  refine ⟨κ₀,C₀,hκ₀,hC₀,?_⟩
  intro A η hA hSkew hη hηle hCritical
  let ξ := ρ*η
  have hξData := (mollifier_amplitude_threshold n κ hκ).2 η hη hηle
  have hξ : 0≤ξ := hξData.1
  have hξκ : ξ≤κ := hξData.2
  have hApprox := actual_critical_approximant_data hn E R hRE hER A hA hSkew η hCritical
  let B := hApprox.choose
  have hB := hApprox.choose_spec
  let KB := fun j=>(hB.2.2.2.1 j).choose
  have hGrowth (j : ℕ) : ∀a∈ball (0:Domain n) 1,∀r : ℝ,0<r →
      (∫x in ball a r∩ball (0:Domain n) 1,hsNormSq (fun i=>E (B j x i)))≤KB j*r^((n:ℝ)-1) :=
    (hB.2.2.2.1 j).choose_spec.2
  have hFrame (j : ℕ) := hHigher (B j) ξ (KB j) (hB.1 j) (hB.2.1 j) hξ hξκ (hB.2.2.1 j) (hGrowth j)
  let ps := fun j=>(hFrame j).choose
  let Ds := fun j=>(hFrame j).choose_spec.choose
  have hFrames (j : ℕ) := (hFrame j).choose_spec.choose_spec
  have hDpCritical (j : ℕ) : criticalGradientMorreySquare (Ds j) (ball (0:Domain n) 1)≤ENNReal.ofReal (C*ξ^2) :=
    (le_add_of_nonneg_right zero_le).trans (hFrames j).2.2.2.2.1
  have hZCritical (j : ℕ) : criticalGradientMorreySquare
      (fun x i=>E (star (R (ps j x))*R (Ds j x i)+star (R (ps j x))*R (E (B j x i))*R (ps j x)))
        (ball (0:Domain n) 1)≤ENNReal.ofReal (C*ξ^2) := by
    have H := (le_add_of_nonneg_left zero_le).trans (hFrames j).2.2.2.2.1
    simpa only [hRE] using H
  have hNatural (j : ℕ) (ψ : Domain n→Ambient (q*q)) (Dψ : Domain n→Gradient n (q*q))
      (hψ : MemW12 (ballDomain (0:Domain n) 1) ψ Dψ) :
      (∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ
        (E (star (R (ps j x))*R (Ds j x i)+star (R (ps j x))*R (E (B j x i))*R (ps j x))) (Dψ x i))=0 := by
    simpa only [hRE] using ((hFrames j).2.2.2.2.2.2 ψ Dψ hψ).2
  have hL2 (j : ℕ) (i : Fin n) : MemLp (fun x=>E (B j x i)) 2 (volume.restrict (ball (0:Domain n) 1)) :=
    E.lipschitz.comp_memLp (map_zero E) (hB.1 j i)
  have hOriginalL2 (i : Fin n) : MemLp (fun x=>E (A x i)) 2 (volume.restrict (ball (0:Domain n) 1)) :=
    E.lipschitz.comp_memLp (map_zero E) (hA i)
  have hBound : 0≤C*ξ^2 := mul_nonneg hC.le (sq_nonneg ξ)
  have hLimit := exists_special_orthogonal_natural_critical_limit_unitBall E R hRE hER hE ps Ds
    (fun j=>(hFrames j).1) (fun j=>(hFrames j).2.1) (fun j=>(hFrames j).2.2.1)
    (fun j x i=>E (B j x i)) (fun x i=>E (A x i)) hL2 hOriginalL2 hB.2.2.2.2
    hBound (sq_nonneg ξ) hBound hDpCritical hB.2.2.1 hZCritical hNatural
  let p := hLimit.choose_spec.choose
  let Dp := hLimit.choose_spec.choose_spec.choose
  have hL := hLimit.choose_spec.choose_spec.choose_spec
  let Zop := fun x i=>star (R (p x))*R (Dp x i)+star (R (p x))*A x i*R (p x)
  let Z := fun x i=>E (Zop x i)
  let Zenc := fun x i=>E (star (R (p x))*R (Dp x i)+star (R (p x))*R (E (A x i))*R (p x))
  have hZE : Zenc=Z := by
    funext x i
    change E (star (R (p x))*R (Dp x i)+star (R (p x))*R (E (A x i))*R (p x))=Z x i
    rw [hRE]
  have hEncoded : (∀i,MemLp (fun x=>Zenc x i) 2 (volume.restrict (ball (0:Domain n) 1))) ∧
      criticalGradientMorreySquare Zenc (ball (0:Domain n) 1)≤ENNReal.ofReal (C*ξ^2) ∧
      (∀(ψ : Domain n→Ambient (q*q)) (Dψ : Domain n→Gradient n (q*q)),
        MemW12 (ballDomain (0:Domain n) 1) ψ Dψ →
        IntegrableOn (fun x=>∑i : Fin n,inner ℝ (Zenc x i) (Dψ x i)) (ball (0:Domain n) 1) volume ∧
        (∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (Zenc x i) (Dψ x i))=0) := hL.2.2.2.2.2.2.2
  have hRaw : (∀i,MemLp (fun x=>Z x i) 2 (volume.restrict (ball (0:Domain n) 1))) ∧
      criticalGradientMorreySquare Z (ball (0:Domain n) 1)≤ENNReal.ofReal (C*ξ^2) ∧
      (∀(ψ : Domain n→Ambient (q*q)) (Dψ : Domain n→Gradient n (q*q)),
        MemW12 (ballDomain (0:Domain n) 1) ψ Dψ →
        IntegrableOn (fun x=>∑i : Fin n,inner ℝ (Z x i) (Dψ x i)) (ball (0:Domain n) 1) volume ∧
        (∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (Z x i) (Dψ x i))=0) := hZE ▸ hEncoded
  have hSum := add_le_add hL.2.2.2.2.1 hRaw.2.1
  rw [←ENNReal.ofReal_add hBound hBound] at hSum
  have hCoeff : C*ξ^2+C*ξ^2=C₀*η^2 := by
    change C*(Real.sqrt ((2:ℝ)^(n-2))*η)^2+C*(Real.sqrt ((2:ℝ)^(n-2))*η)^2=2*C*(2:ℝ)^(n-2)*η^2
    rw [mollifier_amplitude_square]
    ring
  have hSumFinal : criticalGradientMorreySquare Dp (ball (0:Domain n) 1)+
      criticalGradientMorreySquare Z (ball (0:Domain n) 1)≤ENNReal.ofReal (C₀*η^2) :=
    hSum.trans_eq (congrArg ENNReal.ofReal hCoeff)
  have hZSkew := (frame_connection_memLp_and_skew E R hER hE p Dp hL.2.1 hL.2.2.1 A hA hSkew).2.2
  exact ⟨p,Dp,hL.2.1,hL.2.2.1,hL.2.2.2.1,hRaw.1,hZSkew,hSumFinal,hRaw.2.2⟩


/-- Every original sufficiently small critical skew connection has a native
special orthogonal natural Coulomb frame with a uniform critical bound. -/
theorem exists_small_critical_native_coulomb_frame
    (n : ℕ) (hn : 2≤n) (q : ℕ)
    (e : Ambient (q*q)≃L[ℝ](Ambient q→L[ℝ]Ambient q))
    (hE : ∀T : Ambient q→L[ℝ]Ambient q,
      ‖e.symm T‖^2=∑j : Fin q,‖T (EuclideanSpace.single j 1)‖^2) :
    ∃ε C : ℝ,0<ε ∧ 0<C ∧
      ∀(A : Domain n→Fin n→(Ambient q→L[ℝ]Ambient q)) (η : ℝ),
        (∀i,MemLp (fun x=>A x i) 2 (volume.restrict (ball (0:Domain n) 1))) →
        (∀i,∀ᵐx∂volume.restrict (ball (0:Domain n) 1),star (A x i)= -(A x i)) →
        0≤η → η≤ε →
        criticalGradientMorreySquare (fun x i=>e.symm (A x i)) (ball (0:Domain n) 1)≤ENNReal.ofReal (η^2) →
        ∃(p : Domain n→Ambient (q*q)) (Dp : Domain n→Gradient n (q*q)),
          MemW12 (ballDomain (0:Domain n) 1) p Dp ∧
          (∀ᵐx∂volume.restrict (ball (0:Domain n) 1),star (e (p x))*e (p x)=1) ∧
          (∀ᵐx∂volume.restrict (ball (0:Domain n) 1),(e (p x)).det=1) ∧
          let Zop := fun x i=>star (e (p x))*e (Dp x i)+star (e (p x))*A x i*e (p x)
          let Z := fun x i=>e.symm (Zop x i)
          (∀i,MemLp (fun x=>Z x i) 2 (volume.restrict (ball (0:Domain n) 1))) ∧
          (∀ᵐx∂volume.restrict (ball (0:Domain n) 1),∀i,star (Zop x i)= -(Zop x i)) ∧
          (criticalGradientMorreySquare Dp (ball (0:Domain n) 1)+
            criticalGradientMorreySquare Z (ball (0:Domain n) 1)≤ENNReal.ofReal (C*η^2)) ∧
          (∀(ψ : Domain n→Ambient (q*q)) (Dψ : Domain n→Gradient n (q*q)),
            MemW12 (ballDomain (0:Domain n) 1) ψ Dψ →
            IntegrableOn (fun x=>∑i : Fin n,inner ℝ (Z x i) (Dψ x i)) (ball (0:Domain n) 1) volume ∧
            (∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (Z x i) (Dψ x i))=0) := by
  obtain ⟨κ,C,hκ,hC,H⟩ := exists_small_stronger_native_coulomb_frame
    n hn 1 (by norm_num) (by norm_num) q e hE
  refine critical_native_coulomb_passage_of_stronger n hn q
    e.symm.toContinuousLinearMap e.toContinuousLinearMap
    e.apply_symm_apply e.symm_apply_apply hE κ C hκ hC ?_
  intro B η KB hB hSkew hη hSmall hCritical hGrowth
  have hν : (n:ℝ)-2+(1:ℝ)=(n:ℝ)-1 := by ring
  have hGrowth' : ∀a∈ball (0:Domain n) 1,∀r : ℝ,0<r →
      (∫x in ball a r∩ball (0:Domain n) 1,hsNormSq (fun i=>e.symm (B x i)))≤KB*r^((n:ℝ)-2+(1:ℝ)) := by
    intro a ha r hr
    rw [hν]
    exact hGrowth a ha r hr
  obtain ⟨p,Dp,hp,hOrth,hDet,hZLp,_hZSkew,hSum,hGrow,hNatural⟩ :=
    H B η KB hB hSkew hη hSmall hCritical hGrowth'
  refine ⟨p,Dp,hp,hOrth,hDet,hZLp,hSum,?_,hNatural⟩
  intro a ha r hr
  rw [←hν]
  exact hGrow a ha r hr

end StationaryHarmonicMaps.Analysis
end
