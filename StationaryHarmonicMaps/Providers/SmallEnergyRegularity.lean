module

public import StationaryHarmonicMaps.Frozen.VariationalWeakPoissonEquivalence
public import StationaryHarmonicMaps.Analysis.EncodedPotentialMorrey
public import HolderToCK.Analysis.WeakPoissonLocality
public import StationaryHarmonicMaps.Analysis.CompensatedSystemRepresentative
public import StationaryHarmonicMaps.Analysis.OperatorCoefficientCoordinates
public import StationaryHarmonicMaps.Analysis.CriticalNativeCoulombBallExistence
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Stationary small-energy regularity for compact C² targets

The actual normal-projection system has a quantitative critical bound from
stationarity. Native Coulomb frames are constructed for its original
connection on the same three-quarter ball. The compensated representative
estimate gives the half-ball representative, its original energy square-root
factor, pointwise target membership and full continuous uniqueness.
-/

public section
open HarmonicMaps MeasureTheory Set Filter Metric
open scoped ContDiff ENNReal Topology
noncomputable section
namespace StationaryHarmonicMaps.Analysis

private theorem exists_uniform_energy_amplitudes (M C κ θ : ℝ)
    (hM : 0<M) (hC : 0<C) (hκ : 0<κ) (hθ : 0<θ) :
    ∃ε K : ℝ,0<ε ∧ 0<K ∧ ∀E : ℝ≥0∞,E≤ENNReal.ofReal ε →
      let η := Real.sqrt M*Real.sqrt E.toReal
      let β := (1+C)*η
      0≤η ∧ η≤κ ∧ 0≤β ∧ β≤θ ∧
      ENNReal.ofReal M*E=ENNReal.ofReal (η^2) ∧
      C*η^2≤β^2 ∧ η^2≤β^2 ∧ β=K*Real.sqrt E.toReal := by
  let K := (1+C)*Real.sqrt M
  have hK : 0<K := mul_pos (by linarith only [hC]) (Real.sqrt_pos.mpr hM)
  let τ := min κ θ
  have hτ : 0<τ := lt_min hκ hθ
  let ε := (τ/K)^2
  refine ⟨ε,K,pow_pos (div_pos hτ hK) 2,hK,?_⟩
  intro E hE η β
  have hFin : E≠⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hE
  have hReal : E.toReal≤ε := (ENNReal.toReal_le_toReal hFin ENNReal.ofReal_ne_top).mpr hE |>.trans_eq
    (ENNReal.toReal_ofReal (sq_nonneg (τ/K)))
  have hEta : 0≤η := mul_nonneg (Real.sqrt_nonneg M) (Real.sqrt_nonneg E.toReal)
  have hBeta : 0≤β := mul_nonneg (by linarith only [hC]) hEta
  have hBetaK : β=K*Real.sqrt E.toReal := by dsimp only [β,η,K];ring
  have hBetaSquare : β^2≤τ^2 := by
    rw [hBetaK,mul_pow,Real.sq_sqrt ENNReal.toReal_nonneg]
    calc
      _≤K^2*ε := mul_le_mul_of_nonneg_left hReal (sq_nonneg K)
      _=τ^2 := by dsimp only [ε];field_simp
  have hBetaτ : β≤τ := by nlinarith only [hBetaSquare,hBeta,hτ]
  have hEtaBeta : η≤β := by dsimp only [β];nlinarith only [hC,hEta]
  have hSquare : η^2=M*E.toReal := by
    dsimp only [η]
    rw [mul_pow,Real.sq_sqrt hM.le,Real.sq_sqrt ENNReal.toReal_nonneg]
  refine ⟨hEta,hEtaBeta.trans (hBetaτ.trans (min_le_left _ _)),hBeta,
    hBetaτ.trans (min_le_right _ _),?_,?_,?_,hBetaK⟩
  · rw [hSquare,ENNReal.ofReal_mul hM.le,ENNReal.ofReal_toReal hFin]
  · have hCoeff : C≤(1+C)^2 := by nlinarith only [hC,sq_nonneg C]
    calc
      C*η^2≤(1+C)^2*η^2 := mul_le_mul_of_nonneg_right hCoeff (sq_nonneg η)
      _=β^2 := by change (1+C)^2*η^2=((1+C)*η)^2;ring
  · exact pow_le_pow_left₀ hEta hEtaBeta 2

private theorem stationary_original_system_on_threeQuarterBall {n q : ℕ}
    (hn : 2≤n) (N : CompactC2EmbeddedTarget q)
    (G : Ambient q→Ambient q→L[ℝ]Ambient q) (L : ℝ)
    (hG : ContDiff ℝ 1 G) (hcG : HasCompactSupport G)
    (hGN : ∀p : N.Carrier,G p.val=N.normalProjection p)
    (hL : 0≤L) (hDG : ∀y,‖fderiv ℝ G y‖≤L)
    (E : (Ambient q→L[ℝ]Ambient q)→L[ℝ]Ambient (q*q))
    (hE : ∀T : Ambient q→L[ℝ]Ambient q,‖E T‖^2=∑j : Fin q,‖T (EuclideanSpace.single j 1)‖^2)
    (Ω : OpenDomain n) (u : Domain n→Ambient q) (Du : Domain n→Gradient n q)
    (hu : MemW12Loc Ω u Du) (hN : ∀ᵐx∂volume.restrict Ω.val,u x∈N.carrierSet)
    (hweak : IsWeaklyHarmonicByTangentVariations N Ω u Du)
    (hstationary : IsDomainStationary Ω Du)
    (a : Domain n) (R : PositiveRadius) (hball : closedBall a R.val⊆Ω.val) :
    let ρ := 3*R.val/4
    let A := fun x i=>projectionCommutator (G (u x)) (fderiv ℝ G (u x) (Du x i))
    let M := (1+(q:ℝ)*(2*L)^2)*(4:ℝ)^(n-2)
    MemW12 (ballDomain a ρ) u Du ∧
    (∀ᵐx∂volume.restrict (ball a ρ),u x∈N.carrierSet) ∧
    (∀i,MemLp (fun x=>A x i) 2 (volume.restrict (ball a ρ))) ∧
    (∀i,∀ᵐx∂volume.restrict (ball a ρ),star (A x i)= -(A x i)) ∧
    HolderToCK.WeakPoissonOn (ballDomain a ρ) Du (fun x=>-(∑i : Fin n,A x i (Du x i))) ∧
    criticalGradientMorreySquare Du (ball a ρ)+
      criticalGradientMorreySquare (fun x i=>E (A x i)) (ball a ρ)≤
        ENNReal.ofReal M*normalizedEnergy Du a R := by
  intro ρ A M
  have hρR : ρ≤R.val := by dsimp only [ρ];linarith only [R.property]
  have hClosed : closedBall a ρ⊆Ω.val := (closedBall_subset_closedBall hρR).trans hball
  have hSub : ball a ρ⊆Ω.val := ball_subset_closedBall.trans hClosed
  have hProperties := normal_projection_commutator_properties N hu hN hG hcG hGN hL hDG
  have hSkew : ∀i,∀ᵐx∂volume.restrict (ball a ρ),star (A x i)= -(A x i) := by
    intro i
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hSub hProperties] with x hx
    exact skewAdjoint.mem_iff.mp (hx i).1
  have hAL2 (i : Fin n) : MemLp (fun x=>A x i) 2 (volume.restrict (ball a ρ)) :=
    (locallyMemL2_projectionCommutator N hu hN hG hcG hGN hL hDG i
      (closedBall a ρ) (isCompact_closedBall a ρ) hClosed).mono_measure
        (Measure.restrict_mono_set volume ball_subset_closedBall)
  have hEq := variational_weakPoissonOn N hu hN hweak G hG hcG hGN hDG
  have hForcing : (fun x=>-(∑i : Fin n,fderiv ℝ G (u x) (Du x i) (Du x i)))=ᵐ[
      volume.restrict Ω.val](fun x=>-(∑i : Fin n,A x i (Du x i))) := by
    filter_upwards [hProperties] with x hx
    exact congrArg Neg.neg (Finset.sum_congr rfl (fun i _=>(hx i).2.1.symm))
  have hSystem : HolderToCK.WeakPoissonOn (ballDomain a ρ) Du
      (fun x=>-(∑i : Fin n,A x i (Du x i))) :=
    (hEq.congr (EventuallyEq.refl _ _) hForcing).mono hSub
  have hJoint := stationary_joint_morrey_square_bound hn N hu hstationary hN hG hGN hL hDG E hE R.property hball
  have hCoeff : (1+ENNReal.ofReal ((q:ℝ)*(2*L)^2))*ENNReal.ofReal ((4:ℝ)^(n-2))=ENNReal.ofReal M := by
    dsimp only [M]
    rw [ENNReal.ofReal_mul (by positivity : 0≤1+(q:ℝ)*(2*L)^2),
      ENNReal.ofReal_add (by norm_num : (0:ℝ)≤1) (by positivity : 0≤(q:ℝ)*(2*L)^2),ENNReal.ofReal_one]
  rw [hCoeff] at hJoint
  exact ⟨hu.memW12_ball hClosed,ae_restrict_of_ae_restrict_of_subset hSub hN,hAL2,hSkew,hSystem,hJoint⟩

private theorem exists_uniform_given_frame_ball_representative
    (n : ℕ) (hn : 2≤n) (q : ℕ)
    (E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient (q*q))
    (R : Ambient (q*q) →L[ℝ] (Ambient q →L[ℝ] Ambient q))
    (hRE : ∀T,R (E T)=T) (hER : ∀z,E (R z)=z)
    (hE : ∀T : Ambient q →L[ℝ] Ambient q,‖E T‖^2=∑j : Fin q,‖T (EuclideanSpace.single j 1)‖^2)
    (δ : ℝ) (hδ : 0<δ) (hδOne : δ<1) :
    ∃ε C : ℝ,0<ε ∧ ε≤1 ∧ 0<C ∧ ∀(N : CompactC2EmbeddedTarget q)
      (u : Domain n → Ambient q) (Du : Domain n → Gradient n q) (η : ℝ)
      (a : Domain n) (ρ : ℝ),0<ρ →
      MemW12 (ballDomain a ρ) u Du →
      (∀ᵐx∂volume.restrict (ball a ρ),u x∈N.carrierSet) → 0≤η → η≤ε →
      criticalGradientMorreySquare Du (ball a ρ)≤ENNReal.ofReal (η^2) →
      ∀(P : Domain n → Ambient (q*q)) (DP : Domain n → Gradient n (q*q)),
        MemW12 (ballDomain a ρ) P DP →
        (∀ᵐx∂volume.restrict (ball a ρ),star (R (P x))*R (P x)=1) →
        criticalGradientMorreySquare DP (ball a ρ)≤ENNReal.ofReal (η^2) →
        ∀Ω : Domain n → Fin n → (Ambient q →L[ℝ] Ambient q),
          (∀i,MemLp (fun x=>Ω x i) 2 (volume.restrict (ball a ρ))) →
          HolderToCK.WeakPoissonOn (ballDomain a ρ) Du (fun x=>-(∑i : Fin n,Ω x i (Du x i))) →
          let Z := fun x i=>star (R (P x))*R (DP x i)+star (R (P x))*Ω x i*R (P x)
          HolderToCK.WeakPoissonOn (ballDomain a ρ) (fun x i=>E (Z x i)) (fun _=>0) →
          criticalGradientMorreySquare (fun x i=>E (Z x i)) (ball a ρ)≤ENNReal.ofReal (η^2) →
            ∃w : ball a ((2/3:ℝ)*ρ) → Ambient q,
              IsContinuousRepresentative (ballDomain a ((2/3:ℝ)*ρ)) u w ∧
              (∀x,w x∈N.carrierSet) ∧
              (∀x y,‖w x-w y‖≤C*η*ρ^(-(1-δ))*(dist (x:Domain n) (y:Domain n))^(1-δ)) ∧
              ∀W : ball a ((2/3:ℝ)*ρ) → Ambient q,
                IsContinuousRepresentative (ballDomain a ((2/3:ℝ)*ρ)) u W → W=w := by
  have hnReal : (2:ℝ)≤(n:ℝ) := by exact_mod_cast hn
  have hnPos : (0:ℝ)<(n:ℝ) := lt_of_lt_of_le (by norm_num) hnReal
  let p : ℝ := 1+1/(2*(n:ℝ))
  have hDen : 0<2*(n:ℝ) := mul_pos (by norm_num) hnPos
  have hpOne : 1<p := by dsimp only [p];linarith only [div_pos zero_lt_one hDen]
  have hpTwo : p<2 := by
    have hInv : 1/(2*(n:ℝ))<1 := (div_lt_iff₀ hDen).mpr (by linarith only [hnReal])
    dsimp only [p]
    linarith only [hInv]
  have hpConj : (n:ℝ)<p/(p-1) := by
    have hValue : p/(p-1)=2*(n:ℝ)+1 := by
      dsimp only [p]
      field_simp
      ring
    rw [hValue]
    linarith only [hnReal]
  exact exists_compact_target_compensated_ball_representative
    n hn p hpOne hpTwo hpConj q E R hRE hER hE δ hδ hδOne


end StationaryHarmonicMaps.Analysis
namespace StationaryHarmonicMaps.Providers

theorem smallEnergyRegularity {n q : ℕ} (hn : 2 ≤ n)
    (N : CompactC2EmbeddedTarget q) :
    ∃ ε α C : ℝ, 0 < ε ∧ 0 < α ∧ α < 1 ∧ 0 ≤ C ∧
      ∀ (Ω : OpenDomain n) (u : Domain n → Ambient q)
        (Du : Domain n → Gradient n q),
        MemW12Loc Ω u Du →
        (∀ᵐ x ∂volume.restrict Ω.val, u x ∈ N.carrierSet) →
        IsWeaklyHarmonicByTangentVariations N Ω u Du →
        IsDomainStationary Ω Du →
        ∀ (a : Domain n) (R : PositiveRadius),
          Metric.closedBall a R.val ⊆ Ω.val →
          normalizedEnergy Du a R ≤ ENNReal.ofReal ε →
          ∃ w : Metric.ball a (R.val / 2) → Ambient q,
            IsContinuousRepresentative (ballDomain a (R.val / 2)) u w ∧
            (∀ x, w x ∈ N.carrierSet) ∧
            (∀ x y,
              ‖w x - w y‖ ≤ C * Real.rpow R.val (-α) *
                Real.sqrt (normalizedEnergy Du a R).toReal *
                Real.rpow (dist (x : Domain n) (y : Domain n)) α) ∧
            ∀ v : Metric.ball a (R.val / 2) → Ambient q,
              IsContinuousRepresentative (ballDomain a (R.val / 2)) u v → v = w := by
  obtain ⟨G,L,hG,hcG,hGN,hL,hDG,_hIff⟩ := N.variational_weakPoisson_equivalence
  obtain ⟨E,Rmap,_hEntries,_hREntries,hRE,hER,hEnorm⟩ :=
    Analysis.exists_operator_coefficient_coordinates q
  let e : Ambient (q*q)≃L[ℝ](Ambient q→L[ℝ]Ambient q) :=
    { toLinearEquiv :=
        { Rmap.toLinearMap with
          invFun := E
          left_inv := hER
          right_inv := hRE }
      continuous_toFun := Rmap.continuous
      continuous_invFun := E.continuous }
  have hE : ∀T : Ambient q→L[ℝ]Ambient q,
      ‖e.symm T‖^2=∑j : Fin q,‖T (EuclideanSpace.single j 1)‖^2 := hEnorm
  obtain ⟨κ,Cg,hκ,hCg,HGauge⟩ :=
    Analysis.exists_small_critical_native_coulomb_frame_ball n hn q e hE
  obtain ⟨θ,Cr,hθ,_hθOne,hCr,HRep⟩ :=
    Analysis.exists_uniform_given_frame_ball_representative n hn q E Rmap hRE hER hEnorm
      (1/2:ℝ) (by norm_num) (by norm_num)
  let M : ℝ := (1+(q:ℝ)*(2*L)^2)*(4:ℝ)^(n-2)
  have hM : 0<M := by dsimp only [M];positivity
  obtain ⟨ε,K,hε,hK,HAmplitude⟩ :=
    Analysis.exists_uniform_energy_amplitudes M Cg κ θ hM hCg hκ hθ
  let C : ℝ := Cr*K*(3/4:ℝ)^(-(1/2:ℝ))
  have hC : 0<C := mul_pos (mul_pos hCr hK) (Real.rpow_pos_of_pos (by norm_num) _)
  refine ⟨ε,1/2,C,hε,by norm_num,by norm_num,hC.le,?_⟩
  intro Ω u Du hu hN hweak hstationary a R hball hSmall
  let energy := normalizedEnergy Du a R
  let η := Real.sqrt M*Real.sqrt energy.toReal
  let β := (1+Cg)*η
  have hAmp := HAmplitude energy hSmall
  obtain ⟨hη,hηSmall,hβ,hβSmall,hEnergy,hCgBound,hηBound,hβK⟩ := hAmp
  let ρ : ℝ := 3*R.val/4
  have hρ : 0<ρ := by dsimp only [ρ];linarith only [R.property]
  let A := fun x i=>projectionCommutator (G (u x)) (fderiv ℝ G (u x) (Du x i))
  obtain ⟨huBall,hTarget,hAL2,hAskew,hSystem,hJoint⟩ :=
    Analysis.stationary_original_system_on_threeQuarterBall hn N G L hG hcG hGN hL hDG
      E hEnorm Ω u Du hu hN hweak hstationary a R hball
  have hJointEta : criticalGradientMorreySquare Du (ball a ρ)+
      criticalGradientMorreySquare (fun x i=>E (A x i)) (ball a ρ)≤ENNReal.ofReal (η^2) :=
    hJoint.trans_eq hEnergy
  have hACritical : criticalGradientMorreySquare (fun x i=>e.symm (A x i)) (ball a ρ)≤ENNReal.ofReal (η^2) :=
    (le_add_of_nonneg_left zero_le).trans hJointEta
  obtain ⟨P,DP,hP,hOrth,_hDet,hZLp,_hZSkew,hGaugeCritical,hNatural,hDiv⟩ :=
    HGauge a ρ hρ A η hAL2 hAskew hη hηSmall hACritical
  let Z := fun x i=>star (Rmap (P x))*Rmap (DP x i)+star (Rmap (P x))*A x i*Rmap (P x)
  have hDuCritical : criticalGradientMorreySquare Du (ball a ρ)≤ENNReal.ofReal (β^2) :=
    ((le_add_of_nonneg_right zero_le).trans hJointEta).trans (ENNReal.ofReal_le_ofReal hηBound)
  have hFrameCritical : criticalGradientMorreySquare DP (ball a ρ)+
      criticalGradientMorreySquare (fun x i=>E (Z x i)) (ball a ρ)≤ENNReal.ofReal (β^2) :=
    hGaugeCritical.trans (ENNReal.ofReal_le_ofReal hCgBound)
  have hDPCritical : criticalGradientMorreySquare DP (ball a ρ)≤ENNReal.ofReal (β^2) :=
    (le_add_of_nonneg_right zero_le).trans hFrameCritical
  have hZCritical : criticalGradientMorreySquare (fun x i=>E (Z x i)) (ball a ρ)≤ENNReal.ofReal (β^2) :=
    (le_add_of_nonneg_left zero_le).trans hFrameCritical
  have hResult := HRep N u Du β a ρ hρ huBall hTarget hβ hβSmall hDuCritical
    P DP hP hOrth hDPCritical A hAL2 hSystem hDiv hZCritical
  have hRadius : (2/3:ℝ)*ρ=R.val/2 := by dsimp only [ρ];ring
  rw [hRadius] at hResult
  obtain ⟨w,hw,hwN,hwHolder,hwUnique⟩ := hResult
  refine ⟨w,hw,hwN,?_,hwUnique⟩
  intro x y
  have hScale : ρ^(-(1/2:ℝ))=(3/4:ℝ)^(-(1/2:ℝ))*R.val^(-(1/2:ℝ)) := by
    have hρEq : ρ=(3/4:ℝ)*R.val := by dsimp only [ρ];ring
    rw [hρEq,Real.mul_rpow (by norm_num : (0:ℝ)≤3/4) R.property.le]
  have hAlpha : 1-(1/2:ℝ)=1/2 := by norm_num
  have H := hwHolder x y
  have hβK' : β=K*Real.sqrt energy.toReal := hβK
  rw [hAlpha,hScale,hβK'] at H
  exact H.trans_eq (by simp only [Real.rpow_eq_pow];dsimp only [C,energy];ring)

end StationaryHarmonicMaps.Providers
end
