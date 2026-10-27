module

public import StationaryHarmonicMaps.Analysis.EffectiveStationaryConstants
public import StationaryHarmonicMaps.Geometry.EffectiveNormalProjectionData
public import StationaryHarmonicMaps.Frozen.VariationalWeakPoissonEquivalence
public import StationaryHarmonicMaps.Analysis.EncodedPotentialMorrey
public import StationaryHarmonicMaps.Analysis.OperatorCoefficientCoordinates
public import StationaryHarmonicMaps.Analysis.SmoothHolderRepresentative

/-!
# Effective stationary small-energy regularity

The energy threshold and Hölder coefficient are rational functions of
source and ambient dimensions and a certified geometric derivative bound.
The original map, weak gradient, target and stationary variational data
produce the quantitative representative on the entire half ball.
-/

public section
open HarmonicMaps MeasureTheory Set Filter Metric
open scoped ContDiff ENNReal Topology
noncomputable section
namespace StationaryHarmonicMaps.Analysis

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

end StationaryHarmonicMaps.Analysis

namespace StationaryHarmonicMaps.Providers

theorem smallEnergyRegularity_effective {n q : ℕ} (hn : 2 ≤ n)
    (N : CompactC2EmbeddedTarget q)
    (G : Ambient q → (Ambient q →L[ℝ] Ambient q)) (L : ℚ)
    (hG : ContDiff ℝ 1 G) (hcG : HasCompactSupport G)
    (hGN : ∀ p : N.Carrier,G p.val=N.normalProjection p)
    (hL : 0≤L) (hDG : ∀ y,‖fderiv ℝ G y‖≤(L:ℝ)) :
      ∀ (Ω : OpenDomain n) (u : Domain n → Ambient q)
        (Du : Domain n → Gradient n q),
        MemW12Loc Ω u Du →
        (∀ᵐ x ∂volume.restrict Ω.val, u x ∈ N.carrierSet) →
        IsWeaklyHarmonicByTangentVariations N Ω u Du →
        IsDomainStationary Ω Du →
        ∀ (a : Domain n) (R : PositiveRadius),
          Metric.closedBall a R.val ⊆ Ω.val →
          normalizedEnergy Du a R ≤ ENNReal.ofReal (Analysis.effectiveStationaryEnergyThreshold n q L:ℝ) →
          ∃ w : Metric.ball a (R.val / 2) → Ambient q,
            IsContinuousRepresentative (ballDomain a (R.val / 2)) u w ∧
            (∀ x, w x ∈ N.carrierSet) ∧
            (∀ x y,
              ‖w x - w y‖ ≤ (Analysis.effectiveStationaryHolderConstant n q L:ℝ) * Real.rpow R.val (-(1/2:ℝ)) *
                Real.sqrt (normalizedEnergy Du a R).toReal *
                Real.rpow (dist (x : Domain n) (y : Domain n)) (1/2:ℝ)) ∧
            ∀ v : Metric.ball a (R.val / 2) → Ambient q,
              IsContinuousRepresentative (ballDomain a (R.val / 2)) u v → v = w := by
  have hLR : 0≤(L:ℝ) := by exact_mod_cast hL
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
  obtain ⟨κ,Cg,hκ,hCg,hκEq,hCgEq,HGauge⟩ :=
    Analysis.exists_small_critical_native_coulomb_frame_ball_effective n hn q e hE
  obtain ⟨θ,Cr,hθ,_hθOne,hCr,hθEq,hCrEq,HRep⟩ :=
    Analysis.exists_compact_target_compensated_ball_representative_effective
      n hn q E Rmap hRE hER hEnorm
  subst κ Cg θ Cr
  let M : ℝ := (Analysis.rationalMorreyFactor n q L:ℝ)
  have hM : 0<M := by dsimp only [M];exact_mod_cast Analysis.rationalMorreyFactor_pos n q L
  let K : ℝ := (Analysis.rationalAmplitudeMajorant n q L
    (Analysis.effectiveCoulombFrameGradientConstant n q):ℝ)
  have hCgNonneg : 0≤Analysis.effectiveCoulombFrameGradientConstant n q := by exact_mod_cast hCg.le
  have hK : 0≤K := by dsimp only [K];exact_mod_cast (Analysis.rationalAmplitudeMajorant_pos n q L hCgNonneg).le
  have hκRat : 0<Analysis.effectiveCoulombFrameSmallness n q := by exact_mod_cast hκ
  have hθRat : 0<Analysis.effectiveGivenFrameSmallness n q := by exact_mod_cast hθ
  intro Ω u Du hu hN hweak hstationary a R hball hSmall
  let energy := normalizedEnergy Du a R
  let η := Real.sqrt M*Real.sqrt energy.toReal
  let β := (1+(Analysis.effectiveCoulombFrameGradientConstant n q:ℝ))*η
  have hAmp := Analysis.rational_energy_amplitudes n q L
    (Analysis.effectiveCoulombFrameGradientConstant n q)
    (Analysis.effectiveCoulombFrameSmallness n q) (Analysis.effectiveGivenFrameSmallness n q)
    hCgNonneg hκRat hθRat energy hSmall
  obtain ⟨hη,hηSmall,hβ,hβSmall,hEnergy,hCgBound,hηBound,hβK⟩ := hAmp
  let ρ : ℝ := 3*R.val/4
  have hρ : 0<ρ := by dsimp only [ρ];linarith only [R.property]
  let A := fun x i=>projectionCommutator (G (u x)) (fderiv ℝ G (u x) (Du x i))
  obtain ⟨huBall,hTarget,hAL2,hAskew,hSystem,hJoint⟩ :=
    Analysis.stationary_original_system_on_threeQuarterBall hn N G (L:ℝ) hG hcG hGN hLR hDG
      E hEnorm Ω u Du hu hN hweak hstationary a R hball
  have hMCast : (1+(q:ℝ)*(2*L)^2)*(4:ℝ)^(n-2)=M := by
    dsimp only [M,Analysis.rationalMorreyFactor]
    push_cast
    rfl
  rw [hMCast] at hJoint
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
  have hScaleBound : (3/4:ℝ)^(-(1/2:ℝ))≤2 := by
    calc
      _≤(3/4:ℝ)^(-1:ℝ) := Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by norm_num)
      _≤2 := by norm_num
  have H := hwHolder x y
  rw [hScale] at H
  have hRPow : 0≤R.val^(-(1/2:ℝ)) := Real.rpow_nonneg R.property.le _
  have hQuarterPow : 0≤(3/4:ℝ)^(-(1/2:ℝ)) := Real.rpow_nonneg (by norm_num) _
  calc
    _≤(Analysis.effectiveGivenFrameHolderConstant n q:ℝ)*β*
        ((3/4:ℝ)^(-(1/2:ℝ))*R.val^(-(1/2:ℝ)))*(dist (x:Domain n) (y:Domain n))^(1/2:ℝ) := H
    _≤(Analysis.effectiveGivenFrameHolderConstant n q:ℝ)*(K*Real.sqrt energy.toReal)*
        (2*R.val^(-(1/2:ℝ)))*(dist (x:Domain n) (y:Domain n))^(1/2:ℝ) := by
      gcongr
    _=_ := by
      dsimp only [Analysis.effectiveStationaryHolderConstant,Analysis.rationalHolderCoefficient,K,energy]
      push_cast
      simp only [Real.rpow_eq_pow]
      ring

theorem smallEnergySmoothRegularity_effective {n q : ℕ} (hn : 2≤n)
    (N : CompactSmoothEmbeddedTarget q)
    (G : Ambient q → (Ambient q →L[ℝ] Ambient q)) (L : ℚ)
    (hG : ContDiff ℝ 1 G) (hcG : HasCompactSupport G)
    (hGN : ∀ p : (SmoothTarget.toC2 N).Carrier,
      G p.val=(SmoothTarget.toC2 N).normalProjection p)
    (hL : 0≤L) (hDG : ∀ y,‖fderiv ℝ G y‖≤(L:ℝ)) :
      ∀(Ω : OpenDomain n) (u : Domain n→Ambient q) (Du : Domain n→Gradient n q),
        MemW12Loc Ω u Du →
        (∀ᵐx∂volume.restrict Ω.val,u x∈N.carrierSet) →
        IsWeaklyHarmonicByTangentVariations (SmoothTarget.toC2 N) Ω u Du →
        IsDomainStationary Ω Du →
        ∀(a : Domain n) (R : PositiveRadius),closedBall a R.val⊆Ω.val →
          normalizedEnergy Du a R≤ENNReal.ofReal (Analysis.effectiveStationaryEnergyThreshold n q L:ℝ) →
          ∃w : Domain n→Ambient q,
            ContDiffOn ℝ ∞ w (ball a (R.val/2)) ∧
            IsContinuousRepresentative (ballDomain a (R.val/2)) u (fun x=>w x.val) ∧
            (∀x∈ball a (R.val/2),w x∈N.carrierSet) ∧
            (∀x∈ball a (R.val/2),∀y∈ball a (R.val/2),
              ‖w x-w y‖≤(Analysis.effectiveStationaryHolderConstant n q L:ℝ)*R.val^(-(1/2:ℝ))*Real.sqrt (normalizedEnergy Du a R).toReal*(dist x y)^(1/2:ℝ)) ∧
            ∀v : ball a (R.val/2)→Ambient q,
              IsContinuousRepresentative (ballDomain a (R.val/2)) u v →
              v=(fun x=>w x.val) := by
  classical
  let α : ℝ := 1/2
  let C : ℝ := (Analysis.effectiveStationaryHolderConstant n q L:ℝ)
  have hα : 0<α := by norm_num [α]
  have hαOne : α<1 := by norm_num [α]
  have hC : 0≤C := by
    dsimp only [C]
    exact_mod_cast (Analysis.effectiveStationaryHolderConstant_pos n hn q L).le
  intro Ω u Du hu hN hweak hStationary a R hBall hSmall
  have hNC2 : ∀ᵐx∂volume.restrict Ω.val,u x∈(SmoothTarget.toC2 N).carrierSet := by
    simpa only [SmoothTarget.toC2_carrierSet] using hN
  obtain ⟨v,hRep,hVN,hBound,hUnique⟩ := smallEnergyRegularity_effective hn (SmoothTarget.toC2 N) G L hG hcG hGN hL hDG Ω u Du hu hNC2 hweak hStationary a R hBall hSmall
  let w : Domain n→Ambient q := fun x=>if hx : x∈ball a (R.val/2) then v ⟨x,hx⟩ else u x
  have hValue (x : Domain n) (hx : x∈ball a (R.val/2)) : w x=v ⟨x,hx⟩ := dif_pos hx
  have hSame : (fun x : ball a (R.val/2)=>w x.val)=v :=
    funext fun x=>hValue x.val x.property
  have hRepW : IsContinuousRepresentative (ballDomain a (R.val/2)) u (fun x=>w x.val) := by
    exact hSame.symm ▸ hRep
  have hAE : w=ᵐ[volume.restrict (ball a (R.val/2))]u := by
    filter_upwards [hRep.2,ae_restrict_mem measurableSet_ball] with x hx hxb
    exact (hValue x hxb).trans (hx hxb)
  let B : OpenDomain n := ballDomain a (R.val/2)
  have hSub : B.val⊆Ω.val := ball_subset_closedBall.trans
    ((closedBall_subset_closedBall (by linarith only [R.property] : R.val/2≤R.val)).trans hBall)
  have hBoundW : HolderToCK.HolderBoundOn B.val w α
      (C*R.val^(-α)*Real.sqrt (normalizedEnergy Du a R).toReal) := by
    intro x hx y hy
    rw [hValue x hx,hValue y hy]
    exact hBound ⟨x,hx⟩ ⟨y,hy⟩
  have hLocal : HolderToCK.LocallyHolderOn B w := by
    intro x hx
    obtain ⟨r,hr,hbr⟩ := Metric.isOpen_iff.mp isOpen_ball x hx
    have hClosed : closedBall x (r/2)⊆B.val :=
      (closedBall_subset_ball (by linarith only [hr] : r/2<r)).trans hbr
    refine ⟨⟨r/2,half_pos hr⟩,hClosed,α,
      C*R.val^(-α)*Real.sqrt (normalizedEnergy Du a R).toReal,hα,hαOne,?_,?_⟩
    · exact mul_nonneg (mul_nonneg hC (Real.rpow_nonneg R.property.le _)) (Real.sqrt_nonneg _)
    · exact hBoundW.mono (ball_subset_closedBall.trans hClosed)
  have hSmooth := Analysis.smooth_locallyHolder_representative_smooth_target hn N Ω B hSub
    u w Du hu hN hweak hAE hLocal
  refine ⟨w,hSmooth,hRepW,?_,hBoundW,?_⟩
  · intro x hx
    rw [hValue x hx]
    exact hVN ⟨x,hx⟩
  · intro z hz
    exact (hUnique z hz).trans hSame.symm

end StationaryHarmonicMaps.Providers
end
