module

public import StationaryHarmonicMaps.Analysis.CompensatedCutoffPowerGrowth
public import StationaryHarmonicMaps.Analysis.LocalLpMorreyRepresentative
public import StationaryHarmonicMaps.Analysis.EffectiveHolderConstants
public import HarmonicMaps.Analysis.ContinuousRepresentativeLocality
import StationaryHarmonicMaps.Analysis.EffectiveBallCutoff

/-!
# The original target-valued representative after actual compensation

Original compact-target system data and a given small critical Coulomb
frame produce the cutoff's actual improved gradient growth. A radius-two
native Morrey construction supplies a radius-one continuous representative.
The genuine cutoff plateau recovers the same original map throughout
B(0,2/3), with target values, uniqueness and the actual C eta Holder bound.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology ENNReal ContDiff

namespace StationaryHarmonicMaps.Analysis

/-- A genuine cutoff plateau and the original given critical-frame data
produce the unique target-valued Holder representative of the same map.
Neither growth, recurrence nor a continuous representative is an input. -/
theorem exists_compact_target_compensated_cutoff_representative
    (n : ℕ) (hn : 2≤n) (p : ℝ) (hpOne : 1<p) (hpTwo : p<2)
    (hpConj : (n : ℝ)<p/(p-1)) (q : ℕ)
    (E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient (q*q))
    (R : Ambient (q*q) →L[ℝ] (Ambient q →L[ℝ] Ambient q))
    (hRE : ∀T,R (E T)=T) (hER : ∀z,E (R z)=z)
    (hE : ∀T : Ambient q →L[ℝ] Ambient q,‖E T‖^2=∑j : Fin q,‖T (EuclideanSpace.single j 1)‖^2)
    (δ A B L : ℝ) (hδ : 0<δ) (hδOne : δ<1) (hA : 0≤A) (hB : 0≤B) (hL : 0≤L) :
    ∃ε C : ℝ,0<ε ∧ ε≤1 ∧ 0<C ∧ ∀(N : CompactC2EmbeddedTarget q)
      (u : Domain n → Ambient q) (Du : Domain n → Gradient n q) (η : ℝ),
      MemW12 (ballDomain (0 : Domain n) 1) u Du →
      (∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),u x∈N.carrierSet) → 0≤η → η≤ε →
      criticalGradientMorreySquare Du (ball (0 : Domain n) 1)≤ENNReal.ofReal (η^2) →
      ∀(P : Domain n → Ambient (q*q)) (DP : Domain n → Gradient n (q*q)),
        MemW12 (ballDomain (0 : Domain n) 1) P DP →
        (∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),star (R (P x))*R (P x)=1) →
        criticalGradientMorreySquare DP (ball (0 : Domain n) 1)≤ENNReal.ofReal (η^2) →
        ∀Ω : Domain n → Fin n → (Ambient q →L[ℝ] Ambient q),
          (∀i,MemLp (fun x=>Ω x i) 2 (volume.restrict (ball (0 : Domain n) 1))) →
          HolderToCK.WeakPoissonOn (ballDomain (0 : Domain n) 1) Du (fun x=>-(∑i : Fin n,Ω x i (Du x i))) →
          let Z := fun x i=>star (R (P x))*R (DP x i)+star (R (P x))*Ω x i*R (P x)
          HolderToCK.WeakPoissonOn (ballDomain (0 : Domain n) 1) (fun x i=>E (Z x i)) (fun _=>0) →
          criticalGradientMorreySquare (fun x i=>E (Z x i)) (ball (0 : Domain n) 1)≤ENNReal.ofReal (η^2) →
          ∀χ : Domain n → ℝ,ContDiff ℝ ∞ χ → HasCompactSupport χ →
            tsupport χ⊆closedBall (0 : Domain n) (3/4 : ℝ) →
            (∀x,|χ x|≤A) → (∀(x : Domain n) (i : Fin n),|fderiv ℝ χ x (EuclideanSpace.single i 1)|≤B) →
            (∀x,|Laplacian.laplacian χ x|≤L) →
            (∀x∈ball (0:Domain n) (2/3:ℝ),χ x=1) →
            ∃w : ball (0:Domain n) (2/3:ℝ) → Ambient q,
              IsContinuousRepresentative (ballDomain (0:Domain n) (2/3:ℝ)) u w ∧
              (∀x,w x∈N.carrierSet) ∧
              (∀x y,‖w x-w y‖≤C*η*(dist (x:Domain n) (y:Domain n))^(1-δ)) ∧
              ∀W : ball (0:Domain n) (2/3:ℝ) → Ambient q,
                IsContinuousRepresentative (ballDomain (0:Domain n) (2/3:ℝ)) u W → W=w := by
  have hp : 0<p := zero_lt_one.trans hpOne
  let α := 1-δ
  have hα : 0<α := sub_pos.mpr hδOne
  have hαOne : α<1 := by dsimp only [α];linarith only [hδ]
  obtain ⟨ε,D,hε,hεOne,hD,HGrowth⟩ := exists_compact_target_cutoff_power_growth
    n hn p hpOne hpTwo hpConj q E R hRE hER hE δ A B L hδ hδOne hA hB hL
  obtain ⟨S,hS,HRep⟩ := existsUnique_local_representative_of_lp_gradient_growth
    n p α hpOne.le hpTwo.le hα hαOne
  let C := S*D^(1/p)
  have hC : 0<C := mul_pos hS (Real.rpow_pos_of_pos hD _)
  refine ⟨ε,C,hε,hεOne,hC,?_⟩
  intro N u Du η hu hTarget hη hηle hCritical P DP hP hOrth hDPCritical Ω hΩ hEq Z hDiv hZCritical
    χ hχ hcχ hsχ hχA hDχ hLap hOne
  let c := ⨍y in ball (0:Domain n) 1,u y
  let v := fun x=>χ x • (u x-c)
  let Dv := fun x i=>χ x • Du x i+fderiv ℝ χ x (EuclideanSpace.single i 1) • (u x-c)
  obtain ⟨hV,_hPsi,Henergy⟩ := HGrowth N u Du η hu hTarget hη hηle hCritical P DP hP hOrth hDPCritical
    Ω hΩ hEq hDiv hZCritical χ hχ hcχ hsχ hχA hDχ hLap
  let K := D^(1/p)*η
  have hK : 0≤K := mul_nonneg (Real.rpow_nonneg hD.le _) hη
  have hKPower : K^p=D*η^p := by
    rw [Real.mul_rpow (Real.rpow_nonneg hD.le _) hη,←Real.rpow_mul hD.le]
    rw [show (1/p)*p=1 by field_simp,Real.rpow_one]
  have hRawGrowth (x : Domain n) (_hx : x∈ball (0:Domain n) (3*(2:ℝ)/4))
      (r : ℝ) (hr : 0<r) (_hCap : r≤(2:ℝ)/4) :
      (∫y in ball x r,(Real.sqrt (hsNormSq (Dv y)))^p)≤K^p*r^((n:ℝ)-p+p*α) := by
    rw [hKPower]
    exact (Henergy x r hr).2
  have Hlocal := HRep q (⟨univ,isOpen_univ⟩ : OpenDomain n) v Dv K (0:Domain n) 2
    hV.to_memW12Loc (by norm_num) (subset_univ _) hK hRawGrowth
  obtain ⟨V,⟨hVRep,hVHolder⟩,_hUniqueV⟩ := Hlocal
  have hSub : ball (0:Domain n) (2/3:ℝ)⊆ball (0:Domain n) ((2:ℝ)/2) := ball_subset_ball (by norm_num)
  let i : ball (0:Domain n) (2/3:ℝ) → ball (0:Domain n) ((2:ℝ)/2) := inclusion hSub
  have hi : Continuous i := continuous_subtype_val.subtype_mk _
  let w := fun x=>V (i x)+c
  have hwContinuous : Continuous w := (hVRep.1.comp hi).add continuous_const
  have hVAE := ae_restrict_of_ae_restrict_of_subset hSub hVRep.2
  have hwAE : ∀ᵐx∂volume.restrict (ball (0:Domain n) (2/3:ℝ)),
      ∀hx : x∈ball (0:Domain n) (2/3:ℝ),w ⟨x,hx⟩=u x := by
    filter_upwards [hVAE] with x hx
    intro hxBall
    have H := congrArg (fun z : Ambient q=>z+c) (hx (hSub hxBall))
    have hvc : v x+c=u x := by
      dsimp only [v]
      rw [hOne x hxBall,one_smul,sub_add_cancel]
    exact H.trans hvc
  have hw : IsContinuousRepresentative (ballDomain (0:Domain n) (2/3:ℝ)) u w := ⟨hwContinuous,hwAE⟩
  have hwN := hw.mem_closed_of_ae N.carrierSet N.isCompact.isClosed
    (ae_restrict_of_ae_restrict_of_subset (ball_subset_ball (by norm_num : (2/3:ℝ)≤1)) hTarget)
  refine ⟨w,hw,hwN,?_,?_⟩
  · intro x y
    change ‖(V (i x)+c)-(V (i y)+c)‖≤C*η*(dist (x:Domain n) (y:Domain n))^α
    rw [add_sub_add_right_eq_sub]
    exact (hVHolder (i x) (i y)).trans_eq (by dsimp only [K,C];ring)
  · intro W hW
    exact hW.unique hw

@[expose] def effectiveCutoffHolderConstant (n q A B L : ℕ) : ℚ :=
  (explicitLpMorreyRepresentativeMajorant n : ℚ)*(1+effectiveCutoffPowerGrowthConstant n q A B L)

theorem exists_compact_target_compensated_cutoff_representative_effective
    (n : ℕ) (hn : 2≤n) (p : ℝ) (hpOne : 1<p) (hpTwo : p<2)
    (hpConj : (n : ℝ)<p/(p-1)) (q : ℕ)
    (E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient (q*q))
    (R : Ambient (q*q) →L[ℝ] (Ambient q →L[ℝ] Ambient q))
    (hRE : ∀T,R (E T)=T) (hER : ∀z,E (R z)=z)
    (hE : ∀T : Ambient q →L[ℝ] Ambient q,‖E T‖^2=∑j : Fin q,‖T (EuclideanSpace.single j 1)‖^2)
    (A B L : ℕ) (hConjugate : p/(p-1)=((2*n+1 : ℕ) : ℝ)) :
    ∃ε C : ℝ,0<ε ∧ ε≤1 ∧ 0<C ∧
      ε=(effectiveCutoffPowerSmallness n q B L:ℝ) ∧
      C=(effectiveCutoffHolderConstant n q A B L:ℝ) ∧ ∀(N : CompactC2EmbeddedTarget q)
      (u : Domain n → Ambient q) (Du : Domain n → Gradient n q) (η : ℝ),
      MemW12 (ballDomain (0 : Domain n) 1) u Du →
      (∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),u x∈N.carrierSet) → 0≤η → η≤ε →
      criticalGradientMorreySquare Du (ball (0 : Domain n) 1)≤ENNReal.ofReal (η^2) →
      ∀(P : Domain n → Ambient (q*q)) (DP : Domain n → Gradient n (q*q)),
        MemW12 (ballDomain (0 : Domain n) 1) P DP →
        (∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),star (R (P x))*R (P x)=1) →
        criticalGradientMorreySquare DP (ball (0 : Domain n) 1)≤ENNReal.ofReal (η^2) →
        ∀Ω : Domain n → Fin n → (Ambient q →L[ℝ] Ambient q),
          (∀i,MemLp (fun x=>Ω x i) 2 (volume.restrict (ball (0 : Domain n) 1))) →
          HolderToCK.WeakPoissonOn (ballDomain (0 : Domain n) 1) Du (fun x=>-(∑i : Fin n,Ω x i (Du x i))) →
          let Z := fun x i=>star (R (P x))*R (DP x i)+star (R (P x))*Ω x i*R (P x)
          HolderToCK.WeakPoissonOn (ballDomain (0 : Domain n) 1) (fun x i=>E (Z x i)) (fun _=>0) →
          criticalGradientMorreySquare (fun x i=>E (Z x i)) (ball (0 : Domain n) 1)≤ENNReal.ofReal (η^2) →
          ∀χ : Domain n → ℝ,ContDiff ℝ ∞ χ → HasCompactSupport χ →
            tsupport χ⊆closedBall (0 : Domain n) (3/4 : ℝ) →
            (∀x,|χ x|≤A) → (∀(x : Domain n) (i : Fin n),|fderiv ℝ χ x (EuclideanSpace.single i 1)|≤B) →
            (∀x,|Laplacian.laplacian χ x|≤L) →
            (∀x∈ball (0:Domain n) (2/3:ℝ),χ x=1) →
            ∃w : ball (0:Domain n) (2/3:ℝ) → Ambient q,
              IsContinuousRepresentative (ballDomain (0:Domain n) (2/3:ℝ)) u w ∧
              (∀x,w x∈N.carrierSet) ∧
              (∀x y,‖w x-w y‖≤C*η*(dist (x:Domain n) (y:Domain n))^(1-(1/2 : ℝ))) ∧
              ∀W : ball (0:Domain n) (2/3:ℝ) → Ambient q,
                IsContinuousRepresentative (ballDomain (0:Domain n) (2/3:ℝ)) u W → W=w := by
  have hp : 0<p := zero_lt_one.trans hpOne
  let α : ℝ := 1-(1/2 : ℝ)
  have hαEq : α=(1/2 : ℝ) := by norm_num [α]
  have hα : 0<α := by norm_num [α]
  have hαOne : α<1 := by norm_num [α]
  obtain ⟨ε,D,hε,hεOne,hD,hεF,hDF,HGrowth⟩ := exists_compact_target_cutoff_power_growth_effective
    n hn p hpOne hpTwo hpConj q E R hRE hER hE A B L hConjugate
  obtain ⟨S,hS,hSF,HRep⟩ := existsUnique_local_representative_of_lp_gradient_growth_explicit
    n p α hpOne.le hpTwo.le hα hαOne
  have hSbound : S≤(explicitLpMorreyRepresentativeMajorant n : ℝ) := by
    rw [hSF,hαEq]
    exact localLpMorreyRepresentativeConstant_half_le n p hpOne.le
  let C : ℝ := effectiveCutoffHolderConstant n q A B L
  have hCrbound : S*D^(1/p)≤C := by
    have H := mul_le_mul hSbound (effective_root_majorant_helper D p hD.le hpOne.le)
      (Real.rpow_nonneg hD.le _) (Nat.cast_nonneg _)
    exact H.trans_eq (by
      dsimp only [C,effectiveCutoffHolderConstant]
      simp only [Rat.cast_mul,Rat.cast_natCast,Rat.cast_add,Rat.cast_one]
      rw [hDF])
  have hC : 0<C := lt_of_lt_of_le (mul_pos hS (Real.rpow_pos_of_pos hD _)) hCrbound
  refine ⟨ε,C,hε,hεOne,hC,hεF,rfl,?_⟩
  intro N u Du η hu hTarget hη hηle hCritical P DP hP hOrth hDPCritical Ω hΩ hEq Z hDiv hZCritical
    χ hχ hcχ hsχ hχA hDχ hLap hOne
  let c := ⨍y in ball (0:Domain n) 1,u y
  let v := fun x=>χ x • (u x-c)
  let Dv := fun x i=>χ x • Du x i+fderiv ℝ χ x (EuclideanSpace.single i 1) • (u x-c)
  obtain ⟨hV,_hPsi,Henergy⟩ := HGrowth N u Du η hu hTarget hη hηle hCritical P DP hP hOrth hDPCritical
    Ω hΩ hEq hDiv hZCritical χ hχ hcχ hsχ hχA hDχ hLap
  let K := D^(1/p)*η
  have hK : 0≤K := mul_nonneg (Real.rpow_nonneg hD.le _) hη
  have hKPower : K^p=D*η^p := by
    rw [Real.mul_rpow (Real.rpow_nonneg hD.le _) hη,←Real.rpow_mul hD.le]
    rw [show (1/p)*p=1 by field_simp,Real.rpow_one]
  have hRawGrowth (x : Domain n) (_hx : x∈ball (0:Domain n) (3*(2:ℝ)/4))
      (r : ℝ) (hr : 0<r) (_hCap : r≤(2:ℝ)/4) :
      (∫y in ball x r,(Real.sqrt (hsNormSq (Dv y)))^p)≤K^p*r^((n:ℝ)-p+p*α) := by
    rw [hKPower]
    exact (Henergy x r hr).2
  have Hlocal := HRep q (⟨univ,isOpen_univ⟩ : OpenDomain n) v Dv K (0:Domain n) 2
    hV.to_memW12Loc (by norm_num) (subset_univ _) hK hRawGrowth
  obtain ⟨V,⟨hVRep,hVHolder⟩,_hUniqueV⟩ := Hlocal
  have hSub : ball (0:Domain n) (2/3:ℝ)⊆ball (0:Domain n) ((2:ℝ)/2) := ball_subset_ball (by norm_num)
  let i : ball (0:Domain n) (2/3:ℝ) → ball (0:Domain n) ((2:ℝ)/2) := inclusion hSub
  have hi : Continuous i := continuous_subtype_val.subtype_mk _
  let w := fun x=>V (i x)+c
  have hwContinuous : Continuous w := (hVRep.1.comp hi).add continuous_const
  have hVAE := ae_restrict_of_ae_restrict_of_subset hSub hVRep.2
  have hwAE : ∀ᵐx∂volume.restrict (ball (0:Domain n) (2/3:ℝ)),
      ∀hx : x∈ball (0:Domain n) (2/3:ℝ),w ⟨x,hx⟩=u x := by
    filter_upwards [hVAE] with x hx
    intro hxBall
    have H := congrArg (fun z : Ambient q=>z+c) (hx (hSub hxBall))
    have hvc : v x+c=u x := by
      dsimp only [v]
      rw [hOne x hxBall,one_smul,sub_add_cancel]
    exact H.trans hvc
  have hw : IsContinuousRepresentative (ballDomain (0:Domain n) (2/3:ℝ)) u w := ⟨hwContinuous,hwAE⟩
  have hwN := hw.mem_closed_of_ae N.carrierSet N.isCompact.isClosed
    (ae_restrict_of_ae_restrict_of_subset (ball_subset_ball (by norm_num : (2/3:ℝ)≤1)) hTarget)
  refine ⟨w,hw,hwN,?_,?_⟩
  · intro x y
    change ‖(V (i x)+c)-(V (i y)+c)‖≤C*η*(dist (x:Domain n) (y:Domain n))^α
    rw [add_sub_add_right_eq_sub]
    calc
      _≤(S*D^(1/p))*η*(dist (x:Domain n) (y:Domain n))^α :=
        (hVHolder (i x) (i y)).trans_eq (by dsimp only [K];ring)
      _≤_ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCrbound hη)
        (Real.rpow_nonneg dist_nonneg _)
  · intro W hW
    exact hW.unique hw

theorem exists_compensation_cutoff_explicit (n : ℕ) :
    ∃(χ : Domain n → ℝ) (B L : ℝ),B = (2 : ℝ)^24 ∧ L = (2 : ℝ)^48 + (2 : ℝ)^25*(n : ℝ) ∧ ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      tsupport χ⊆closedBall (0:Domain n) (3/4:ℝ) ∧
      (∀x,|χ x|≤1) ∧ 0≤B ∧ 0≤L ∧
      (∀(x : Domain n) (i : Fin n),|fderiv ℝ χ x (EuclideanSpace.single i 1)|≤B) ∧
      (∀x,|Laplacian.laplacian χ x|≤L) ∧
      ∀x∈ball (0:Domain n) (2/3:ℝ),χ x=1 := by
  let χ : Domain n → ℝ := effectiveBallCutoff
  refine ⟨χ, (2 : ℝ)^24, (2 : ℝ)^48 + (2 : ℝ)^25*(n : ℝ),
    rfl, rfl, effectiveBallCutoff_contDiff, effectiveBallCutoff_hasCompactSupport,
    effectiveBallCutoff_tsupport_subset, ?_, by positivity, by positivity, ?_, ?_, ?_⟩
  · intro x
    rw [abs_of_nonneg (effectiveBallCutoff_mem_Icc x).1]
    exact (effectiveBallCutoff_mem_Icc x).2
  · intro x i
    calc
      _ = ‖fderiv ℝ χ x (EuclideanSpace.single i (1 : ℝ))‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖fderiv ℝ χ x‖*‖EuclideanSpace.single i (1 : ℝ)‖ :=
        (fderiv ℝ χ x).le_opNorm _
      _ = ‖fderiv ℝ χ x‖ := by simp only [PiLp.norm_single, norm_one, mul_one]
      _ ≤ (2 : ℝ)^24 := effectiveBallCutoff_fderiv_bound x
  · intro x
    exact effectiveBallCutoff_laplacian_bound x
  · intro x hx
    exact effectiveBallCutoff_eq_one (mem_ball_zero_iff.mp hx).le

private theorem exists_compensation_cutoff (n : ℕ) :
    ∃(χ : Domain n → ℝ) (B L : ℝ),ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      tsupport χ⊆closedBall (0:Domain n) (3/4:ℝ) ∧
      (∀x,|χ x|≤1) ∧ 0≤B ∧ 0≤L ∧
      (∀(x : Domain n) (i : Fin n),|fderiv ℝ χ x (EuclideanSpace.single i 1)|≤B) ∧
      (∀x,|Laplacian.laplacian χ x|≤L) ∧
      ∀x∈ball (0:Domain n) (2/3:ℝ),χ x=1 := by
  obtain ⟨χ,B,L,_hBFormula,_hLFormula,H⟩ := exists_compensation_cutoff_explicit n
  exact ⟨χ,B,L,H⟩

/-- A fixed genuine smooth cutoff is constructed internally. The constants
precede the compact target, map, frame and connection, and the conclusion
refers to the same original map on B(0,2/3). -/
theorem exists_compact_target_compensated_representative
    (n : ℕ) (hn : 2≤n) (p : ℝ) (hpOne : 1<p) (hpTwo : p<2)
    (hpConj : (n : ℝ)<p/(p-1)) (q : ℕ)
    (E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient (q*q))
    (R : Ambient (q*q) →L[ℝ] (Ambient q →L[ℝ] Ambient q))
    (hRE : ∀T,R (E T)=T) (hER : ∀z,E (R z)=z)
    (hE : ∀T : Ambient q →L[ℝ] Ambient q,‖E T‖^2=∑j : Fin q,‖T (EuclideanSpace.single j 1)‖^2)
    (δ : ℝ) (hδ : 0<δ) (hδOne : δ<1) :
    ∃ε C : ℝ,0<ε ∧ ε≤1 ∧ 0<C ∧ ∀(N : CompactC2EmbeddedTarget q)
      (u : Domain n → Ambient q) (Du : Domain n → Gradient n q) (η : ℝ),
      MemW12 (ballDomain (0 : Domain n) 1) u Du →
      (∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),u x∈N.carrierSet) → 0≤η → η≤ε →
      criticalGradientMorreySquare Du (ball (0 : Domain n) 1)≤ENNReal.ofReal (η^2) →
      ∀(P : Domain n → Ambient (q*q)) (DP : Domain n → Gradient n (q*q)),
        MemW12 (ballDomain (0 : Domain n) 1) P DP →
        (∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),star (R (P x))*R (P x)=1) →
        criticalGradientMorreySquare DP (ball (0 : Domain n) 1)≤ENNReal.ofReal (η^2) →
        ∀Ω : Domain n → Fin n → (Ambient q →L[ℝ] Ambient q),
          (∀i,MemLp (fun x=>Ω x i) 2 (volume.restrict (ball (0 : Domain n) 1))) →
          HolderToCK.WeakPoissonOn (ballDomain (0 : Domain n) 1) Du (fun x=>-(∑i : Fin n,Ω x i (Du x i))) →
          let Z := fun x i=>star (R (P x))*R (DP x i)+star (R (P x))*Ω x i*R (P x)
          HolderToCK.WeakPoissonOn (ballDomain (0 : Domain n) 1) (fun x i=>E (Z x i)) (fun _=>0) →
          criticalGradientMorreySquare (fun x i=>E (Z x i)) (ball (0 : Domain n) 1)≤ENNReal.ofReal (η^2) →
            ∃w : ball (0:Domain n) (2/3:ℝ) → Ambient q,
              IsContinuousRepresentative (ballDomain (0:Domain n) (2/3:ℝ)) u w ∧
              (∀x,w x∈N.carrierSet) ∧
              (∀x y,‖w x-w y‖≤C*η*(dist (x:Domain n) (y:Domain n))^(1-δ)) ∧
              ∀W : ball (0:Domain n) (2/3:ℝ) → Ambient q,
                IsContinuousRepresentative (ballDomain (0:Domain n) (2/3:ℝ)) u W → W=w := by
  obtain ⟨χ,B,L,hχ,hcχ,hsχ,hχA,hB,hL,hDχ,hLap,hOne⟩ := exists_compensation_cutoff n
  obtain ⟨ε,C,hε,hεOne,hC,H⟩ := exists_compact_target_compensated_cutoff_representative
    n hn p hpOne hpTwo hpConj q E R hRE hER hE δ 1 B L hδ hδOne (by norm_num) hB hL
  refine ⟨ε,C,hε,hεOne,hC,?_⟩
  intro N u Du η hu hTarget hη hηle hCritical P DP hP hOrth hDPCritical Ω hΩ hEq Z hDiv hZCritical
  exact H N u Du η hu hTarget hη hηle hCritical P DP hP hOrth hDPCritical Ω hΩ hEq
    hDiv hZCritical χ hχ hcχ hsχ hχA hDχ hLap hOne

@[expose] def effectiveCompensationCutoffGradientBound : ℕ := 2^24

@[expose] def effectiveCompensationCutoffLaplacianBound (n : ℕ) : ℕ := 2^48+2^25*n

@[expose] def effectiveGivenFrameSmallness (n q : ℕ) : ℚ :=
  effectiveCutoffPowerSmallness n q effectiveCompensationCutoffGradientBound
    (effectiveCompensationCutoffLaplacianBound n)

@[expose] def effectiveGivenFrameHolderConstant (n q : ℕ) : ℚ :=
  effectiveCutoffHolderConstant n q 1 effectiveCompensationCutoffGradientBound
    (effectiveCompensationCutoffLaplacianBound n)

theorem effectiveGivenFrameSmallness_pos (n q : ℕ) : 0 < effectiveGivenFrameSmallness n q :=
  effectiveCutoffPowerSmallness_pos n q _ _

theorem effectiveGivenFrameSmallness_le_one (n q : ℕ) : effectiveGivenFrameSmallness n q ≤ 1 :=
  effectiveCutoffPowerSmallness_le_one n q _ _

theorem effectiveCutoffHolderConstant_pos (n q A B L : ℕ) :
    0 < effectiveCutoffHolderConstant n q A B L := by
  have H := effectiveCutoffPowerGrowthConstant_pos n q A B L
  have HS : 0 < (explicitLpMorreyRepresentativeMajorant n : ℚ) := by
    unfold explicitLpMorreyRepresentativeMajorant
    positivity
  unfold effectiveCutoffHolderConstant
  positivity

theorem effectiveGivenFrameHolderConstant_pos (n q : ℕ) : 0 < effectiveGivenFrameHolderConstant n q :=
  effectiveCutoffHolderConstant_pos n q 1 _ _

theorem exists_compact_target_compensated_representative_effective
    (n : ℕ) (hn : 2≤n) (p : ℝ) (hpOne : 1<p) (hpTwo : p<2)
    (hpConj : (n : ℝ)<p/(p-1)) (q : ℕ)
    (E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient (q*q))
    (R : Ambient (q*q) →L[ℝ] (Ambient q →L[ℝ] Ambient q))
    (hRE : ∀T,R (E T)=T) (hER : ∀z,E (R z)=z)
    (hE : ∀T : Ambient q →L[ℝ] Ambient q,‖E T‖^2=∑j : Fin q,‖T (EuclideanSpace.single j 1)‖^2)
    (hConjugate : p/(p-1)=((2*n+1 : ℕ) : ℝ)) :
    ∃ε C : ℝ,0<ε ∧ ε≤1 ∧ 0<C ∧
      ε=(effectiveGivenFrameSmallness n q : ℝ) ∧
      C=(effectiveGivenFrameHolderConstant n q : ℝ) ∧ ∀(N : CompactC2EmbeddedTarget q)
      (u : Domain n → Ambient q) (Du : Domain n → Gradient n q) (η : ℝ),
      MemW12 (ballDomain (0 : Domain n) 1) u Du →
      (∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),u x∈N.carrierSet) → 0≤η → η≤ε →
      criticalGradientMorreySquare Du (ball (0 : Domain n) 1)≤ENNReal.ofReal (η^2) →
      ∀(P : Domain n → Ambient (q*q)) (DP : Domain n → Gradient n (q*q)),
        MemW12 (ballDomain (0 : Domain n) 1) P DP →
        (∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),star (R (P x))*R (P x)=1) →
        criticalGradientMorreySquare DP (ball (0 : Domain n) 1)≤ENNReal.ofReal (η^2) →
        ∀Ω : Domain n → Fin n → (Ambient q →L[ℝ] Ambient q),
          (∀i,MemLp (fun x=>Ω x i) 2 (volume.restrict (ball (0 : Domain n) 1))) →
          HolderToCK.WeakPoissonOn (ballDomain (0 : Domain n) 1) Du (fun x=>-(∑i : Fin n,Ω x i (Du x i))) →
          let Z := fun x i=>star (R (P x))*R (DP x i)+star (R (P x))*Ω x i*R (P x)
          HolderToCK.WeakPoissonOn (ballDomain (0 : Domain n) 1) (fun x i=>E (Z x i)) (fun _=>0) →
          criticalGradientMorreySquare (fun x i=>E (Z x i)) (ball (0 : Domain n) 1)≤ENNReal.ofReal (η^2) →
            ∃w : ball (0:Domain n) (2/3:ℝ) → Ambient q,
              IsContinuousRepresentative (ballDomain (0:Domain n) (2/3:ℝ)) u w ∧
              (∀x,w x∈N.carrierSet) ∧
              (∀x y,‖w x-w y‖≤C*η*(dist (x:Domain n) (y:Domain n))^(1/2 : ℝ)) ∧
              ∀W : ball (0:Domain n) (2/3:ℝ) → Ambient q,
                IsContinuousRepresentative (ballDomain (0:Domain n) (2/3:ℝ)) u W → W=w := by
  obtain ⟨χ,B,L,hBF,hLF,hχ,hcχ,hsχ,hχA,_hB,_hL,hDχ,hLap,hOne⟩ := exists_compensation_cutoff_explicit n
  have hDBC : ∀ (x : Domain n) (i : Fin n), |fderiv ℝ χ x (EuclideanSpace.single i 1)| ≤
      (effectiveCompensationCutoffGradientBound : ℝ) := by
    intro x i
    simpa only [hBF,effectiveCompensationCutoffGradientBound,Nat.cast_pow,Nat.cast_ofNat] using hDχ x i
  have hLBC : ∀ x, |Laplacian.laplacian χ x| ≤ (effectiveCompensationCutoffLaplacianBound n : ℝ) := by
    intro x
    simpa only [hLF,effectiveCompensationCutoffLaplacianBound,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using hLap x
  obtain ⟨ε,C,hε,hεOne,hC,hεF,hCF,H⟩ := exists_compact_target_compensated_cutoff_representative_effective
    n hn p hpOne hpTwo hpConj q E R hRE hER hE 1 effectiveCompensationCutoffGradientBound
      (effectiveCompensationCutoffLaplacianBound n) hConjugate
  refine ⟨ε,C,hε,hεOne,hC,hεF,hCF,?_⟩
  intro N u Du η hu hTarget hη hηle hCritical P DP hP hOrth hDPCritical Ω hΩ hEq Z hDiv hZCritical
  have Hdata := H N u Du η hu hTarget hη hηle hCritical P DP hP hOrth hDPCritical Ω hΩ hEq
    hDiv hZCritical χ hχ hcχ hsχ (by simpa only [Nat.cast_one] using hχA) hDBC hLBC hOne
  norm_num only [show (1 : ℝ)-1/2=1/2 by norm_num] at Hdata
  exact Hdata

end StationaryHarmonicMaps.Analysis

end
