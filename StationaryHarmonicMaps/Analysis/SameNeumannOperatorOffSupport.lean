module

public import StationaryHarmonicMaps.Analysis.EffectiveNeumannBoundary
public import StationaryHarmonicMaps.Analysis.NeumannOperatorOffSupport
public import Mathlib.Analysis.Normed.Module.Normalize

/-!
# One actual Neumann operator with off-support bounds for all query balls

The same operator and the same native response precede every query.
Empty intersections give zero directly. Large intersecting queries force
the original input to vanish everywhere on the unit ball. Small queries
use the actual interior harmonic bound or a nearby genuine unit-sphere
center and the actual boundary harmonic bound. Every geometric case and
volume factor is produced in the proof.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology

namespace StationaryHarmonicMaps.Analysis

private theorem inverse_ball_volume_dilate {n : ℕ} (a b : Domain n) {s t : ℝ}
    (hs : 0<s) (ht : 0<t) :
    (volume.real (ball b s))⁻¹=t^n*(volume.real (ball a (t*s)))⁻¹ := by
  have hV := (HolderToCK.ball_volume_real_pos (0:Domain n) (by norm_num : (0:ℝ)<1)).ne'
  rw [HolderToCK.ball_volume_real b hs,HolderToCK.ball_volume_real a (mul_pos ht hs),mul_pow]
  field_simp [pow_ne_zero n hs.ne',pow_ne_zero n ht.ne',hV]

private theorem normalized_boundary_center_of_small_query {n : ℕ}
    (a : Domain n) (r : ℝ) (hr : 0<r) (hSmall : r<1/64)
    (hMeet : (ball a r∩ball (0:Domain n) 1).Nonempty)
    (hNot : ¬closedBall a (8*r)⊆ball (0:Domain n) 1) :
    ∃b : Domain n,‖b‖=1 ∧ dist a b≤8*r := by
  obtain ⟨x,hx,hxU⟩ := hMeet
  obtain ⟨z,hz,hzOut⟩ := Set.not_subset.mp hNot
  have hAUpper : ‖a‖<1+r := by
    have H := dist_triangle a x 0
    have Hx : dist a x<r := by rw [dist_comm];exact hx
    have HxU : dist x 0<1 := hxU
    rw [dist_zero_right] at H
    linarith
  have hALower : 1≤8*r+‖a‖ := by
    have H := dist_triangle z a 0
    have Hz : dist z a≤8*r := hz
    have HOut : 1≤‖z‖ := not_lt.mp (by simpa only [mem_ball_zero_iff] using hzOut)
    rw [dist_zero_right,dist_zero_right] at H
    linarith
  have haPos : 0<‖a‖ := by linarith
  let b := NormedSpace.normalize a
  have hb : ‖b‖=1 := NormedSpace.norm_normalize (norm_pos_iff.mp haPos)
  have hScale : ‖a‖ • b=a := NormedSpace.norm_smul_normalize a
  have hDiff : a-b=(‖a‖-1) • b := by
    calc
      _=(‖a‖ • b)-b := congrArg (fun v : Domain n=>v-b) hScale.symm
      _=_ := by module
  have hDist : dist a b=|‖a‖-1| := by rw [dist_eq_norm,hDiff,norm_smul,hb,mul_one,Real.norm_eq_abs]
  refine ⟨b,hb,?_⟩
  rw [hDist]
  exact abs_le.mpr ⟨by linarith,by linarith⟩

@[expose] def effectiveNeumannOffSupportConstant (n : ℕ) : ℕ :=
  max (64 ^ n) (EffectiveCoulomb.neumannBoundaryBound n * 16 ^ n)

theorem effectiveNeumannOffSupportConstant_pos (n : ℕ) :
    0 < (effectiveNeumannOffSupportConstant n : ℝ) := by
  have H : (0 : ℝ) < (64 : ℝ) ^ n := by positivity
  exact H.trans_le (by
    simp only [effectiveNeumannOffSupportConstant, Nat.cast_max, Nat.cast_pow,
      Nat.cast_mul, Nat.cast_ofNat]
    exact le_max_left _ _)

/-- For each dimension at least two, one genuine contractive self-adjoint Neumann L2 operator has the same-response essential off-support bound on every center and positive radius, with a dimension-only constant chosen before the target dimension and all original data. -/
theorem effective_same_neumann_operator_all_ball_offSupport_bounds (n : ℕ) (hn : 2≤n) :
    ∀q : ℕ,
      let μ := volume.restrict (ball (0:Domain n) 1)
      let E : Gradient n q → Ambient (n*q) := fun A=>WithLp.toLp 2
        (fun k=>A (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)
      ∃T : Lp (Ambient (n*q)) 2 μ →L[ℝ] Lp (Ambient (n*q)) 2 μ,
        ‖T‖≤1 ∧ IsSelfAdjoint T ∧ (∀Z,T (T Z)=T Z) ∧
        ∀(F : Domain n → Gradient n q) (hF : ∀i,MemLp (fun x=>F x i) 2 μ),
          let A := (memLp_hs_flatten F hF).toLp (fun x=>E (F x))
          let Q := fun (x : Domain n) (i : Fin n)=>WithLp.toLp 2
            (fun j : Fin q=>(T A) x (finProdFinEquiv (i,j)))
          let Q₀ := fun x i=>(ball (0:Domain n) 1).indicator (fun y=>Q y i) x
          ∃f : Domain n → Ambient q,MemW12 (ballDomain (0:Domain n) 1) f Q ∧
            (∫x,hsNormSq (Q x) ∂μ)≤∫x,hsNormSq (F x) ∂μ ∧
            (∀ (ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q),
              MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ →
              Integrable (fun x=>∑i : Fin n,inner ℝ (Q x i) (Dψ x i)) μ ∧
              Integrable (fun x=>∑i : Fin n,inner ℝ (F x i) (Dψ x i)) μ ∧
              (∫x,∑i : Fin n,inner ℝ (Q x i) (Dψ x i) ∂μ)=
                ∫x,∑i : Fin n,inner ℝ (F x i) (Dψ x i) ∂μ) ∧
            HolderToCK.WeakPoissonOn (ballDomain (0:Domain n) 1)
              (fun x i=>Q x i-F x i) (fun _=>(0:Ambient q)) ∧
            (∀i,MemLp (fun x=>Q₀ x i) 2 volume) ∧
            ∀(a : Domain n) (r : ℝ),0<r →
              F =ᵐ[volume.restrict (ball (0:Domain n) 1∩ball a (256*r))] (fun _=>(0:Gradient n q)) →
              ∀ᵐx∂volume.restrict (ball a r),hsNormSq (Q₀ x)≤
                (effectiveNeumannOffSupportConstant n : ℝ)*(volume.real (ball a (256*r)))⁻¹*(∫y in ball a (256*r),hsNormSq (Q₀ y)) := by
  let K : ℝ := EffectiveCoulomb.neumannBoundaryBound n
  have hK : 0 < K := by
    change 0 < (EffectiveCoulomb.neumannBoundaryBound n : ℝ)
    exact_mod_cast EffectiveCoulomb.neumannBoundaryBound_pos n
  let C := max ((64:ℝ)^n) (K*(16:ℝ)^n)
  have hC : 0<C := (pow_pos (by norm_num : (0:ℝ)<64) n).trans_le (le_max_left _ _)
  have heq : (effectiveNeumannOffSupportConstant n : ℝ) = C := by
    simp only [effectiveNeumannOffSupportConstant, Nat.cast_max, Nat.cast_pow,
      Nat.cast_mul, Nat.cast_ofNat, C, K]
  rw [heq]
  intro q μ E
  obtain ⟨T,hNorm,hSelf,hIdem,Hresponse⟩ := exists_neumann_L2_operator_interior_offSupport_bounds_unitBall (q:=q) hn
  refine ⟨T,hNorm,hSelf,hIdem,?_⟩
  intro F hF A Q Q₀
  obtain ⟨f,hf,hEnergy,hNat,hEq,Hinterior⟩ := Hresponse F hF
  have hQ₀ (i : Fin n) : MemLp (fun x=>Q₀ x i) 2 volume :=
    (memLp_indicator_iff_restrict measurableSet_ball).mpr (hf.2.2 i)
  have hI₀ : Integrable (fun x=>hsNormSq (Q₀ x)) volume :=
    integrable_finsetSum _ (fun i _=>(hQ₀ i).integrable_norm_pow (by decide : (2:ℕ)≠0))
  refine ⟨f,hf,hEnergy,hNat,hEq,hQ₀,?_⟩
  intro a r hr hZero
  let B := ball a (256*r)
  let M := C*(volume.real B)⁻¹*(∫y in B,hsNormSq (Q₀ y))
  have hM0 : 0≤M := mul_nonneg (mul_nonneg hC.le (inv_nonneg.mpr ENNReal.toReal_nonneg))
    (integral_nonneg fun y=>hsNormSq_nonneg (Q₀ y))
  have hIB : IntegrableOn (fun x=>hsNormSq (Q₀ x)) B volume := hI₀.integrableOn
  by_cases hMeet : (ball a r∩ball (0:Domain n) 1).Nonempty
  · obtain ⟨x₀,hx₀,hx₀U⟩ := hMeet
    have hAUpper : ‖a‖<1+r := by
      have HT := dist_triangle a x₀ 0
      have HX : dist a x₀<r := by rw [dist_comm];exact hx₀
      have HU : dist x₀ 0<1 := hx₀U
      rw [dist_zero_right] at HT
      linarith
    by_cases hLarge : (1/64:ℝ)≤r
    · have hUnitBig : ball (0:Domain n) 1⊆B := by
        intro y hy
        have HT := dist_triangle y 0 a
        have HY : dist y 0<1 := hy
        rw [dist_zero_left] at HT
        change dist y a<256*r
        linarith
      have hUnitCap : ball (0:Domain n) 1⊆ball (0:Domain n) 1∩ball a (256*r) :=
        fun y hy=>⟨hy,hUnitBig hy⟩
      have hFUnit : F =ᵐ[μ] (fun _=>(0:Gradient n q)) :=
        ae_restrict_of_ae_restrict_of_subset hUnitCap hZero
      have hFEnergy : (∫x,hsNormSq (F x) ∂μ)=0 := by
        have H0 : (fun x=>hsNormSq (F x)) =ᵐ[μ] (fun _=>(0:ℝ)) :=
          hFUnit.mono (fun x hx=>by change hsNormSq (F x)=0;rw [hx];simp only [hsNormSq,Pi.zero_apply,norm_zero,
            zero_pow (by decide : (2:ℕ)≠0),Finset.sum_const_zero])
        rw [integral_congr_ae H0,integral_zero]
      have hQEnergy : (∫x,hsNormSq (Q x) ∂μ)=0 := le_antisymm
        (hEnergy.trans_eq hFEnergy) (integral_nonneg fun x=>hsNormSq_nonneg (Q x))
      have hIQ : Integrable (fun x=>hsNormSq (Q x)) μ :=
        integrable_finsetSum _ (fun i _=>(hf.2.2 i).integrable_norm_pow (by decide : (2:ℕ)≠0))
      have hHS := (integral_eq_zero_iff_of_nonneg (fun x=>hsNormSq_nonneg (Q x)) hIQ).mp hQEnergy
      have hHSConditional := (ae_restrict_iff' measurableSet_ball).mp hHS
      have hZero₀ : ∀ᵐx∂volume,hsNormSq (Q₀ x)=0 := by
        filter_upwards [hHSConditional] with x hx
        by_cases hIn : x∈ball (0:Domain n) 1
        · simpa only [Q₀,indicator_of_mem hIn,Pi.zero_apply] using hx hIn
        · simp only [Q₀,indicator_of_notMem hIn,hsNormSq,norm_zero,zero_pow (by decide : (2:ℕ)≠0),Finset.sum_const_zero]
      exact (hZero₀.filter_mono (ae_mono Measure.restrict_le_self)).mono (fun x hx=>by rw [hx];exact hM0)
    · have hSmall : r<1/64 := lt_of_not_ge hLarge
      by_cases hContained : closedBall a (8*r)⊆ball (0:Domain n) 1
      · have hSmallUnit : ball a (8*r)⊆ball (0:Domain n) 1 := ball_subset_closedBall.trans hContained
        have hSmallBig : ball a (8*r)⊆B := ball_subset_ball (by linarith)
        have hSmallCap : ball a (8*r)⊆ball (0:Domain n) 1∩ball a (256*r) :=
          fun x hx=>⟨hSmallUnit hx,hSmallBig hx⟩
        have hFSmall : F =ᵐ[volume.restrict (ball a (8*r))] (fun _=>(0:Gradient n q)) :=
          ae_restrict_of_ae_restrict_of_subset hSmallCap hZero
        obtain ⟨_V,_hV,_hAE,_hLap,_hGrad,_hPoint,hBound,_hTop,_hAll⟩ :=
          Hinterior a ⟨8*r,by positivity⟩ hSmallUnit hFSmall
        have hHalf : (8*r)/2=4*r := by ring
        change ∀ᵐx∂volume.restrict (ball a ((8*r)/2)),hsNormSq (Q x)≤
          (volume.real (ball a ((8*r)/2)))⁻¹*(∫y in ball a (8*r),hsNormSq (Q y)) at hBound
        rw [hHalf] at hBound
        have hQueryHalf : ball a r⊆ball a (4*r) := ball_subset_ball (by linarith)
        have hEnergySmall : (∫y in ball a (8*r),hsNormSq (Q y))≤∫y in B,hsNormSq (Q₀ y) := by
          calc
            _=∫y in ball a (8*r),hsNormSq (Q₀ y) := by
              apply setIntegral_congr_fun measurableSet_ball
              intro y hy
              simp only [Q₀,indicator_of_mem (hSmallUnit hy)]
            _≤_ := setIntegral_mono_set hIB (Eventually.of_forall fun y=>hsNormSq_nonneg (Q₀ y))
              (Eventually.of_forall fun y hy=>hSmallBig hy)
        have hVolume : (volume.real (ball a (4*r)))⁻¹=(64:ℝ)^n*(volume.real B)⁻¹ := by
          have H := inverse_ball_volume_dilate a a (s:=4*r) (t:=64) (by positivity) (by norm_num)
          simpa only [show (64:ℝ)*(4*r)=256*r by ring] using H
        have hScale : (volume.real (ball a (4*r)))⁻¹*(∫y in ball a (8*r),hsNormSq (Q y))≤M := by
          calc
            _≤(volume.real (ball a (4*r)))⁻¹*(∫y in B,hsNormSq (Q₀ y)) :=
              mul_le_mul_of_nonneg_left hEnergySmall (inv_nonneg.mpr ENNReal.toReal_nonneg)
            _=(64:ℝ)^n*(volume.real B)⁻¹*(∫y in B,hsNormSq (Q₀ y)) := by rw [hVolume]
            _≤M := mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (le_max_left _ _) (inv_nonneg.mpr ENNReal.toReal_nonneg))
              (integral_nonneg fun y=>hsNormSq_nonneg (Q₀ y))
        filter_upwards [ae_restrict_of_ae_restrict_of_subset hQueryHalf hBound,ae_restrict_mem measurableSet_ball] with x hx hxQ
        have hxU : x∈ball (0:Domain n) 1 := hSmallUnit ((ball_subset_ball (by linarith : r≤8*r)) hxQ)
        simpa only [Q₀,indicator_of_mem hxU] using hx.trans hScale
      · obtain ⟨b,hb,hab⟩ := normalized_boundary_center_of_small_query a r hr hSmall ⟨x₀,hx₀,hx₀U⟩ hContained
        have hQueryHalf : ball a r⊆ball b (16*r) := by
          intro x hx
          have HT := dist_triangle x a b
          have HX : dist x a<r := hx
          change dist x b<16*r
          linarith
        have hOuterBig : ball b (32*r)⊆B := by
          intro x hx
          have HT := dist_triangle x b a
          have HX : dist x b<32*r := hx
          have Hba : dist b a≤8*r := by simpa only [dist_comm] using hab
          change dist x a<256*r
          linarith
        have hBoundaryCap : ball (0:Domain n) 1∩ball b (32*r)⊆ball (0:Domain n) 1∩ball a (256*r) :=
          fun x hx=>⟨hx.1,hOuterBig hx.2⟩
        have hFBoundary : F =ᵐ[volume.restrict (ball (0:Domain n) 1∩ball b (32*r))] (fun _=>(0:Gradient n q)) :=
          ae_restrict_of_ae_restrict_of_subset hBoundaryCap hZero
        have hBound := EffectiveCoulomb.native_neumann_boundary_gradient_le n hn q b hb
          (32*r) (by positivity) (by linarith) f Q F hf hF
          (fun ψ Dψ hψ=>(hNat ψ Dψ hψ).2.2) hFBoundary
        have hHalf : (32*r)/2=16*r := by ring
        change ∀ᵐx∂volume.restrict (ball b ((32*r)/2)),hsNormSq (Q₀ x)≤
          K*(volume.real (ball b ((32*r)/2)))⁻¹*(∫y in ball b (32*r),hsNormSq (Q₀ y)) at hBound
        rw [hHalf] at hBound
        have hEnergyBoundary : (∫y in ball b (32*r),hsNormSq (Q₀ y))≤∫y in B,hsNormSq (Q₀ y) :=
          setIntegral_mono_set hIB (Eventually.of_forall fun y=>hsNormSq_nonneg (Q₀ y))
            (Eventually.of_forall fun y hy=>hOuterBig hy)
        have hVolume : (volume.real (ball b (16*r)))⁻¹=(16:ℝ)^n*(volume.real B)⁻¹ := by
          have H := inverse_ball_volume_dilate a b (s:=16*r) (t:=16) (by positivity) (by norm_num)
          simpa only [show (16:ℝ)*(16*r)=256*r by ring] using H
        have hScale : K*(volume.real (ball b (16*r)))⁻¹*(∫y in ball b (32*r),hsNormSq (Q₀ y))≤M := by
          calc
            _≤K*(volume.real (ball b (16*r)))⁻¹*(∫y in B,hsNormSq (Q₀ y)) :=
              mul_le_mul_of_nonneg_left hEnergyBoundary (mul_nonneg hK.le (inv_nonneg.mpr ENNReal.toReal_nonneg))
            _=(K*(16:ℝ)^n)*(volume.real B)⁻¹*(∫y in B,hsNormSq (Q₀ y)) := by rw [hVolume];ring
            _≤M := mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (le_max_right _ _) (inv_nonneg.mpr ENNReal.toReal_nonneg))
              (integral_nonneg fun y=>hsNormSq_nonneg (Q₀ y))
        exact (ae_restrict_of_ae_restrict_of_subset hQueryHalf hBound).mono (fun x hx=>hx.trans hScale)
  · filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    have hOut : x∉ball (0:Domain n) 1 := fun h=>hMeet ⟨x,hx,h⟩
    have hHS0 : hsNormSq (Q₀ x)=0 := by
      simp only [Q₀,indicator_of_notMem hOut,hsNormSq,norm_zero,zero_pow (by decide : (2:ℕ)≠0),Finset.sum_const_zero]
    rw [hHS0]
    exact hM0

/-- For each dimension at least two, one genuine contractive self-adjoint Neumann L2 operator has the same-response essential off-support bound on every center and positive radius, with a dimension-only constant chosen before the target dimension and all original data. -/
theorem exists_same_neumann_operator_all_ball_offSupport_bounds (n : ℕ) (hn : 2≤n) :
    ∃C : ℝ,0<C ∧ ∀q : ℕ,
      let μ := volume.restrict (ball (0:Domain n) 1)
      let E : Gradient n q → Ambient (n*q) := fun A=>WithLp.toLp 2
        (fun k=>A (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)
      ∃T : Lp (Ambient (n*q)) 2 μ →L[ℝ] Lp (Ambient (n*q)) 2 μ,
        ‖T‖≤1 ∧ IsSelfAdjoint T ∧ (∀Z,T (T Z)=T Z) ∧
        ∀(F : Domain n → Gradient n q) (hF : ∀i,MemLp (fun x=>F x i) 2 μ),
          let A := (memLp_hs_flatten F hF).toLp (fun x=>E (F x))
          let Q := fun (x : Domain n) (i : Fin n)=>WithLp.toLp 2
            (fun j : Fin q=>(T A) x (finProdFinEquiv (i,j)))
          let Q₀ := fun x i=>(ball (0:Domain n) 1).indicator (fun y=>Q y i) x
          ∃f : Domain n → Ambient q,MemW12 (ballDomain (0:Domain n) 1) f Q ∧
            (∫x,hsNormSq (Q x) ∂μ)≤∫x,hsNormSq (F x) ∂μ ∧
            (∀ (ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q),
              MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ →
              Integrable (fun x=>∑i : Fin n,inner ℝ (Q x i) (Dψ x i)) μ ∧
              Integrable (fun x=>∑i : Fin n,inner ℝ (F x i) (Dψ x i)) μ ∧
              (∫x,∑i : Fin n,inner ℝ (Q x i) (Dψ x i) ∂μ)=
                ∫x,∑i : Fin n,inner ℝ (F x i) (Dψ x i) ∂μ) ∧
            HolderToCK.WeakPoissonOn (ballDomain (0:Domain n) 1)
              (fun x i=>Q x i-F x i) (fun _=>(0:Ambient q)) ∧
            (∀i,MemLp (fun x=>Q₀ x i) 2 volume) ∧
            ∀(a : Domain n) (r : ℝ),0<r →
              F =ᵐ[volume.restrict (ball (0:Domain n) 1∩ball a (256*r))] (fun _=>(0:Gradient n q)) →
              ∀ᵐx∂volume.restrict (ball a r),hsNormSq (Q₀ x)≤
                C*(volume.real (ball a (256*r)))⁻¹*(∫y in ball a (256*r),hsNormSq (Q₀ y)) := by
  exact ⟨(effectiveNeumannOffSupportConstant n : ℝ), effectiveNeumannOffSupportConstant_pos n,
    effective_same_neumann_operator_all_ball_offSupport_bounds n hn⟩

end StationaryHarmonicMaps.Analysis

end
