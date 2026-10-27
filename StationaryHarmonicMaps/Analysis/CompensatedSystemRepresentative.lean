module

public import StationaryHarmonicMaps.Analysis.CompensatedCutoffRepresentative
public import StationaryHarmonicMaps.Analysis.AntisymmetricSystemAffine
public import HolderToCK.Analysis.WeakPoissonAffine

/-!
# Scale-correct representatives for an original given-frame system

Positive affine transport preserves the original native map, frame, weak
system and full critical suprema. Actual operator-L2 and gradient-L2 data
supply the original forcing's L1 integrability inside the proof. The
representative covers two thirds of the original ball, so a system on
B(0,3/4) gives the required representative on B(0,1/2).
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology ENNReal ContDiff

namespace StationaryHarmonicMaps.Analysis

private theorem weakPoisson_affineBall_integrable {n q : ℕ}
    {a : Domain n} {r : ℝ} {F : Domain n → Ambient q}
    {Du : Domain n → Gradient n q}
    (hEq : HolderToCK.WeakPoissonOn (ballDomain a r) Du F)
    (hF : IntegrableOn F (Metric.ball a r) volume)
    (b : Domain n) {t : ℝ} (ht : 0 < t) :
    HolderToCK.WeakPoissonOn (ballDomain b (r / t))
      (fun x i => t • Du (a + t • (x - b)) i)
      (fun x => t ^ 2 • F (a + t • (x - b))) := by
  have hF' : IntegrableOn (fun x => t ^ 2 • F (a + t • (x - b)))
      (Metric.ball b (r / t)) volume := by
    change Integrable (t ^ 2 • (fun x => F (a + t • (x - b))))
      (volume.restrict (Metric.ball b (r / t)))
    exact (HolderToCK.integrable_affineBall a b ht r hF).smul (t ^ 2)
  refine ⟨hF'.locallyIntegrableOn, ?_⟩
  intro ψ hψ hcψ hsψ
  let Ψ : Domain n → Ambient q := fun z => ψ (b + t⁻¹ • (z - a))
  have hΨ : ContDiff ℝ ∞ Ψ := hψ.comp (affineBall_contDiff b a t⁻¹)
  have hcΨ : HasCompactSupport Ψ :=
    affineBallTest_hasCompactSupport hcψ b a (inv_ne_zero ht.ne')
  have hratio : r / t / t⁻¹ = r := by field_simp
  have hsΨ : tsupport Ψ ⊆ (ballDomain a r).val := by
    simpa only [hratio, Ψ, ballDomain] using
      affineBallTest_tsupport_subset b a (inv_pos.mpr ht) (r / t) hsψ
  have hder (x : Domain n) (i : Fin n) :
      fderiv ℝ Ψ (a + t • (x - b)) (EuclideanSpace.single i 1) =
        t⁻¹ • fderiv ℝ ψ x (EuclideanSpace.single i 1) := by
    simpa only [coordinateDerivative, Ψ, affineBall_inverse a b ht.ne'] using
      affineBallTest_coordinateDerivative hψ b a t⁻¹ i (a + t • (x - b))
  obtain ⟨hleft, hright, heq⟩ := hEq.2 Ψ hΨ hcΨ hsΨ
  let A : Domain n → ℝ := fun z => ∑ i : Fin n,
    inner ℝ (Du z i) (fderiv ℝ Ψ z (EuclideanSpace.single i 1))
  let B : Domain n → ℝ := fun z => inner ℝ (F z) (Ψ z)
  have hA (x : Domain n) : (∑ i : Fin n,
      inner ℝ (t • Du (a + t • (x - b)) i) (fderiv ℝ ψ x (EuclideanSpace.single i 1))) =
        t ^ 2 * A (a + t • (x - b)) := by
    simp only [A, hder, real_inner_smul_left, real_inner_smul_right, ← Finset.mul_sum]
    field_simp
  have hB (x : Domain n) : inner ℝ (t ^ 2 • F (a + t • (x - b))) (ψ x) =
      t ^ 2 * B (a + t • (x - b)) := by
    simp only [B, Ψ, affineBall_inverse a b ht.ne', real_inner_smul_left]
  have hleft' : IntegrableOn (fun x => ∑ i : Fin n,
      inner ℝ (t • Du (a + t • (x - b)) i) (fderiv ℝ ψ x (EuclideanSpace.single i 1)))
      (Metric.ball b (r / t)) volume :=
    ((HolderToCK.integrable_affineBall a b ht r hleft).const_mul (t ^ 2)).congr
      (Eventually.of_forall fun x => (hA x).symm)
  have hright' : IntegrableOn (fun x => inner ℝ (t ^ 2 • F (a + t • (x - b))) (ψ x))
      (Metric.ball b (r / t)) volume :=
    ((HolderToCK.integrable_affineBall a b ht r hright).const_mul (t ^ 2)).congr
      (Eventually.of_forall fun x => (hB x).symm)
  have hleftEq : (∫ x in Metric.ball b (r / t), ∑ i : Fin n,
      inner ℝ (t • Du (a + t • (x - b)) i) (fderiv ℝ ψ x (EuclideanSpace.single i 1))) =
      t ^ 2 * ((t ^ n)⁻¹ * ∫ z in Metric.ball a r, A z) := by
    calc
      _ = ∫ x in Metric.ball b (r / t), t ^ 2 * A (a + t • (x - b)) :=
        setIntegral_congr_fun measurableSet_ball (fun x _ => hA x)
      _ = t ^ 2 * ∫ x in Metric.ball b (r / t), A (a + t • (x - b)) := integral_const_mul _ _
      _ = _ := by rw [integral_affineBall a b ht r A, smul_eq_mul]
  have hrightEq : (∫ x in Metric.ball b (r / t), inner ℝ (t ^ 2 • F (a + t • (x - b))) (ψ x)) =
      t ^ 2 * ((t ^ n)⁻¹ * ∫ z in Metric.ball a r, B z) := by
    calc
      _ = ∫ x in Metric.ball b (r / t), t ^ 2 * B (a + t • (x - b)) :=
        setIntegral_congr_fun measurableSet_ball (fun x _ => hB x)
      _ = t ^ 2 * ∫ x in Metric.ball b (r / t), B (a + t • (x - b)) := integral_const_mul _ _
      _ = _ := by rw [integral_affineBall a b ht r B, smul_eq_mul]
  refine ⟨hleft', hright', ?_⟩
  dsimp only [ballDomain]
  rw [hleftEq, hrightEq]
  change (∫ z in Metric.ball a r, A z) = -(∫ z in Metric.ball a r, B z) at heq
  rw [heq, mul_neg, mul_neg]


/-- The original system and the same given critical Coulomb frame on an
arbitrary positive ball produce the same-map target-valued representative
on two thirds of that ball, with the exact inverse radius exponent. -/
theorem exists_compact_target_compensated_ball_representative
    (n : ℕ) (hn : 2≤n) (p : ℝ) (hpOne : 1<p) (hpTwo : p<2)
    (hpConj : (n : ℝ)<p/(p-1)) (q : ℕ)
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
  obtain ⟨ε,C,hε,hεOne,hC,H⟩ := exists_compact_target_compensated_representative
    n hn p hpOne hpTwo hpConj q E R hRE hER hE δ hδ hδOne
  refine ⟨ε,C,hε,hεOne,hC,?_⟩
  intro N u Du η a ρ hρ hu hTarget hη hηle hCritical P DP hP hOrth hDPCritical Ω hΩ hEq Z hDiv hZCritical
  let U := fun y=>u (a+ρ • y)
  let DU := fun y i=>ρ • Du (a+ρ • y) i
  let S := fun y=>P (a+ρ • y)
  let DS := fun y i=>ρ • DP (a+ρ • y) i
  let A := fun y i=>ρ • Ω (a+ρ • y) i
  let ZU := fun y i=>star (R (S y))*R (DS y i)+star (R (S y))*A y i*R (S y)
  have hU : MemW12 (ballDomain (0:Domain n) 1) U DU := by
    simpa only [sub_zero,div_self hρ.ne'] using hu.affineBall_pullback (0:Domain n) hρ
  have hS : MemW12 (ballDomain (0:Domain n) 1) S DS := by
    simpa only [sub_zero,div_self hρ.ne'] using hP.affineBall_pullback (0:Domain n) hρ
  have hUN : ∀ᵐy∂volume.restrict (ball (0:Domain n) 1),U y∈N.carrierSet := by
    simpa only [sub_zero,div_self hρ.ne'] using ae_affineBall a (0:Domain n) hρ ρ hTarget
  have hSOrth : ∀ᵐy∂volume.restrict (ball (0:Domain n) 1),star (R (S y))*R (S y)=1 := by
    simpa only [sub_zero,div_self hρ.ne'] using ae_affineBall a (0:Domain n) hρ ρ hOrth
  have hDUCritical : criticalGradientMorreySquare DU (ball (0:Domain n) 1)≤ENNReal.ofReal (η^2) := by
    rw [criticalGradientMorreySquare_unitBall a ⟨ρ,hρ⟩ Du]
    exact hCritical
  have hDSCritical : criticalGradientMorreySquare DS (ball (0:Domain n) 1)≤ENNReal.ofReal (η^2) := by
    rw [criticalGradientMorreySquare_unitBall a ⟨ρ,hρ⟩ DP]
    exact hDPCritical
  have hAL2 (i : Fin n) : MemLp (fun y=>A y i) 2 (volume.restrict (ball (0:Domain n) 1)) := by
    have hEncoded := E.lipschitz.comp_memLp (map_zero E) (hΩ i)
    have hScaled := (memLp_affineBall a (0:Domain n) hρ ρ hEncoded).const_smul ρ
    have H := R.lipschitz.comp_memLp (map_zero R) hScaled
    have H0 : MemLp (fun y=>A y i) 2 (volume.restrict (ball (0:Domain n) (ρ/ρ))) :=
      MemLp.ae_eq (Eventually.of_forall fun y=>by
        change R (ρ • E (Ω (a+ρ • (y-0)) i))=ρ • Ω (a+ρ • y) i
        rw [sub_zero,map_smul,hRE]) H
    simpa only [div_self hρ.ne'] using H0
  have hForcingI : IntegrableOn (fun x=>-(∑i : Fin n,Ω x i (Du x i))) (ball a ρ) volume := by
    apply Integrable.neg
    apply integrable_finsetSum
    intro i _
    have hZi := hΩ i
    have hFi := hu.2.2 i
    have hm := (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      (hZi.aestronglyMeasurable.prodMk hFi.aestronglyMeasurable)
    have hp : MemLp (fun x=>‖Ω x i‖*‖Du x i‖) 1 (volume.restrict (ball a ρ)) :=
      hFi.norm.mul' hZi.norm
    apply (memLp_one_iff_integrable.mp hp).mono' hm
    exact Eventually.of_forall fun x=>(Ω x i).le_opNorm _
  have hUEq : HolderToCK.WeakPoissonOn (ballDomain (0:Domain n) 1) DU
      (fun y=>-(∑i : Fin n,A y i (DU y i))) := by
    have H := weakPoisson_affineBall_integrable hEq hForcingI (0:Domain n) hρ
    simp only [sub_zero,div_self hρ.ne'] at H
    exact H.congr (EventuallyEq.refl _ _)
      (Eventually.of_forall fun y=>system_forcing_smul ρ (Ω (a+ρ • y)) (Du (a+ρ • y)))
  have hZU (y : Domain n) (i : Fin n) : ZU y i=ρ • Z (a+ρ • y) i := by
    ext z
    simp only [ZU,S,DS,A,Z,map_smul,mul_apply_eq_comp,smul_apply,add_apply,smul_add]
  have hZUEq : HolderToCK.WeakPoissonOn (ballDomain (0:Domain n) 1)
      (fun y i=>E (ZU y i)) (fun _=>0) := by
    have H := weakPoisson_affineBall_integrable hDiv (integrable_zero _ _ _) (0:Domain n) hρ
    simp only [sub_zero,div_self hρ.ne',smul_zero] at H
    exact H.congr (Eventually.of_forall fun y=>by
        funext i
        change ρ • E (Z (a+ρ • y) i)=E (ZU y i)
        rw [hZU,map_smul]) (EventuallyEq.refl _ _)
  have hZUCritical : criticalGradientMorreySquare (fun y i=>E (ZU y i)) (ball (0:Domain n) 1)≤
      ENNReal.ofReal (η^2) := by
    have hField : (fun y i=>E (ZU y i))=(fun y i=>ρ • E (Z (a+ρ • y) i)) := by
      funext y i
      rw [hZU,map_smul]
    rw [hField,criticalGradientMorreySquare_unitBall a ⟨ρ,hρ⟩ (fun x i=>E (Z x i))]
    exact hZCritical
  obtain ⟨V,hV,hVN,hVH,_hVU⟩ := H N U DU η hU hUN hη hηle hDUCritical S DS hS hSOrth
    hDSCritical A hAL2 hUEq hZUEq hZUCritical
  have hRatio : (2/3:ℝ)/ρ⁻¹=(2/3:ℝ)*ρ := by rw [div_inv_eq_mul]
  have hImage (x : ball a ((2/3:ℝ)*ρ)) : ρ⁻¹ • ((x:Domain n)-a)∈ball (0:Domain n) (2/3:ℝ) := by
    have hx : (x:Domain n)∈ball a ((2/3:ℝ)/ρ⁻¹) := by rw [hRatio];exact x.property
    have H := (affineBall_mem_ball_iff (0:Domain n) a (inv_pos.mpr hρ) (2/3:ℝ) x).mpr hx
    simpa only [zero_add] using H
  let i : ball a ((2/3:ℝ)*ρ) → ball (0:Domain n) (2/3:ℝ) :=
    fun x=>⟨ρ⁻¹ • ((x:Domain n)-a),hImage x⟩
  have hi : Continuous i := by
    apply Continuous.subtype_mk
    exact (continuous_subtype_val.sub continuous_const).const_smul ρ⁻¹
  let w := fun x=>V (i x)
  have hwCont : Continuous w := hV.1.comp hi
  have hBackAE := ae_affineBall (0:Domain n) a (inv_pos.mpr hρ) (2/3:ℝ) hV.2
  rw [hRatio] at hBackAE
  have hwAE : ∀ᵐx∂volume.restrict (ball a ((2/3:ℝ)*ρ)),
      ∀hx : x∈ball a ((2/3:ℝ)*ρ),w ⟨x,hx⟩=u x := by
    filter_upwards [hBackAE] with x hx
    intro hxBall
    have hM : (0:Domain n)+ρ⁻¹ • (x-a)∈ball (0:Domain n) (2/3:ℝ) := by
      rw [zero_add]
      exact hImage ⟨x,hxBall⟩
    have H := hx hM
    have hInverse : a+ρ • (ρ⁻¹ • (x-a))=x := by
      rw [smul_smul,mul_inv_cancel₀ hρ.ne',one_smul,add_sub_cancel]
    let y0 : ball (0:Domain n) (2/3:ℝ) := ⟨(0:Domain n)+ρ⁻¹ • (x-a),hM⟩
    have hy0 : i ⟨x,hxBall⟩=y0 := Subtype.ext (zero_add _).symm
    calc
      w ⟨x,hxBall⟩=V y0 := congrArg V hy0
      _=U ((0:Domain n)+ρ⁻¹ • (x-a)) := H
      _=u x := by
        change u (a+ρ • ((0:Domain n)+ρ⁻¹ • (x-a)))=u x
        rw [zero_add,hInverse]
  have hw : IsContinuousRepresentative (ballDomain a ((2/3:ℝ)*ρ)) u w := ⟨hwCont,hwAE⟩
  refine ⟨w,hw,fun x=>hVN (i x),?_,?_⟩
  · intro x y
    have hDist : dist (i x:Domain n) (i y:Domain n)=ρ⁻¹*dist (x:Domain n) (y:Domain n) := by
      change dist (ρ⁻¹ • ((x:Domain n)-a)) (ρ⁻¹ • ((y:Domain n)-a))=_
      rw [dist_eq_norm,←smul_sub,sub_sub_sub_cancel_right,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hρ.le),dist_eq_norm]
    exact (hVH (i x) (i y)).trans_eq (by
      rw [hDist,Real.mul_rpow (inv_nonneg.mpr hρ.le) dist_nonneg,Real.inv_rpow hρ.le,←Real.rpow_neg hρ.le]
      ring)
  · intro W hW
    exact hW.unique hw


theorem exists_compact_target_compensated_ball_representative_effective
    (n : ℕ) (hn : 2≤n) (q : ℕ)
    (E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient (q*q))
    (R : Ambient (q*q) →L[ℝ] (Ambient q →L[ℝ] Ambient q))
    (hRE : ∀T,R (E T)=T) (hER : ∀z,E (R z)=z)
    (hE : ∀T : Ambient q →L[ℝ] Ambient q,‖E T‖^2=∑j : Fin q,‖T (EuclideanSpace.single j 1)‖^2)
    :
    ∃ε C : ℝ,0<ε ∧ ε≤1 ∧ 0<C ∧
      ε=(effectiveGivenFrameSmallness n q : ℝ) ∧
      C=(effectiveGivenFrameHolderConstant n q : ℝ) ∧ ∀(N : CompactC2EmbeddedTarget q)
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
              (∀x y,‖w x-w y‖≤C*η*ρ^(-(1/2 : ℝ))*(dist (x:Domain n) (y:Domain n))^(1/2 : ℝ)) ∧
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
  have hValue : p/(p-1)=2*(n:ℝ)+1 := by
    dsimp only [p]
    field_simp
    ring
  have hpConj : (n:ℝ)<p/(p-1) := by rw [hValue];linarith only [hnReal]
  have hConjugate : p/(p-1)=((2*n+1 : ℕ) : ℝ) := by
    simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] using hValue
  obtain ⟨ε,C,hε,hεOne,hC,hεF,hCF,H⟩ := exists_compact_target_compensated_representative_effective
    n hn p hpOne hpTwo hpConj q E R hRE hER hE hConjugate
  refine ⟨ε,C,hε,hεOne,hC,hεF,hCF,?_⟩
  intro N u Du η a ρ hρ hu hTarget hη hηle hCritical P DP hP hOrth hDPCritical Ω hΩ hEq Z hDiv hZCritical
  let U := fun y=>u (a+ρ • y)
  let DU := fun y i=>ρ • Du (a+ρ • y) i
  let S := fun y=>P (a+ρ • y)
  let DS := fun y i=>ρ • DP (a+ρ • y) i
  let A := fun y i=>ρ • Ω (a+ρ • y) i
  let ZU := fun y i=>star (R (S y))*R (DS y i)+star (R (S y))*A y i*R (S y)
  have hU : MemW12 (ballDomain (0:Domain n) 1) U DU := by
    simpa only [sub_zero,div_self hρ.ne'] using hu.affineBall_pullback (0:Domain n) hρ
  have hS : MemW12 (ballDomain (0:Domain n) 1) S DS := by
    simpa only [sub_zero,div_self hρ.ne'] using hP.affineBall_pullback (0:Domain n) hρ
  have hUN : ∀ᵐy∂volume.restrict (ball (0:Domain n) 1),U y∈N.carrierSet := by
    simpa only [sub_zero,div_self hρ.ne'] using ae_affineBall a (0:Domain n) hρ ρ hTarget
  have hSOrth : ∀ᵐy∂volume.restrict (ball (0:Domain n) 1),star (R (S y))*R (S y)=1 := by
    simpa only [sub_zero,div_self hρ.ne'] using ae_affineBall a (0:Domain n) hρ ρ hOrth
  have hDUCritical : criticalGradientMorreySquare DU (ball (0:Domain n) 1)≤ENNReal.ofReal (η^2) := by
    rw [criticalGradientMorreySquare_unitBall a ⟨ρ,hρ⟩ Du]
    exact hCritical
  have hDSCritical : criticalGradientMorreySquare DS (ball (0:Domain n) 1)≤ENNReal.ofReal (η^2) := by
    rw [criticalGradientMorreySquare_unitBall a ⟨ρ,hρ⟩ DP]
    exact hDPCritical
  have hAL2 (i : Fin n) : MemLp (fun y=>A y i) 2 (volume.restrict (ball (0:Domain n) 1)) := by
    have hEncoded := E.lipschitz.comp_memLp (map_zero E) (hΩ i)
    have hScaled := (memLp_affineBall a (0:Domain n) hρ ρ hEncoded).const_smul ρ
    have H := R.lipschitz.comp_memLp (map_zero R) hScaled
    have H0 : MemLp (fun y=>A y i) 2 (volume.restrict (ball (0:Domain n) (ρ/ρ))) :=
      MemLp.ae_eq (Eventually.of_forall fun y=>by
        change R (ρ • E (Ω (a+ρ • (y-0)) i))=ρ • Ω (a+ρ • y) i
        rw [sub_zero,map_smul,hRE]) H
    simpa only [div_self hρ.ne'] using H0
  have hForcingI : IntegrableOn (fun x=>-(∑i : Fin n,Ω x i (Du x i))) (ball a ρ) volume := by
    apply Integrable.neg
    apply integrable_finsetSum
    intro i _
    have hZi := hΩ i
    have hFi := hu.2.2 i
    have hm := (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      (hZi.aestronglyMeasurable.prodMk hFi.aestronglyMeasurable)
    have hp : MemLp (fun x=>‖Ω x i‖*‖Du x i‖) 1 (volume.restrict (ball a ρ)) :=
      hFi.norm.mul' hZi.norm
    apply (memLp_one_iff_integrable.mp hp).mono' hm
    exact Eventually.of_forall fun x=>(Ω x i).le_opNorm _
  have hUEq : HolderToCK.WeakPoissonOn (ballDomain (0:Domain n) 1) DU
      (fun y=>-(∑i : Fin n,A y i (DU y i))) := by
    have H := weakPoisson_affineBall_integrable hEq hForcingI (0:Domain n) hρ
    simp only [sub_zero,div_self hρ.ne'] at H
    exact H.congr (EventuallyEq.refl _ _)
      (Eventually.of_forall fun y=>system_forcing_smul ρ (Ω (a+ρ • y)) (Du (a+ρ • y)))
  have hZU (y : Domain n) (i : Fin n) : ZU y i=ρ • Z (a+ρ • y) i := by
    ext z
    simp only [ZU,S,DS,A,Z,map_smul,mul_apply_eq_comp,smul_apply,add_apply,smul_add]
  have hZUEq : HolderToCK.WeakPoissonOn (ballDomain (0:Domain n) 1)
      (fun y i=>E (ZU y i)) (fun _=>0) := by
    have H := weakPoisson_affineBall_integrable hDiv (integrable_zero _ _ _) (0:Domain n) hρ
    simp only [sub_zero,div_self hρ.ne',smul_zero] at H
    exact H.congr (Eventually.of_forall fun y=>by
        funext i
        change ρ • E (Z (a+ρ • y) i)=E (ZU y i)
        rw [hZU,map_smul]) (EventuallyEq.refl _ _)
  have hZUCritical : criticalGradientMorreySquare (fun y i=>E (ZU y i)) (ball (0:Domain n) 1)≤
      ENNReal.ofReal (η^2) := by
    have hField : (fun y i=>E (ZU y i))=(fun y i=>ρ • E (Z (a+ρ • y) i)) := by
      funext y i
      rw [hZU,map_smul]
    rw [hField,criticalGradientMorreySquare_unitBall a ⟨ρ,hρ⟩ (fun x i=>E (Z x i))]
    exact hZCritical
  obtain ⟨V,hV,hVN,hVH,_hVU⟩ := H N U DU η hU hUN hη hηle hDUCritical S DS hS hSOrth
    hDSCritical A hAL2 hUEq hZUEq hZUCritical
  have hRatio : (2/3:ℝ)/ρ⁻¹=(2/3:ℝ)*ρ := by rw [div_inv_eq_mul]
  have hImage (x : ball a ((2/3:ℝ)*ρ)) : ρ⁻¹ • ((x:Domain n)-a)∈ball (0:Domain n) (2/3:ℝ) := by
    have hx : (x:Domain n)∈ball a ((2/3:ℝ)/ρ⁻¹) := by rw [hRatio];exact x.property
    have H := (affineBall_mem_ball_iff (0:Domain n) a (inv_pos.mpr hρ) (2/3:ℝ) x).mpr hx
    simpa only [zero_add] using H
  let i : ball a ((2/3:ℝ)*ρ) → ball (0:Domain n) (2/3:ℝ) :=
    fun x=>⟨ρ⁻¹ • ((x:Domain n)-a),hImage x⟩
  have hi : Continuous i := by
    apply Continuous.subtype_mk
    exact (continuous_subtype_val.sub continuous_const).const_smul ρ⁻¹
  let w := fun x=>V (i x)
  have hwCont : Continuous w := hV.1.comp hi
  have hBackAE := ae_affineBall (0:Domain n) a (inv_pos.mpr hρ) (2/3:ℝ) hV.2
  rw [hRatio] at hBackAE
  have hwAE : ∀ᵐx∂volume.restrict (ball a ((2/3:ℝ)*ρ)),
      ∀hx : x∈ball a ((2/3:ℝ)*ρ),w ⟨x,hx⟩=u x := by
    filter_upwards [hBackAE] with x hx
    intro hxBall
    have hM : (0:Domain n)+ρ⁻¹ • (x-a)∈ball (0:Domain n) (2/3:ℝ) := by
      rw [zero_add]
      exact hImage ⟨x,hxBall⟩
    have H := hx hM
    have hInverse : a+ρ • (ρ⁻¹ • (x-a))=x := by
      rw [smul_smul,mul_inv_cancel₀ hρ.ne',one_smul,add_sub_cancel]
    let y0 : ball (0:Domain n) (2/3:ℝ) := ⟨(0:Domain n)+ρ⁻¹ • (x-a),hM⟩
    have hy0 : i ⟨x,hxBall⟩=y0 := Subtype.ext (zero_add _).symm
    calc
      w ⟨x,hxBall⟩=V y0 := congrArg V hy0
      _=U ((0:Domain n)+ρ⁻¹ • (x-a)) := H
      _=u x := by
        change u (a+ρ • ((0:Domain n)+ρ⁻¹ • (x-a)))=u x
        rw [zero_add,hInverse]
  have hw : IsContinuousRepresentative (ballDomain a ((2/3:ℝ)*ρ)) u w := ⟨hwCont,hwAE⟩
  refine ⟨w,hw,fun x=>hVN (i x),?_,?_⟩
  · intro x y
    have hDist : dist (i x:Domain n) (i y:Domain n)=ρ⁻¹*dist (x:Domain n) (y:Domain n) := by
      change dist (ρ⁻¹ • ((x:Domain n)-a)) (ρ⁻¹ • ((y:Domain n)-a))=_
      rw [dist_eq_norm,←smul_sub,sub_sub_sub_cancel_right,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hρ.le),dist_eq_norm]
    exact (hVH (i x) (i y)).trans_eq (by
      rw [hDist,Real.mul_rpow (inv_nonneg.mpr hρ.le) dist_nonneg,Real.inv_rpow hρ.le,←Real.rpow_neg hρ.le]
      ring)
  · intro W hW
    exact hW.unique hw


/-- A genuine original system on B(0,3/4), together with its same given
small critical Coulomb frame, gives the unique target-valued Holder
representative on B(0,1/2). The auxiliary low exponent and cutoff are
chosen internally before all original data. -/
theorem exists_compact_target_given_frame_halfBall_representative
    (n : ℕ) (hn : 2≤n) (q : ℕ)
    (E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient (q*q))
    (R : Ambient (q*q) →L[ℝ] (Ambient q →L[ℝ] Ambient q))
    (hRE : ∀T,R (E T)=T) (hER : ∀z,E (R z)=z)
    (hE : ∀T : Ambient q →L[ℝ] Ambient q,‖E T‖^2=∑j : Fin q,‖T (EuclideanSpace.single j 1)‖^2)
    (δ : ℝ) (hδ : 0<δ) (hδOne : δ<1) :
    ∃ε C : ℝ,0<ε ∧ ε≤1 ∧ 0<C ∧ ∀(N : CompactC2EmbeddedTarget q)
      (u : Domain n → Ambient q) (Du : Domain n → Gradient n q) (η : ℝ),
      MemW12 (ballDomain (0:Domain n) (3/4:ℝ)) u Du →
      (∀ᵐx∂volume.restrict (ball (0:Domain n) (3/4:ℝ)),u x∈N.carrierSet) → 0≤η → η≤ε →
      criticalGradientMorreySquare Du (ball (0:Domain n) (3/4:ℝ))≤ENNReal.ofReal (η^2) →
      ∀(P : Domain n → Ambient (q*q)) (DP : Domain n → Gradient n (q*q)),
        MemW12 (ballDomain (0:Domain n) (3/4:ℝ)) P DP →
        (∀ᵐx∂volume.restrict (ball (0:Domain n) (3/4:ℝ)),star (R (P x))*R (P x)=1) →
        criticalGradientMorreySquare DP (ball (0:Domain n) (3/4:ℝ))≤ENNReal.ofReal (η^2) →
        ∀Ω : Domain n → Fin n → (Ambient q →L[ℝ] Ambient q),
          (∀i,MemLp (fun x=>Ω x i) 2 (volume.restrict (ball (0:Domain n) (3/4:ℝ)))) →
          HolderToCK.WeakPoissonOn (ballDomain (0:Domain n) (3/4:ℝ)) Du (fun x=>-(∑i : Fin n,Ω x i (Du x i))) →
          let Z := fun x i=>star (R (P x))*R (DP x i)+star (R (P x))*Ω x i*R (P x)
          HolderToCK.WeakPoissonOn (ballDomain (0:Domain n) (3/4:ℝ)) (fun x i=>E (Z x i)) (fun _=>0) →
          criticalGradientMorreySquare (fun x i=>E (Z x i)) (ball (0:Domain n) (3/4:ℝ))≤ENNReal.ofReal (η^2) →
            ∃w : ball (0:Domain n) (1/2:ℝ) → Ambient q,
              IsContinuousRepresentative (ballDomain (0:Domain n) (1/2:ℝ)) u w ∧
              (∀x,w x∈N.carrierSet) ∧
              (∀x y,‖w x-w y‖≤C*η*(dist (x:Domain n) (y:Domain n))^(1-δ)) ∧
              ∀W : ball (0:Domain n) (1/2:ℝ) → Ambient q,
                IsContinuousRepresentative (ballDomain (0:Domain n) (1/2:ℝ)) u W → W=w := by
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
  obtain ⟨ε,C0,hε,hεOne,hC0,H⟩ := exists_compact_target_compensated_ball_representative
    n hn p hpOne hpTwo hpConj q E R hRE hER hE δ hδ hδOne
  let C := C0*(3/4:ℝ)^(-(1-δ))
  have hC : 0<C := mul_pos hC0 (Real.rpow_pos_of_pos (by norm_num) _)
  refine ⟨ε,C,hε,hεOne,hC,?_⟩
  intro N u Du η hu hTarget hη hηle hCritical P DP hP hOrth hDPCritical Ω hΩ hEq Z hDiv hZCritical
  have H0 := H N u Du η (0:Domain n) (3/4:ℝ) (by norm_num) hu hTarget hη hηle hCritical
    P DP hP hOrth hDPCritical Ω hΩ hEq hDiv hZCritical
  have hRadius : (2/3:ℝ)*(3/4:ℝ)=1/2 := by norm_num
  have H1 : ∃w : ball (0:Domain n) (1/2:ℝ) → Ambient q,
      IsContinuousRepresentative (ballDomain (0:Domain n) (1/2:ℝ)) u w ∧
      (∀x,w x∈N.carrierSet) ∧
      (∀x y,‖w x-w y‖≤C0*η*(3/4:ℝ)^(-(1-δ))*(dist (x:Domain n) (y:Domain n))^(1-δ)) ∧
      ∀W : ball (0:Domain n) (1/2:ℝ) → Ambient q,
        IsContinuousRepresentative (ballDomain (0:Domain n) (1/2:ℝ)) u W → W=w := by
    rw [hRadius] at H0
    exact H0
  obtain ⟨w,hw,hwN,hwHolder,hwUnique⟩ := H1
  refine ⟨w,hw,hwN,?_,hwUnique⟩
  intro x y
  exact (hwHolder x y).trans_eq (by dsimp only [C];ring)


end StationaryHarmonicMaps.Analysis

end
