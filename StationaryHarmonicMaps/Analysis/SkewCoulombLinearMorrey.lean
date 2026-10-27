/- Copyright (c) 2026. All rights reserved. -/
module

public import StationaryHarmonicMaps.Analysis.CoexactOperatorLpMorrey
public import StationaryHarmonicMaps.Geometry.OrthogonalRightHS
public import StationaryHarmonicMaps.Geometry.GaugedEnergyAlgebra
public import StationaryHarmonicMaps.Analysis.SkewRelativeCoexactProjection

/-!
# The skew linear relative response of the original transformed connection

One response of the original transformed connection retains every
subdimensional power-growth estimate. The coefficient skew projection acts
on its primitive, tensor and response together, so the original gradient
complement and unrestricted native boundary identities remain valid.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

private theorem native_linear_image {n q k : ℕ} {Ω : OpenDomain n}
    (f : Domain n → Ambient q) (Df : Domain n → Gradient n q) (hf : MemW12 Ω f Df)
    (L : Ambient q →L[ℝ] Ambient k) :
    MemW12 Ω (fun x=>L (f x)) (fun x i=>L (Df x i)) :=
  ⟨(memW12Loc_continuousLinearMap hf.to_memW12Loc L).1,
    L.lipschitz.comp_memLp (map_zero L) hf.2.1,
    fun i=>L.lipschitz.comp_memLp (map_zero L) (hf.2.2 i)⟩

/-- The same original skew transformed connection has a native skew relative
response with every power-growth bound inherited from the original A. -/
theorem exists_skew_coulomb_linear_relative_power_growth (n : ℕ) (hn : 2≤n) :
    ∃ L : {ν : ℝ //0≤ν ∧ ν<(n:ℝ)} → ℝ,
      (∀ν,0<L ν) ∧ ∀(q : ℕ)
      (E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient (q*q))
      (R : Ambient (q*q) →L[ℝ] (Ambient q →L[ℝ] Ambient q)),
      (∀T,R (E T)=T) → (∀z,E (R z)=z) →
      (∀T : Ambient q →L[ℝ] Ambient q,‖E T‖^2=∑j : Fin q,‖T (EuclideanSpace.single j 1)‖^2) →
      ∀(p : Domain n → Ambient (q*q)) (Dp : Domain n → Gradient n (q*q))
        (A : Domain n → Fin n → (Ambient q →L[ℝ] Ambient q)),
        MemW12 (ballDomain (0 : Domain n) 1) p Dp →
        (∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),star (R (p x))*R (p x)=1) →
        (∀i,MemLp (fun x=>A x i) 2 (volume.restrict (ball (0 : Domain n) 1))) →
        (∀i,∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),star (A x i)= -A x i) →
        let G := fun x i=>E (star (R (p x))*A x i*R (p x))
        let μ := volume.restrict (ball (0 : Domain n) 1)
        ∃(u : Domain n → Ambient (q*q))
          (c : Fin n → Fin n → Domain n → Ambient (q*q))
          (Dc : Fin n → Fin n → Domain n → Gradient n (q*q))
          (Q : Domain n → Gradient n (q*q)),
          MemW12 (ballDomain (0 : Domain n) 1) u (fun x i=>G x i-Q x i) ∧
          (∀x,star (R (u x))= -R (u x)) ∧
          (∀i j,MemW12 (ballDomain (0 : Domain n) 1) (c i j) (Dc i j)) ∧
          (∀i j x,star (R (c i j x))= -R (c i j x)) ∧
          (∀i j x k,star (R (Dc i j x k))= -R (Dc i j x k)) ∧
          (∀x i,star (R (Q x i))= -R (Q x i)) ∧
          (∀i,MemLp (fun x=>Q x i) 2 μ) ∧
          (∀ᵐx∂μ,∀i j,c i j x= -c j i x) ∧
          (∀ᵐx∂μ,∀i j k,Dc i j x k+Dc j k x i+Dc k i x j=0) ∧
          (∀ᵐx∂μ,∀j,(∑i : Fin n,Dc i j x i)=Q x j) ∧
          (∀(j : Fin n) (ψ : Domain n → Ambient (q*q)) (Dψ : Domain n → Gradient n (q*q)),
            MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ →
            Integrable (fun x=>∑i : Fin n,inner ℝ (c i j x) (Dψ x i)) μ ∧
            Integrable (fun x=>inner ℝ (Q x j) (ψ x)) μ ∧
            (∫x,∑i : Fin n,inner ℝ (c i j x) (Dψ x i) ∂μ)=-(∫x,inner ℝ (Q x j) (ψ x) ∂μ)) ∧
          (∀(ψ : Domain n → Ambient (q*q)) (Dψ : Domain n → Gradient n (q*q)),
            MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ →
            Integrable (fun x=>∑i : Fin n,inner ℝ (Q x i) (Dψ x i)) μ ∧
            (∫x,∑i : Fin n,inner ℝ (Q x i) (Dψ x i) ∂μ)=0) ∧
          ∀(ν : {ν : ℝ //0≤ν ∧ ν<(n:ℝ)}) (K : ℝ),0≤K →
            (∀a : Domain n,a∈ball (0 : Domain n) 1 → ∀r : ℝ,0<r →
              (∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (fun i=>E (A x i)))≤K*r^ν.val) →
            ∀a : Domain n,a∈ball (0 : Domain n) 1 → ∀r : ℝ,0<r →
              (∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (Q x))≤L ν*K*r^ν.val := by
  obtain ⟨_Cp,Cm,_hCp,hCm,HT⟩ := exists_same_coexact_operator_all_lp_and_power_growth_unitBall n hn
  refine ⟨Cm,hCm,?_⟩
  intro q E R hRE hER hE p Dp A hp hOrth hA hAskew G μ
  obtain ⟨S,_hFormula,hTarget,hSelf,hNorm,hFix⟩ :=
    exists_full_coefficient_skew_projection E R hRE hER hE
  have hP := R.continuous.comp_aestronglyMeasurable hp.2.1.aestronglyMeasurable
  have hGNorm (i : Fin n) : ∀ᵐx∂μ,‖G x i‖=‖E (A x i)‖ := by
    filter_upwards [hOrth] with x hx
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    have hStar : star (star (R (p x)))*star (R (p x))=1 := by
      rw [star_star]
      exact mul_star_eq_one_of_star_mul_eq_one _ hx
    change ‖E (star (R (p x))*A x i*R (p x))‖^2=‖E (A x i)‖^2
    rw [encoded_norm_sq_mul_right_orthogonal E hE _ _ hx,
      encoded_norm_sq_mul_left_orthogonal E hE _ _ hStar]
  have hGLp (i : Fin n) : MemLp (fun x=>G x i) 2 μ := by
    have hEA := E.lipschitz.comp_memLp (map_zero E) (hA i)
    have hGM : AEStronglyMeasurable (fun x=>G x i) μ :=
      E.continuous.comp_aestronglyMeasurable ((((ContinuousLinearMap.adjoint (𝕜:=ℝ) (E:=Ambient q) (F:=Ambient q)).continuous.comp_aestronglyMeasurable hP).mul (hA i).aestronglyMeasurable).mul hP)
    exact hEA.of_le hGM ((hGNorm i).mono fun x hx=>hx.le)
  have hGHS : (fun x=>hsNormSq (G x))=ᵐ[μ](fun x=>hsNormSq (fun i=>E (A x i))) := by
    filter_upwards [ae_all_iff.mpr hGNorm] with x hx
    simp only [hsNormSq,hx]
  have hSG : ∀ᵐx∂μ,∀i,S (G x i)=G x i := by
    filter_upwards [ae_all_iff.mpr hAskew] with x hx i
    apply hFix
    rw [hRE]
    simp only [star_mul,star_star,hx]
    ext z
    simp only [mul_apply_eq_comp,neg_apply,map_neg]
  let enc : Gradient n (q*q) → Ambient (n*(q*q)) := fun H=>WithLp.toLp 2
    (fun k=>H (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)
  let dec := fun (W : Domain n → Ambient (n*(q*q))) x i=>WithLp.toLp 2
    (fun j : Fin (q*q)=>W x (finProdFinEquiv (i,j)))
  let W := (memLp_hs_flatten G hGLp).toLp (fun x=>enc (G x))
  have hDecode : dec W=ᵐ[μ]G := by
    filter_upwards [(memLp_hs_flatten G hGLp).coeFn_toLp] with x hx
    change (fun i=>WithLp.toLp 2 (fun j : Fin (q*q)=>W x (finProdFinEquiv (i,j))))=G x
    rw [hx]
    exact hs_unflatten_flatten (G x)
  obtain ⟨T,_hT,_hSelf,_hIdem,Hresponse⟩ := HT (q*q)
  obtain ⟨u,c,Dc,hu,hc,hSkew,hClosed,hDiv,hNormal,hNatural,_hH1,_hEnergy,_hCore,_hLp,hM⟩ := Hresponse W
  let Q := dec (T W)
  let v := fun x=>S (u x)
  let d := fun i j x=>S (c i j x)
  let Dd := fun i j x k=>S (Dc i j x k)
  let P := fun x i=>S (Q x i)
  have huG : MemW12 (ballDomain (0 : Domain n) 1) v (fun x i=>G x i-P x i) := by
    apply (native_linear_image u _ hu S).congr_ae (Eventually.of_forall fun _=>rfl)
    filter_upwards [hDecode,hSG] with x hx hSx
    funext i
    change S (dec W x i-Q x i)=G x i-S (Q x i)
    rw [map_sub,hx,hSx]
  have hd (i j : Fin n) : MemW12 (ballDomain (0 : Domain n) 1) (d i j) (Dd i j) :=
    native_linear_image (c i j) (Dc i j) (hc i j) S
  have hQ (i : Fin n) : MemLp (fun x=>Q x i) 2 μ :=
    memLp_hs_unflatten (T W) (Lp.memLp (T W)) i
  have hP (i : Fin n) : MemLp (fun x=>P x i) 2 μ :=
    S.lipschitz.comp_memLp (map_zero S) (hQ i)
  have hdS : ∀ᵐx∂μ,∀i j,d i j x= -d j i x := by
    filter_upwards [hSkew] with x hx i j
    change S (c i j x)= -S (c j i x)
    rw [hx,map_neg]
  have hdC : ∀ᵐx∂μ,∀i j k,Dd i j x k+Dd j k x i+Dd k i x j=0 := by
    filter_upwards [hClosed] with x hx i j k
    change S (Dc i j x k)+S (Dc j k x i)+S (Dc k i x j)=0
    rw [←map_add,←map_add,hx,map_zero]
  have hdD : ∀ᵐx∂μ,∀j,(∑i : Fin n,Dd i j x i)=P x j := by
    filter_upwards [hDiv] with x hx j
    change (∑i : Fin n,S (Dc i j x i))=S (Q x j)
    rw [←map_sum,hx]
  have hdN (j : Fin n) (ψ : Domain n → Ambient (q*q)) (Dψ : Domain n → Gradient n (q*q))
      (hψ : MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ) :
      Integrable (fun x=>∑i : Fin n,inner ℝ (d i j x) (Dψ x i)) μ ∧
      Integrable (fun x=>inner ℝ (P x j) (ψ x)) μ ∧
      (∫x,∑i : Fin n,inner ℝ (d i j x) (Dψ x i) ∂μ)=-(∫x,inner ℝ (P x j) (ψ x) ∂μ) := by
    obtain ⟨hI,hJ,hEq⟩ := hNormal j (fun x=>S (ψ x)) (fun x i=>S (Dψ x i))
      (native_linear_image ψ Dψ hψ S)
    have hLeft : (fun x=>∑i : Fin n,inner ℝ (c i j x) (S (Dψ x i))) =
        (fun x=>∑i : Fin n,inner ℝ (d i j x) (Dψ x i)) :=
      funext fun x=>Finset.sum_congr rfl (fun i _=>(hSelf _ _).symm)
    have hRight : (fun x=>inner ℝ (Q x j) (S (ψ x))) =
        (fun x=>inner ℝ (P x j) (ψ x)) := funext fun x=>(hSelf _ _).symm
    exact ⟨hI.congr (Eventually.of_forall (congrFun hLeft)),
      hJ.congr (Eventually.of_forall (congrFun hRight)),
      (integral_congr_ae (Eventually.of_forall (congrFun hLeft))).symm.trans
        (hEq.trans (congrArg Neg.neg (integral_congr_ae
          (Eventually.of_forall (congrFun hRight)))))⟩
  have hPN (ψ : Domain n → Ambient (q*q)) (Dψ : Domain n → Gradient n (q*q))
      (hψ : MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ) :
      Integrable (fun x=>∑i : Fin n,inner ℝ (P x i) (Dψ x i)) μ ∧
      (∫x,∑i : Fin n,inner ℝ (P x i) (Dψ x i) ∂μ)=0 := by
    obtain ⟨hI,hEq⟩ := hNatural (fun x=>S (ψ x)) (fun x i=>S (Dψ x i))
      (native_linear_image ψ Dψ hψ S)
    have hLeft : (fun x=>∑i : Fin n,inner ℝ (Q x i) (S (Dψ x i))) =
        (fun x=>∑i : Fin n,inner ℝ (P x i) (Dψ x i)) :=
      funext fun x=>Finset.sum_congr rfl (fun i _=>(hSelf _ _).symm)
    exact ⟨hI.congr (Eventually.of_forall (congrFun hLeft)),
      (integral_congr_ae (Eventually.of_forall (congrFun hLeft))).symm.trans hEq⟩
  refine ⟨v,d,Dd,P,huG,(fun x=>hTarget _),hd,(fun i j x=>hTarget _),
    (fun i j x k=>hTarget _),(fun x i=>hTarget _),hP,hdS,hdC,hdD,hdN,hPN,?_⟩
  intro ν K hK hGrowth a ha r hr
  have hDecodedHS : (fun x=>hsNormSq (dec W x))=ᵐ[μ](fun x=>hsNormSq (G x)) :=
    hDecode.mono fun x hx=>congrArg hsNormSq hx
  have hForcing : ∀a : Domain n,a∈ball (0 : Domain n) 1 → ∀r : ℝ,0<r →
      (∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (dec W x))≤K*r^ν.val := by
    intro a ha r hr
    rw [integral_congr_ae ((hDecodedHS.trans hGHS).filter_mono
      (ae_mono (Measure.restrict_mono_set volume inter_subset_right)))]
    exact hGrowth a ha r hr
  have hPQ (x : Domain n) : hsNormSq (P x)≤hsNormSq (Q x) :=
    Finset.sum_le_sum fun i _=>pow_le_pow_left₀ (norm_nonneg _) (hNorm _) 2
  have hPIB : IntegrableOn (fun x=>hsNormSq (P x)) (ball (0 : Domain n) 1) volume :=
    integrable_hsNormSq_of_columns P hP
  have hQIB : IntegrableOn (fun x=>hsNormSq (Q x)) (ball (0 : Domain n) 1) volume :=
    integrable_hsNormSq_of_columns Q hQ
  have hPI := hPIB.mono_set (inter_subset_right (s:=ball a r))
  have hQI := hQIB.mono_set (inter_subset_right (s:=ball a r))
  exact (integral_mono hPI hQI hPQ).trans (hM ν K hK hForcing a ha r hr)

/-- The same original skew transformed connection has a native skew relative
response with every power-growth bound inherited from the original A. -/
theorem effective_skew_coulomb_linear_relative_power_growth (n : ℕ) (hn : 2≤n) :
    ∀(q : ℕ)
      (E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient (q*q))
      (R : Ambient (q*q) →L[ℝ] (Ambient q →L[ℝ] Ambient q)),
      (∀T,R (E T)=T) → (∀z,E (R z)=z) →
      (∀T : Ambient q →L[ℝ] Ambient q,‖E T‖^2=∑j : Fin q,‖T (EuclideanSpace.single j 1)‖^2) →
      ∀(p : Domain n → Ambient (q*q)) (Dp : Domain n → Gradient n (q*q))
        (A : Domain n → Fin n → (Ambient q →L[ℝ] Ambient q)),
        MemW12 (ballDomain (0 : Domain n) 1) p Dp →
        (∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),star (R (p x))*R (p x)=1) →
        (∀i,MemLp (fun x=>A x i) 2 (volume.restrict (ball (0 : Domain n) 1))) →
        (∀i,∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),star (A x i)= -A x i) →
        let G := fun x i=>E (star (R (p x))*A x i*R (p x))
        let μ := volume.restrict (ball (0 : Domain n) 1)
        ∃(u : Domain n → Ambient (q*q))
          (c : Fin n → Fin n → Domain n → Ambient (q*q))
          (Dc : Fin n → Fin n → Domain n → Gradient n (q*q))
          (Q : Domain n → Gradient n (q*q)),
          MemW12 (ballDomain (0 : Domain n) 1) u (fun x i=>G x i-Q x i) ∧
          (∀x,star (R (u x))= -R (u x)) ∧
          (∀i j,MemW12 (ballDomain (0 : Domain n) 1) (c i j) (Dc i j)) ∧
          (∀i j x,star (R (c i j x))= -R (c i j x)) ∧
          (∀i j x k,star (R (Dc i j x k))= -R (Dc i j x k)) ∧
          (∀x i,star (R (Q x i))= -R (Q x i)) ∧
          (∀i,MemLp (fun x=>Q x i) 2 μ) ∧
          (∀ᵐx∂μ,∀i j,c i j x= -c j i x) ∧
          (∀ᵐx∂μ,∀i j k,Dc i j x k+Dc j k x i+Dc k i x j=0) ∧
          (∀ᵐx∂μ,∀j,(∑i : Fin n,Dc i j x i)=Q x j) ∧
          (∀(j : Fin n) (ψ : Domain n → Ambient (q*q)) (Dψ : Domain n → Gradient n (q*q)),
            MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ →
            Integrable (fun x=>∑i : Fin n,inner ℝ (c i j x) (Dψ x i)) μ ∧
            Integrable (fun x=>inner ℝ (Q x j) (ψ x)) μ ∧
            (∫x,∑i : Fin n,inner ℝ (c i j x) (Dψ x i) ∂μ)=-(∫x,inner ℝ (Q x j) (ψ x) ∂μ)) ∧
          (∀(ψ : Domain n → Ambient (q*q)) (Dψ : Domain n → Gradient n (q*q)),
            MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ →
            Integrable (fun x=>∑i : Fin n,inner ℝ (Q x i) (Dψ x i)) μ ∧
            (∫x,∑i : Fin n,inner ℝ (Q x i) (Dψ x i) ∂μ)=0) ∧
          ∀(ν : {ν : ℝ //0≤ν ∧ ν≤(n:ℝ)-1}) (K : ℝ),0≤K →
            (∀a : Domain n,a∈ball (0 : Domain n) 1 → ∀r : ℝ,0<r →
              (∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (fun i=>E (A x i)))≤K*r^ν.val) →
            ∀a : Domain n,a∈ball (0 : Domain n) 1 → ∀r : ℝ,0<r →
              (∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (Q x))≤(effectiveCoexactPowerConstant n : ℝ)*K*r^ν.val := by
  obtain ⟨_Cp,_hCp,HT⟩ := effective_same_coexact_operator_all_lp_and_power_growth_unitBall n hn
  intro q E R hRE hER hE p Dp A hp hOrth hA hAskew G μ
  obtain ⟨S,_hFormula,hTarget,hSelf,hNorm,hFix⟩ :=
    exists_full_coefficient_skew_projection E R hRE hER hE
  have hP := R.continuous.comp_aestronglyMeasurable hp.2.1.aestronglyMeasurable
  have hGNorm (i : Fin n) : ∀ᵐx∂μ,‖G x i‖=‖E (A x i)‖ := by
    filter_upwards [hOrth] with x hx
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    have hStar : star (star (R (p x)))*star (R (p x))=1 := by
      rw [star_star]
      exact mul_star_eq_one_of_star_mul_eq_one _ hx
    change ‖E (star (R (p x))*A x i*R (p x))‖^2=‖E (A x i)‖^2
    rw [encoded_norm_sq_mul_right_orthogonal E hE _ _ hx,
      encoded_norm_sq_mul_left_orthogonal E hE _ _ hStar]
  have hGLp (i : Fin n) : MemLp (fun x=>G x i) 2 μ := by
    have hEA := E.lipschitz.comp_memLp (map_zero E) (hA i)
    have hGM : AEStronglyMeasurable (fun x=>G x i) μ :=
      E.continuous.comp_aestronglyMeasurable ((((ContinuousLinearMap.adjoint (𝕜:=ℝ) (E:=Ambient q) (F:=Ambient q)).continuous.comp_aestronglyMeasurable hP).mul (hA i).aestronglyMeasurable).mul hP)
    exact hEA.of_le hGM ((hGNorm i).mono fun x hx=>hx.le)
  have hGHS : (fun x=>hsNormSq (G x))=ᵐ[μ](fun x=>hsNormSq (fun i=>E (A x i))) := by
    filter_upwards [ae_all_iff.mpr hGNorm] with x hx
    simp only [hsNormSq,hx]
  have hSG : ∀ᵐx∂μ,∀i,S (G x i)=G x i := by
    filter_upwards [ae_all_iff.mpr hAskew] with x hx i
    apply hFix
    rw [hRE]
    simp only [star_mul,star_star,hx]
    ext z
    simp only [mul_apply_eq_comp,neg_apply,map_neg]
  let enc : Gradient n (q*q) → Ambient (n*(q*q)) := fun H=>WithLp.toLp 2
    (fun k=>H (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)
  let dec := fun (W : Domain n → Ambient (n*(q*q))) x i=>WithLp.toLp 2
    (fun j : Fin (q*q)=>W x (finProdFinEquiv (i,j)))
  let W := (memLp_hs_flatten G hGLp).toLp (fun x=>enc (G x))
  have hDecode : dec W=ᵐ[μ]G := by
    filter_upwards [(memLp_hs_flatten G hGLp).coeFn_toLp] with x hx
    change (fun i=>WithLp.toLp 2 (fun j : Fin (q*q)=>W x (finProdFinEquiv (i,j))))=G x
    rw [hx]
    exact hs_unflatten_flatten (G x)
  obtain ⟨T,_hT,_hSelf,_hIdem,Hresponse⟩ := HT (q*q)
  obtain ⟨u,c,Dc,hu,hc,hSkew,hClosed,hDiv,hNormal,hNatural,_hH1,_hEnergy,_hCore,_hLp,hM⟩ := Hresponse W
  let Q := dec (T W)
  let v := fun x=>S (u x)
  let d := fun i j x=>S (c i j x)
  let Dd := fun i j x k=>S (Dc i j x k)
  let P := fun x i=>S (Q x i)
  have huG : MemW12 (ballDomain (0 : Domain n) 1) v (fun x i=>G x i-P x i) := by
    apply (native_linear_image u _ hu S).congr_ae (Eventually.of_forall fun _=>rfl)
    filter_upwards [hDecode,hSG] with x hx hSx
    funext i
    change S (dec W x i-Q x i)=G x i-S (Q x i)
    rw [map_sub,hx,hSx]
  have hd (i j : Fin n) : MemW12 (ballDomain (0 : Domain n) 1) (d i j) (Dd i j) :=
    native_linear_image (c i j) (Dc i j) (hc i j) S
  have hQ (i : Fin n) : MemLp (fun x=>Q x i) 2 μ :=
    memLp_hs_unflatten (T W) (Lp.memLp (T W)) i
  have hP (i : Fin n) : MemLp (fun x=>P x i) 2 μ :=
    S.lipschitz.comp_memLp (map_zero S) (hQ i)
  have hdS : ∀ᵐx∂μ,∀i j,d i j x= -d j i x := by
    filter_upwards [hSkew] with x hx i j
    change S (c i j x)= -S (c j i x)
    rw [hx,map_neg]
  have hdC : ∀ᵐx∂μ,∀i j k,Dd i j x k+Dd j k x i+Dd k i x j=0 := by
    filter_upwards [hClosed] with x hx i j k
    change S (Dc i j x k)+S (Dc j k x i)+S (Dc k i x j)=0
    rw [←map_add,←map_add,hx,map_zero]
  have hdD : ∀ᵐx∂μ,∀j,(∑i : Fin n,Dd i j x i)=P x j := by
    filter_upwards [hDiv] with x hx j
    change (∑i : Fin n,S (Dc i j x i))=S (Q x j)
    rw [←map_sum,hx]
  have hdN (j : Fin n) (ψ : Domain n → Ambient (q*q)) (Dψ : Domain n → Gradient n (q*q))
      (hψ : MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ) :
      Integrable (fun x=>∑i : Fin n,inner ℝ (d i j x) (Dψ x i)) μ ∧
      Integrable (fun x=>inner ℝ (P x j) (ψ x)) μ ∧
      (∫x,∑i : Fin n,inner ℝ (d i j x) (Dψ x i) ∂μ)=-(∫x,inner ℝ (P x j) (ψ x) ∂μ) := by
    obtain ⟨hI,hJ,hEq⟩ := hNormal j (fun x=>S (ψ x)) (fun x i=>S (Dψ x i))
      (native_linear_image ψ Dψ hψ S)
    have hLeft : (fun x=>∑i : Fin n,inner ℝ (c i j x) (S (Dψ x i))) =
        (fun x=>∑i : Fin n,inner ℝ (d i j x) (Dψ x i)) :=
      funext fun x=>Finset.sum_congr rfl (fun i _=>(hSelf _ _).symm)
    have hRight : (fun x=>inner ℝ (Q x j) (S (ψ x))) =
        (fun x=>inner ℝ (P x j) (ψ x)) := funext fun x=>(hSelf _ _).symm
    exact ⟨hI.congr (Eventually.of_forall (congrFun hLeft)),
      hJ.congr (Eventually.of_forall (congrFun hRight)),
      (integral_congr_ae (Eventually.of_forall (congrFun hLeft))).symm.trans
        (hEq.trans (congrArg Neg.neg (integral_congr_ae
          (Eventually.of_forall (congrFun hRight)))))⟩
  have hPN (ψ : Domain n → Ambient (q*q)) (Dψ : Domain n → Gradient n (q*q))
      (hψ : MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ) :
      Integrable (fun x=>∑i : Fin n,inner ℝ (P x i) (Dψ x i)) μ ∧
      (∫x,∑i : Fin n,inner ℝ (P x i) (Dψ x i) ∂μ)=0 := by
    obtain ⟨hI,hEq⟩ := hNatural (fun x=>S (ψ x)) (fun x i=>S (Dψ x i))
      (native_linear_image ψ Dψ hψ S)
    have hLeft : (fun x=>∑i : Fin n,inner ℝ (Q x i) (S (Dψ x i))) =
        (fun x=>∑i : Fin n,inner ℝ (P x i) (Dψ x i)) :=
      funext fun x=>Finset.sum_congr rfl (fun i _=>(hSelf _ _).symm)
    exact ⟨hI.congr (Eventually.of_forall (congrFun hLeft)),
      (integral_congr_ae (Eventually.of_forall (congrFun hLeft))).symm.trans hEq⟩
  refine ⟨v,d,Dd,P,huG,(fun x=>hTarget _),hd,(fun i j x=>hTarget _),
    (fun i j x k=>hTarget _),(fun x i=>hTarget _),hP,hdS,hdC,hdD,hdN,hPN,?_⟩
  intro ν K hK hGrowth a ha r hr
  have hDecodedHS : (fun x=>hsNormSq (dec W x))=ᵐ[μ](fun x=>hsNormSq (G x)) :=
    hDecode.mono fun x hx=>congrArg hsNormSq hx
  have hForcing : ∀a : Domain n,a∈ball (0 : Domain n) 1 → ∀r : ℝ,0<r →
      (∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (dec W x))≤K*r^ν.val := by
    intro a ha r hr
    rw [integral_congr_ae ((hDecodedHS.trans hGHS).filter_mono
      (ae_mono (Measure.restrict_mono_set volume inter_subset_right)))]
    exact hGrowth a ha r hr
  have hPQ (x : Domain n) : hsNormSq (P x)≤hsNormSq (Q x) :=
    Finset.sum_le_sum fun i _=>pow_le_pow_left₀ (norm_nonneg _) (hNorm _) 2
  have hPIB : IntegrableOn (fun x=>hsNormSq (P x)) (ball (0 : Domain n) 1) volume :=
    integrable_hsNormSq_of_columns P hP
  have hQIB : IntegrableOn (fun x=>hsNormSq (Q x)) (ball (0 : Domain n) 1) volume :=
    integrable_hsNormSq_of_columns Q hQ
  have hPI := hPIB.mono_set (inter_subset_right (s:=ball a r))
  have hQI := hQIB.mono_set (inter_subset_right (s:=ball a r))
  exact (integral_mono hPI hQI hPQ).trans (hM ν K hK hForcing a ha r hr)

end StationaryHarmonicMaps.Analysis

end
