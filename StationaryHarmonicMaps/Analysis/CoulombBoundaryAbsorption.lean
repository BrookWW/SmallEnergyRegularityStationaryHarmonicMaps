module

public import StationaryHarmonicMaps.Analysis.CoulombBoundaryMorreyPart
public import StationaryHarmonicMaps.Analysis.CoulombGivenFrameRelativeSplit
public import StationaryHarmonicMaps.Analysis.UniformGrowthAbsorption
public import StationaryHarmonicMaps.Geometry.OrthogonalRightHS

/-!
# Full boundary Morrey absorption for a given critical Coulomb frame

The original frame's natural Coulomb connection produces its actual linear
and nonlinear relative responses. Their true full-ball growth estimates
improve every effective coefficient of the original gradient. A finite
original power-growth bound and scalar absorption then control that same
frame and its same connection on every truncated ball.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

private theorem frame_gradient_hs_le_relative_split {n q : ℕ}
    (E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient (q*q))
    (R : Ambient (q*q) →L[ℝ] (Ambient q →L[ℝ] Ambient q))
    (hER : ∀z,E (R z)=z)
    (hE : ∀T : Ambient q →L[ℝ] Ambient q,‖E T‖^2=∑j : Fin q,‖T (EuclideanSpace.single j 1)‖^2)
    (P : Ambient q →L[ℝ] Ambient q) (hP : star P*P=1)
    (D : Gradient n (q*q)) (A : Fin n → (Ambient q →L[ℝ] Ambient q))
    (b c : Gradient n (q*q))
    (hSplit : ∀i,b i+c i=E (star P*R (D i)+star P*A i*P)) :
    hsNormSq D≤4*hsNormSq b+4*hsNormSq c+2*hsNormSq (fun i=>E (A i)) := by
  let F := fun i=>E (star P*R (D i))
  let G := fun i=>E (star P*A i*P)
  have hStar : star (star P)*star P=1 := by
    rw [star_star]
    exact mul_star_eq_one_of_star_mul_eq_one P hP
  have hF : hsNormSq F=hsNormSq D := by
    apply Finset.sum_congr rfl
    intro i _
    change ‖E (star P*R (D i))‖^2=‖D i‖^2
    rw [encoded_norm_sq_mul_left_orthogonal E hE _ _ hStar,hER]
  have hG : hsNormSq G=hsNormSq (fun i=>E (A i)) := by
    apply Finset.sum_congr rfl
    intro i _
    change ‖E (star P*A i*P)‖^2=‖E (A i)‖^2
    rw [encoded_norm_sq_mul_right_orthogonal E hE _ _ hP,
      encoded_norm_sq_mul_left_orthogonal E hE _ _ hStar]
  have hFG : F=(fun i=>(b i+c i)+ -G i) := by
    funext i
    have H := hSplit i
    rw [map_add] at H
    change b i+c i=F i+G i at H
    rw [H]
    abel
  have H1 := HolderToCK.hsNormSq_add_le b c
  have H2 := HolderToCK.hsNormSq_add_le (fun i=>b i+c i) (fun i=> -G i)
  change hsNormSq (fun i=>b i+c i)≤2*hsNormSq b+2*hsNormSq c at H1
  change hsNormSq (fun i=>(b i+c i)+ -G i)≤
    2*hsNormSq (fun i=>b i+c i)+2*hsNormSq (fun i=> -G i) at H2
  have hNeg : hsNormSq (fun i=> -G i)=hsNormSq G := by simp only [hsNormSq,norm_neg]
  rw [←hF,hFG]
  rw [hNeg,hG] at H2
  nlinarith only [H1,H2]

/-- A given native natural Coulomb frame with small original critical norm
and finite original ν-growth has full boundary ν-growth controlled by the
original connection. No gauge existence or stronger-class membership is
concluded from this conditional a priori estimate. -/
theorem exists_coulomb_boundary_power_growth_absorption (n : ℕ) (hn : 2≤n) (q : ℕ)
    (E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient (q*q))
    (R : Ambient (q*q) →L[ℝ] (Ambient q →L[ℝ] Ambient q))
    (hRE : ∀T,R (E T)=T) (hER : ∀z,E (R z)=z)
    (hE : ∀T : Ambient q →L[ℝ] Ambient q,‖E T‖^2=∑j : Fin q,‖T (EuclideanSpace.single j 1)‖^2)
    (ν : ℝ) (hν : 0≤ν) (hνn : ν<(n:ℝ)) :
    ∃δ C : ℝ,0<δ ∧ 0<C ∧ ∀ (p : Domain n → Ambient (q*q)) (Dp : Domain n → Gradient n (q*q))
      (A : Domain n → Fin n → (Ambient q →L[ℝ] Ambient q)) (K₀ K : ℝ),
      MemW12 (ballDomain (0 : Domain n) 1) p Dp →
      (∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),star (R (p x))*R (p x)=1) →
      (∀i,MemLp (fun x=>A x i) 2 (volume.restrict (ball (0 : Domain n) 1))) →
      (∀i,∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),star (A x i)= -A x i) →
      criticalGradientMorreySquare Dp (ball (0 : Domain n) 1)≤ENNReal.ofReal (δ^2) →
      (∀a∈ball (0 : Domain n) 1,∀r : ℝ,0<r →
        (∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (Dp x))≤K₀*r^ν) → 0≤K →
      (∀a∈ball (0 : Domain n) 1,∀r : ℝ,0<r →
        (∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (fun i=>E (A x i)))≤K*r^ν) →
      let Z := fun x i=>star (R (p x))*R (Dp x i)+star (R (p x))*A x i*R (p x)
      (∀ (ψ : Domain n → Ambient (q*q)) (Dψ : Domain n → Gradient n (q*q)),
        MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ →
        (∫x in ball (0 : Domain n) 1,∑i : Fin n,inner ℝ (E (Z x i)) (Dψ x i))=0) →
      ∀a∈ball (0 : Domain n) 1,∀r : ℝ,0<r →
        (∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (Dp x))≤C*K*r^ν := by
  obtain ⟨Lb,hLb,Hb⟩ := exists_coulomb_boundary_logarithmic_power_growth n hn q E R hER hE ν hν hνn
  obtain ⟨Lc,hLc,Hsplit⟩ := exists_given_frame_coulomb_relative_fields_unitBall n hn
  let l := Lc ⟨ν,hν,hνn⟩
  have hl : 0<l := hLc _
  let δ := Real.sqrt (1/(8*Lb))
  have hδ : 0<δ := Real.sqrt_pos.mpr (by positivity)
  have hδEq : 4*Lb*δ^2=(1/2 : ℝ) := by
    dsimp only [δ]
    rw [Real.sq_sqrt (by positivity : 0≤1/(8*Lb))]
    field_simp
    ring
  let C := 2*(4*l+2)
  have hC : 0<C := by dsimp only [C];positivity
  refine ⟨δ,C,hδ,hC,?_⟩
  intro p Dp A K₀ K hp hOrth hA hAskew hCritical hInitial hK hGrowth Z hNatural
  obtain ⟨Qc,Qb,v,w,c,Dc,hQc,hQb,_hw,hv,_hQct,_hQbt,hTotal,hQbN,_hQcN,
    _hc,_hct,_hDct,_hCS,_hCC,_hCD,_hCN,hLinear⟩ :=
    Hsplit q E R hRE hER hE p Dp A hp hOrth hA hAskew hNatural
  let μ := volume.restrict (ball (0 : Domain n) 1)
  have hAI : Integrable (fun x=>hsNormSq (fun i=>E (A x i))) μ :=
    integrable_hsNormSq_of_columns _ (fun i=>E.lipschitz.comp_memLp (map_zero E) (hA i))
  have hBI : Integrable (fun x=>hsNormSq (Qb x)) μ := integrable_hsNormSq_of_columns _ hQb
  have hCI : Integrable (fun x=>hsNormSq (Qc x)) μ := integrable_hsNormSq_of_columns _ hQc
  have hPoint : ∀ᵐx∂μ,hsNormSq (Dp x)≤4*hsNormSq (Qb x)+4*hsNormSq (Qc x)+
      2*hsNormSq (fun i=>E (A x i)) := by
    filter_upwards [hOrth] with x hx
    exact frame_gradient_hs_le_relative_split E R hER hE _ hx (Dp x) (A x) (Qb x) (Qc x) (hTotal x)
  let X := (ball (0 : Domain n) 1) × PositiveRadius
  letI : Nonempty X := ⟨(⟨0,mem_ball_self (by norm_num)⟩,⟨1,by norm_num⟩)⟩
  let f := fun x : X=>∫y in ball x.1.val x.2.val∩ball (0 : Domain n) 1,hsNormSq (Dp y)
  let weight := fun x : X=>x.2.val^ν
  have hf (x : X) : 0≤f x := integral_nonneg fun _=>hsNormSq_nonneg _
  have hWeight (x : X) : 0<weight x := Real.rpow_pos_of_pos x.2.property ν
  have hFinite (x : X) : f x≤K₀*weight x := hInitial x.1.val x.1.property x.2.val x.2.property
  have hStep (J : ℝ) (hJ : 0≤J) (hJG : ∀x : X,f x≤J*weight x) (x : X) :
      f x≤((1/2 : ℝ)*J+(4*l+2)*K)*weight x := by
    have hOriginal (a : Domain n) (ha : a∈ball (0 : Domain n) 1) (r : ℝ) (hr : 0<r) :
        (∫y in ball a r∩ball (0 : Domain n) 1,hsNormSq (Dp y))≤J*r^ν := hJG (⟨a,ha⟩,⟨r,hr⟩)
    have hB := Hb p Dp δ J hp hOrth hδ.le hCritical hJ hOriginal Qb v hQb hv
      (fun ψ Dψ hψ=>(hQbN ψ Dψ hψ).2) x.1.val x.2.val x.2.property
    have hC := hLinear ⟨ν,hν,hνn⟩ K hK hGrowth x.1.val x.1.property x.2.val x.2.property
    have hAQuery := hGrowth x.1.val x.1.property x.2.val x.2.property
    let S := ball x.1.val x.2.val∩ball (0 : Domain n) 1
    have hSub : S⊆ball (0 : Domain n) 1 := inter_subset_right
    have hBS : IntegrableOn (fun y=>hsNormSq (Qb y)) S volume :=
      hBI.mono_measure (Measure.restrict_mono_set volume hSub)
    have hCS : IntegrableOn (fun y=>hsNormSq (Qc y)) S volume :=
      hCI.mono_measure (Measure.restrict_mono_set volume hSub)
    have hAS : IntegrableOn (fun y=>hsNormSq (fun i=>E (A y i))) S volume :=
      hAI.mono_measure (Measure.restrict_mono_set volume hSub)
    have hIntegrable : IntegrableOn
        (fun y=>4*hsNormSq (Qb y)+4*hsNormSq (Qc y)+2*hsNormSq (fun i=>E (A y i))) S volume :=
      ((hBS.const_mul 4).add (hCS.const_mul 4)).add (hAS.const_mul 2)
    have H := integral_mono_ae (hp.integrable_hsNormSq.mono_set hSub) hIntegrable
      (hPoint.filter_mono (ae_mono (Measure.restrict_mono_set volume hSub)))
    change (∫y in S,hsNormSq (Dp y))≤∫y in S,
      4*hsNormSq (Qb y)+4*hsNormSq (Qc y)+2*hsNormSq (fun i=>E (A y i)) at H
    have hSumI : IntegrableOn (fun y=>4*hsNormSq (Qb y)+4*hsNormSq (Qc y)) S volume :=
      (hBS.const_mul 4).add (hCS.const_mul 4)
    have hIntegralEq : (∫y in S,4*hsNormSq (Qb y)+4*hsNormSq (Qc y)+
        2*hsNormSq (fun i=>E (A y i)))=
        4*(∫y in S,hsNormSq (Qb y))+4*(∫y in S,hsNormSq (Qc y))+
          2*(∫y in S,hsNormSq (fun i=>E (A y i))) := by
      calc
        _=(∫y in S,4*hsNormSq (Qb y)+4*hsNormSq (Qc y))+
            (∫y in S,2*hsNormSq (fun i=>E (A y i))) := integral_add hSumI (hAS.const_mul 2)
        _=((∫y in S,4*hsNormSq (Qb y))+(∫y in S,4*hsNormSq (Qc y)))+
            (∫y in S,2*hsNormSq (fun i=>E (A y i))) := by
          rw [integral_add (hBS.const_mul 4) (hCS.const_mul 4)]
        _=_ := by rw [integral_const_mul,integral_const_mul,integral_const_mul]
    rw [hIntegralEq] at H
    change f x≤4*(∫y in S,hsNormSq (Qb y))+4*(∫y in S,hsNormSq (Qc y))+
      2*(∫y in S,hsNormSq (fun i=>E (A y i))) at H
    have H' : f x≤4*(Lb*δ^2*J*weight x)+4*(l*K*weight x)+2*(K*weight x) := by
      dsimp only [S] at H
      exact H.trans (add_le_add (add_le_add (mul_le_mul_of_nonneg_left hB (by norm_num))
        (mul_le_mul_of_nonneg_left hC (by norm_num))) (mul_le_mul_of_nonneg_left hAQuery (by norm_num)))
    exact H'.trans_eq (by rw [←hδEq];ring)
  have hAbsorb := uniform_weighted_growth_absorption f weight hf hWeight (1/2) ((4*l+2)*K) K₀
    (by norm_num) (by norm_num) (by positivity) hFinite hStep
  intro a ha r hr
  have H := hAbsorb (⟨a,ha⟩,⟨r,hr⟩)
  exact H.trans_eq (by dsimp only [C];norm_num;ring)


private theorem frame_connection_hs_le_gradient_and_original {n q : ℕ}
    (E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient (q*q))
    (R : Ambient (q*q) →L[ℝ] (Ambient q →L[ℝ] Ambient q))
    (hER : ∀z,E (R z)=z)
    (hE : ∀T : Ambient q →L[ℝ] Ambient q,‖E T‖^2=∑j : Fin q,‖T (EuclideanSpace.single j 1)‖^2)
    (P : Ambient q →L[ℝ] Ambient q) (hP : star P*P=1)
    (D : Gradient n (q*q)) (A : Fin n → (Ambient q →L[ℝ] Ambient q)) :
    hsNormSq (fun i=>E (star P*R (D i)+star P*A i*P))≤
      2*hsNormSq D+2*hsNormSq (fun i=>E (A i)) := by
  have hStar : star (star P)*star P=1 := by
    rw [star_star]
    exact mul_star_eq_one_of_star_mul_eq_one P hP
  have hCol (i : Fin n) :
      ‖E (star P*R (D i)+star P*A i*P)‖^2=‖D i+E (A i*P)‖^2 := by
    rw [mul_assoc,←mul_add,encoded_norm_sq_mul_left_orthogonal E hE _ _ hStar,map_add,hER]
  have hNorm : hsNormSq (fun i=>E (A i*P))=hsNormSq (fun i=>E (A i)) :=
    Finset.sum_congr rfl (fun i _=>encoded_norm_sq_mul_right_orthogonal E hE _ _ hP)
  have H := HolderToCK.hsNormSq_add_le D (fun i=>E (A i*P))
  rw [hNorm] at H
  simpa only [hsNormSq,hCol,Pi.add_apply] using H

/-- The same small-critical native Coulomb frame and its original full
natural connection satisfy one joint full-boundary power-growth bound.
The original finite frame coefficient is eliminated by absorption. -/
theorem exists_coulomb_boundary_joint_power_growth_absorption (n : ℕ) (hn : 2≤n) (q : ℕ)
    (E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient (q*q))
    (R : Ambient (q*q) →L[ℝ] (Ambient q →L[ℝ] Ambient q))
    (hRE : ∀T,R (E T)=T) (hER : ∀z,E (R z)=z)
    (hE : ∀T : Ambient q →L[ℝ] Ambient q,‖E T‖^2=∑j : Fin q,‖T (EuclideanSpace.single j 1)‖^2)
    (ν : ℝ) (hν : 0≤ν) (hνn : ν<(n:ℝ)) :
    ∃δ C : ℝ,0<δ ∧ 0<C ∧ ∀ (p : Domain n → Ambient (q*q)) (Dp : Domain n → Gradient n (q*q))
      (A : Domain n → Fin n → (Ambient q →L[ℝ] Ambient q)) (K₀ K : ℝ),
      MemW12 (ballDomain (0 : Domain n) 1) p Dp →
      (∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),star (R (p x))*R (p x)=1) →
      (∀i,MemLp (fun x=>A x i) 2 (volume.restrict (ball (0 : Domain n) 1))) →
      (∀i,∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),star (A x i)= -A x i) →
      criticalGradientMorreySquare Dp (ball (0 : Domain n) 1)≤ENNReal.ofReal (δ^2) →
      (∀a∈ball (0 : Domain n) 1,∀r : ℝ,0<r →
        (∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (Dp x))≤K₀*r^ν) → 0≤K →
      (∀a∈ball (0 : Domain n) 1,∀r : ℝ,0<r →
        (∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (fun i=>E (A x i)))≤K*r^ν) →
      let Z := fun x i=>star (R (p x))*R (Dp x i)+star (R (p x))*A x i*R (p x)
      (∀ (ψ : Domain n → Ambient (q*q)) (Dψ : Domain n → Gradient n (q*q)),
        MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ →
        (∫x in ball (0 : Domain n) 1,∑i : Fin n,inner ℝ (E (Z x i)) (Dψ x i))=0) →
      ∀a∈ball (0 : Domain n) 1,∀r : ℝ,0<r →
        ((∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (Dp x))≤C*K*r^ν) ∧
        ((∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (fun i=>E (Z x i)))≤C*K*r^ν) := by
  obtain ⟨δ,D,hδ,hD,HD⟩ := exists_coulomb_boundary_power_growth_absorption n hn q E R hRE hER hE ν hν hνn
  refine ⟨δ,2*D+2,hδ,by positivity,?_⟩
  intro p Dp A K₀ K hp hOrth hA hAskew hCritical hInitial hK hGrowth Z hNatural a ha r hr
  have hDP := HD p Dp A K₀ K hp hOrth hA hAskew hCritical hInitial hK hGrowth hNatural a ha r hr
  obtain ⟨_hZ,hEZ,_hSkew⟩ := frame_connection_memLp_and_skew E R hER hE p Dp hp hOrth A hA hAskew
  let S := ball a r∩ball (0 : Domain n) 1
  have hSub : S⊆ball (0 : Domain n) 1 := inter_subset_right
  have hZI : IntegrableOn (fun x=>hsNormSq (fun i=>E (Z x i))) S volume :=
    (integrable_hsNormSq_of_columns _ hEZ).mono_measure (Measure.restrict_mono_set volume hSub)
  have hDI : IntegrableOn (fun x=>hsNormSq (Dp x)) S volume := hp.integrable_hsNormSq.mono_set hSub
  have hAI : IntegrableOn (fun x=>hsNormSq (fun i=>E (A x i))) S volume :=
    (integrable_hsNormSq_of_columns _ (fun i=>E.lipschitz.comp_memLp (map_zero E) (hA i))).mono_measure
      (Measure.restrict_mono_set volume hSub)
  have hPoint : ∀ᵐx∂volume.restrict S,hsNormSq (fun i=>E (Z x i))≤
      2*hsNormSq (Dp x)+2*hsNormSq (fun i=>E (A x i)) := by
    filter_upwards [hOrth.filter_mono (ae_mono (Measure.restrict_mono_set volume hSub))] with x hx
    exact frame_connection_hs_le_gradient_and_original E R hER hE _ hx (Dp x) (A x)
  have hZBound : (∫x in S,hsNormSq (fun i=>E (Z x i)))≤
      2*(∫x in S,hsNormSq (Dp x))+2*(∫x in S,hsNormSq (fun i=>E (A x i))) := by
    have H := integral_mono_ae hZI ((hDI.const_mul 2).add (hAI.const_mul 2)) hPoint
    change (∫x in S,hsNormSq (fun i=>E (Z x i)))≤
      ∫x in S,2*hsNormSq (Dp x)+2*hsNormSq (fun i=>E (A x i)) at H
    rwa [integral_add (hDI.const_mul 2) (hAI.const_mul 2),integral_const_mul,integral_const_mul] at H
  constructor
  · exact hDP.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith only [hD] : D≤2*D+2) hK) (Real.rpow_nonneg hr.le ν))
  · have hAG := hGrowth a ha r hr
    exact hZBound.trans ((add_le_add (mul_le_mul_of_nonneg_left hDP (by norm_num))
      (mul_le_mul_of_nonneg_left hAG (by norm_num))).trans_eq (by ring))

@[expose] def effectiveCoulombAbsorptionAmplitude (n q : ℕ) : ℚ :=
  EffectiveCoulomb.absorptionAmplitude (effectiveCoulombLogarithmicPowerConstant n q)

@[expose] def effectiveCoulombAbsorptionConstant (n : ℕ) : ℚ :=
  2 * (4 * effectiveCoexactPowerConstant n + 2)

@[expose] def effectiveCoulombJointConstant (n : ℕ) : ℚ :=
  2 * effectiveCoulombAbsorptionConstant n + 2

theorem effectiveCoulombAbsorptionAmplitude_pos (n : ℕ) (hn : 2 ≤ n) (q : ℕ) :
    0 < effectiveCoulombAbsorptionAmplitude n q :=
  EffectiveCoulomb.absorptionAmplitude_pos (effectiveCoulombLogarithmicPowerConstant_pos n hn q).le

theorem effectiveCoulombAbsorptionConstant_pos (n : ℕ) (hn : 1 ≤ n) :
    0 < effectiveCoulombAbsorptionConstant n := by
  have H := effectiveCoexactPowerConstant_pos n hn
  unfold effectiveCoulombAbsorptionConstant
  positivity

theorem effectiveCoulombJointConstant_pos (n : ℕ) (hn : 1 ≤ n) :
    0 < effectiveCoulombJointConstant n := by
  have H := effectiveCoulombAbsorptionConstant_pos n hn
  unfold effectiveCoulombJointConstant
  positivity

/-- A given native natural Coulomb frame with small original critical norm
and finite original ν-growth has full boundary ν-growth controlled by the
original connection. No gauge existence or stronger-class membership is
concluded from this conditional a priori estimate. -/
theorem effective_coulomb_boundary_power_growth_absorption (n : ℕ) (hn : 2≤n) (q : ℕ)
    (E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient (q*q))
    (R : Ambient (q*q) →L[ℝ] (Ambient q →L[ℝ] Ambient q))
    (hRE : ∀T,R (E T)=T) (hER : ∀z,E (R z)=z)
    (hE : ∀T : Ambient q →L[ℝ] Ambient q,‖E T‖^2=∑j : Fin q,‖T (EuclideanSpace.single j 1)‖^2)
    (ν : ℝ) (hν : 0≤ν) (hνCap : ν≤(n:ℝ)-1) :
    ∀ (p : Domain n → Ambient (q*q)) (Dp : Domain n → Gradient n (q*q))
      (A : Domain n → Fin n → (Ambient q →L[ℝ] Ambient q)) (K₀ K : ℝ),
      MemW12 (ballDomain (0 : Domain n) 1) p Dp →
      (∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),star (R (p x))*R (p x)=1) →
      (∀i,MemLp (fun x=>A x i) 2 (volume.restrict (ball (0 : Domain n) 1))) →
      (∀i,∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),star (A x i)= -A x i) →
      criticalGradientMorreySquare Dp (ball (0 : Domain n) 1)≤ENNReal.ofReal ((effectiveCoulombAbsorptionAmplitude n q : ℝ)^2) →
      (∀a∈ball (0 : Domain n) 1,∀r : ℝ,0<r →
        (∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (Dp x))≤K₀*r^ν) → 0≤K →
      (∀a∈ball (0 : Domain n) 1,∀r : ℝ,0<r →
        (∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (fun i=>E (A x i)))≤K*r^ν) →
      let Z := fun x i=>star (R (p x))*R (Dp x i)+star (R (p x))*A x i*R (p x)
      (∀ (ψ : Domain n → Ambient (q*q)) (Dψ : Domain n → Gradient n (q*q)),
        MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ →
        (∫x in ball (0 : Domain n) 1,∑i : Fin n,inner ℝ (E (Z x i)) (Dψ x i))=0) →
      ∀a∈ball (0 : Domain n) 1,∀r : ℝ,0<r →
        (∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (Dp x))≤(effectiveCoulombAbsorptionConstant n : ℝ)*K*r^ν := by
  let Lb : ℝ := effectiveCoulombLogarithmicPowerConstant n q
  have hLb : 0 < Lb := by
    change 0 < (effectiveCoulombLogarithmicPowerConstant n q : ℝ)
    exact_mod_cast effectiveCoulombLogarithmicPowerConstant_pos n hn q
  have Hb := effective_coulomb_boundary_logarithmic_power_growth n hn q E R hER hE ν hν hνCap
  have Hsplit := effective_given_frame_coulomb_relative_fields_unitBall n hn
  let l : ℝ := effectiveCoexactPowerConstant n
  have hl : 0 < l := by
    change 0 < (effectiveCoexactPowerConstant n : ℝ)
    exact_mod_cast effectiveCoexactPowerConstant_pos n (by omega)
  let δ : ℝ := effectiveCoulombAbsorptionAmplitude n q
  have hδ : 0 < δ := by
    change 0 < (effectiveCoulombAbsorptionAmplitude n q : ℝ)
    exact_mod_cast effectiveCoulombAbsorptionAmplitude_pos n hn q
  have hδScale : 4 * Lb * δ ^ 2 ≤ 1 / 2 :=
    EffectiveCoulomb.absorptionAmplitude_controls_square
      (effectiveCoulombLogarithmicPowerConstant_pos n hn q).le
  let C : ℝ := effectiveCoulombAbsorptionConstant n
  have hCeq : C = 2 * (4 * l + 2) := by
    simp only [C, l, effectiveCoulombAbsorptionConstant, Rat.cast_mul, Rat.cast_add, Rat.cast_ofNat]
  intro p Dp A K₀ K hp hOrth hA hAskew hCritical hInitial hK hGrowth Z hNatural
  obtain ⟨Qc,Qb,v,w,c,Dc,hQc,hQb,_hw,hv,_hQct,_hQbt,hTotal,hQbN,_hQcN,
    _hc,_hct,_hDct,_hCS,_hCC,_hCD,_hCN,hLinear⟩ :=
    Hsplit q E R hRE hER hE p Dp A hp hOrth hA hAskew hNatural
  let μ := volume.restrict (ball (0 : Domain n) 1)
  have hAI : Integrable (fun x=>hsNormSq (fun i=>E (A x i))) μ :=
    integrable_hsNormSq_of_columns _ (fun i=>E.lipschitz.comp_memLp (map_zero E) (hA i))
  have hBI : Integrable (fun x=>hsNormSq (Qb x)) μ := integrable_hsNormSq_of_columns _ hQb
  have hCI : Integrable (fun x=>hsNormSq (Qc x)) μ := integrable_hsNormSq_of_columns _ hQc
  have hPoint : ∀ᵐx∂μ,hsNormSq (Dp x)≤4*hsNormSq (Qb x)+4*hsNormSq (Qc x)+
      2*hsNormSq (fun i=>E (A x i)) := by
    filter_upwards [hOrth] with x hx
    exact frame_gradient_hs_le_relative_split E R hER hE _ hx (Dp x) (A x) (Qb x) (Qc x) (hTotal x)
  let X := (ball (0 : Domain n) 1) × PositiveRadius
  letI : Nonempty X := ⟨(⟨0,mem_ball_self (by norm_num)⟩,⟨1,by norm_num⟩)⟩
  let f := fun x : X=>∫y in ball x.1.val x.2.val∩ball (0 : Domain n) 1,hsNormSq (Dp y)
  let weight := fun x : X=>x.2.val^ν
  have hf (x : X) : 0≤f x := integral_nonneg fun _=>hsNormSq_nonneg _
  have hWeight (x : X) : 0<weight x := Real.rpow_pos_of_pos x.2.property ν
  have hFinite (x : X) : f x≤K₀*weight x := hInitial x.1.val x.1.property x.2.val x.2.property
  have hStep (J : ℝ) (hJ : 0≤J) (hJG : ∀x : X,f x≤J*weight x) (x : X) :
      f x≤((1/2 : ℝ)*J+(4*l+2)*K)*weight x := by
    have hOriginal (a : Domain n) (ha : a∈ball (0 : Domain n) 1) (r : ℝ) (hr : 0<r) :
        (∫y in ball a r∩ball (0 : Domain n) 1,hsNormSq (Dp y))≤J*r^ν := hJG (⟨a,ha⟩,⟨r,hr⟩)
    have hB := Hb p Dp δ J hp hOrth hδ.le hCritical hJ hOriginal Qb v hQb hv
      (fun ψ Dψ hψ=>(hQbN ψ Dψ hψ).2) x.1.val x.2.val x.2.property
    have hC := hLinear ⟨ν,hν,hνCap⟩ K hK hGrowth x.1.val x.1.property x.2.val x.2.property
    have hAQuery := hGrowth x.1.val x.1.property x.2.val x.2.property
    let S := ball x.1.val x.2.val∩ball (0 : Domain n) 1
    have hSub : S⊆ball (0 : Domain n) 1 := inter_subset_right
    have hBS : IntegrableOn (fun y=>hsNormSq (Qb y)) S volume :=
      hBI.mono_measure (Measure.restrict_mono_set volume hSub)
    have hCS : IntegrableOn (fun y=>hsNormSq (Qc y)) S volume :=
      hCI.mono_measure (Measure.restrict_mono_set volume hSub)
    have hAS : IntegrableOn (fun y=>hsNormSq (fun i=>E (A y i))) S volume :=
      hAI.mono_measure (Measure.restrict_mono_set volume hSub)
    have hIntegrable : IntegrableOn
        (fun y=>4*hsNormSq (Qb y)+4*hsNormSq (Qc y)+2*hsNormSq (fun i=>E (A y i))) S volume :=
      ((hBS.const_mul 4).add (hCS.const_mul 4)).add (hAS.const_mul 2)
    have H := integral_mono_ae (hp.integrable_hsNormSq.mono_set hSub) hIntegrable
      (hPoint.filter_mono (ae_mono (Measure.restrict_mono_set volume hSub)))
    change (∫y in S,hsNormSq (Dp y))≤∫y in S,
      4*hsNormSq (Qb y)+4*hsNormSq (Qc y)+2*hsNormSq (fun i=>E (A y i)) at H
    have hSumI : IntegrableOn (fun y=>4*hsNormSq (Qb y)+4*hsNormSq (Qc y)) S volume :=
      (hBS.const_mul 4).add (hCS.const_mul 4)
    have hIntegralEq : (∫y in S,4*hsNormSq (Qb y)+4*hsNormSq (Qc y)+
        2*hsNormSq (fun i=>E (A y i)))=
        4*(∫y in S,hsNormSq (Qb y))+4*(∫y in S,hsNormSq (Qc y))+
          2*(∫y in S,hsNormSq (fun i=>E (A y i))) := by
      calc
        _=(∫y in S,4*hsNormSq (Qb y)+4*hsNormSq (Qc y))+
            (∫y in S,2*hsNormSq (fun i=>E (A y i))) := integral_add hSumI (hAS.const_mul 2)
        _=((∫y in S,4*hsNormSq (Qb y))+(∫y in S,4*hsNormSq (Qc y)))+
            (∫y in S,2*hsNormSq (fun i=>E (A y i))) := by
          rw [integral_add (hBS.const_mul 4) (hCS.const_mul 4)]
        _=_ := by rw [integral_const_mul,integral_const_mul,integral_const_mul]
    rw [hIntegralEq] at H
    change f x≤4*(∫y in S,hsNormSq (Qb y))+4*(∫y in S,hsNormSq (Qc y))+
      2*(∫y in S,hsNormSq (fun i=>E (A y i))) at H
    have H' : f x≤4*(Lb*δ^2*J*weight x)+4*(l*K*weight x)+2*(K*weight x) := by
      dsimp only [S] at H
      exact H.trans (add_le_add (add_le_add (mul_le_mul_of_nonneg_left hB (by norm_num))
        (mul_le_mul_of_nonneg_left hC (by norm_num))) (mul_le_mul_of_nonneg_left hAQuery (by norm_num)))
    have hScale := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hδScale hJ) (hWeight x).le
    exact H'.trans (by nlinarith only [hScale])
  have hAbsorb := uniform_weighted_growth_absorption f weight hf hWeight (1/2) ((4*l+2)*K) K₀
    (by norm_num) (by norm_num) (by positivity) hFinite hStep
  intro a ha r hr
  have H := hAbsorb (⟨a,ha⟩,⟨r,hr⟩)
  exact H.trans_eq (by
    change (4*l+2)*K/(1-(1/2 : ℝ))*r^ν = C*K*r^ν
    rw [hCeq]
    ring)


/-- The same small-critical native Coulomb frame and its original full
natural connection satisfy one joint full-boundary power-growth bound.
The original finite frame coefficient is eliminated by absorption. -/
theorem effective_coulomb_boundary_joint_power_growth_absorption (n : ℕ) (hn : 2≤n) (q : ℕ)
    (E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient (q*q))
    (R : Ambient (q*q) →L[ℝ] (Ambient q →L[ℝ] Ambient q))
    (hRE : ∀T,R (E T)=T) (hER : ∀z,E (R z)=z)
    (hE : ∀T : Ambient q →L[ℝ] Ambient q,‖E T‖^2=∑j : Fin q,‖T (EuclideanSpace.single j 1)‖^2)
    (ν : ℝ) (hν : 0≤ν) (hνCap : ν≤(n:ℝ)-1) :
    ∀ (p : Domain n → Ambient (q*q)) (Dp : Domain n → Gradient n (q*q))
      (A : Domain n → Fin n → (Ambient q →L[ℝ] Ambient q)) (K₀ K : ℝ),
      MemW12 (ballDomain (0 : Domain n) 1) p Dp →
      (∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),star (R (p x))*R (p x)=1) →
      (∀i,MemLp (fun x=>A x i) 2 (volume.restrict (ball (0 : Domain n) 1))) →
      (∀i,∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),star (A x i)= -A x i) →
      criticalGradientMorreySquare Dp (ball (0 : Domain n) 1)≤ENNReal.ofReal ((effectiveCoulombAbsorptionAmplitude n q : ℝ)^2) →
      (∀a∈ball (0 : Domain n) 1,∀r : ℝ,0<r →
        (∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (Dp x))≤K₀*r^ν) → 0≤K →
      (∀a∈ball (0 : Domain n) 1,∀r : ℝ,0<r →
        (∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (fun i=>E (A x i)))≤K*r^ν) →
      let Z := fun x i=>star (R (p x))*R (Dp x i)+star (R (p x))*A x i*R (p x)
      (∀ (ψ : Domain n → Ambient (q*q)) (Dψ : Domain n → Gradient n (q*q)),
        MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ →
        (∫x in ball (0 : Domain n) 1,∑i : Fin n,inner ℝ (E (Z x i)) (Dψ x i))=0) →
      ∀a∈ball (0 : Domain n) 1,∀r : ℝ,0<r →
        ((∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (Dp x))≤(effectiveCoulombJointConstant n : ℝ)*K*r^ν) ∧
        ((∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (fun i=>E (Z x i)))≤(effectiveCoulombJointConstant n : ℝ)*K*r^ν) := by
  let D : ℝ := effectiveCoulombAbsorptionConstant n
  have hD : 0 < D := by
    change 0 < (effectiveCoulombAbsorptionConstant n : ℝ)
    exact_mod_cast effectiveCoulombAbsorptionConstant_pos n (by omega)
  have HD := effective_coulomb_boundary_power_growth_absorption n hn q E R hRE hER hE ν hν hνCap
  have hEq : (effectiveCoulombJointConstant n : ℝ) = 2 * D + 2 := by
    simp only [effectiveCoulombJointConstant, Rat.cast_mul, Rat.cast_add, Rat.cast_ofNat, D]
  rw [hEq]
  intro p Dp A K₀ K hp hOrth hA hAskew hCritical hInitial hK hGrowth Z hNatural a ha r hr
  have hDP := HD p Dp A K₀ K hp hOrth hA hAskew hCritical hInitial hK hGrowth hNatural a ha r hr
  obtain ⟨_hZ,hEZ,_hSkew⟩ := frame_connection_memLp_and_skew E R hER hE p Dp hp hOrth A hA hAskew
  let S := ball a r∩ball (0 : Domain n) 1
  have hSub : S⊆ball (0 : Domain n) 1 := inter_subset_right
  have hZI : IntegrableOn (fun x=>hsNormSq (fun i=>E (Z x i))) S volume :=
    (integrable_hsNormSq_of_columns _ hEZ).mono_measure (Measure.restrict_mono_set volume hSub)
  have hDI : IntegrableOn (fun x=>hsNormSq (Dp x)) S volume := hp.integrable_hsNormSq.mono_set hSub
  have hAI : IntegrableOn (fun x=>hsNormSq (fun i=>E (A x i))) S volume :=
    (integrable_hsNormSq_of_columns _ (fun i=>E.lipschitz.comp_memLp (map_zero E) (hA i))).mono_measure
      (Measure.restrict_mono_set volume hSub)
  have hPoint : ∀ᵐx∂volume.restrict S,hsNormSq (fun i=>E (Z x i))≤
      2*hsNormSq (Dp x)+2*hsNormSq (fun i=>E (A x i)) := by
    filter_upwards [hOrth.filter_mono (ae_mono (Measure.restrict_mono_set volume hSub))] with x hx
    exact frame_connection_hs_le_gradient_and_original E R hER hE _ hx (Dp x) (A x)
  have hZBound : (∫x in S,hsNormSq (fun i=>E (Z x i)))≤
      2*(∫x in S,hsNormSq (Dp x))+2*(∫x in S,hsNormSq (fun i=>E (A x i))) := by
    have H := integral_mono_ae hZI ((hDI.const_mul 2).add (hAI.const_mul 2)) hPoint
    change (∫x in S,hsNormSq (fun i=>E (Z x i)))≤
      ∫x in S,2*hsNormSq (Dp x)+2*hsNormSq (fun i=>E (A x i)) at H
    rwa [integral_add (hDI.const_mul 2) (hAI.const_mul 2),integral_const_mul,integral_const_mul] at H
  constructor
  · exact hDP.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith only [hD] : D≤2*D+2) hK) (Real.rpow_nonneg hr.le ν))
  · have hAG := hGrowth a ha r hr
    exact hZBound.trans ((add_le_add (mul_le_mul_of_nonneg_left hDP (by norm_num))
      (mul_le_mul_of_nonneg_left hAG (by norm_num))).trans_eq (by ring))

end StationaryHarmonicMaps.Analysis

end
