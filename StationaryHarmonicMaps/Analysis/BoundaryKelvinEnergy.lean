module

public import StationaryHarmonicMaps.Analysis.BoundaryInversionGeometry
public import StationaryHarmonicMaps.Analysis.BoundaryZeroExtensionPoincare
public import StationaryHarmonicMaps.Analysis.SobolevOddKelvinExtension

/-!
# Actual local energy of the native odd Kelvin reflection

The exterior portion of a sphere-centered query ball maps into the same
query ball inside the original unit ball. Actual inversion transport and
the original zero extension's local boundary Poincare estimate therefore
bound the same literal reflected gradient by the original local gradient
energy. The statement is an energy estimate; reflected harmonicity is not
an input or a conclusion.
-/

public section

open HarmonicMaps EuclideanGeometry MeasureTheory Filter Set
open StationaryHarmonicMaps.Geometry
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

private theorem norm_sub_sq_le_two {E : Type*} [NormedAddCommGroup E] (v w : E) :
    ‖v-w‖^2≤2*‖v‖^2+2*‖w‖^2 := by
  have H := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le v w) 2
  nlinarith only [H,sq_nonneg (‖v‖-‖w‖)]

private theorem odd_kelvin_gradient_hs_bound {n q : ℕ} (hn : 2≤n)
    (x : Domain n) (hx : 1≤‖x‖) (hx2 : ‖x‖≤2) (u : Ambient q) (D : Gradient n q) :
    hsNormSq (fun i=> -‖x‖^(2-(n:ℝ)) •
        (∑j : Fin n,(fderiv ℝ (inversion (0 : Domain n) 1) x (EuclideanSpace.single i 1)) j • D j)-
        ((2-(n:ℝ))*‖x‖^(-(n:ℝ))*inner ℝ x (EuclideanSpace.single i 1)) • u)≤
      2*hsNormSq D+(8*(n:ℝ)*|2-(n:ℝ)|^2)*‖u‖^2 := by
  let I := inversion (0 : Domain n) 1
  let C := fun i=>∑j : Fin n,(fderiv ℝ I x (EuclideanSpace.single i 1)) j • D j
  let w := ‖x‖^(2-(n:ℝ))
  let b := fun i=>(2-(n:ℝ))*‖x‖^(-(n:ℝ))*inner ℝ x (EuclideanSpace.single i 1)
  have hxPos : 0<‖x‖ := zero_lt_one.trans_le hx
  have hDI : ‖fderiv ℝ I x‖≤1 :=
    (norm_fderiv_unit_inversion_le x (norm_pos_iff.mp hxPos)).trans
      ((inv_le_one₀ (sq_pos_of_pos hxPos)).mpr (by nlinarith only [hx]))
  have hC : hsNormSq C≤hsNormSq D := by
    simpa only [one_pow,one_mul] using hsNormSq_right_comp_le_of_norm_le D (fderiv ℝ I x) hDI
  have hw0 : 0≤w := Real.rpow_nonneg (norm_nonneg _) _
  have hw1 : w≤1 := Real.rpow_le_one_of_one_le_of_nonpos hx
    (sub_nonpos.mpr (by exact_mod_cast hn))
  have hb (i : Fin n) : ‖b i‖≤2*|2-(n:ℝ)| := by
    have hp : ‖x‖^(-(n:ℝ))≤1 := Real.rpow_le_one_of_one_le_of_nonpos hx
      (neg_nonpos.mpr (Nat.cast_nonneg n))
    have hi : |inner ℝ x (EuclideanSpace.single i 1)|≤2 := by
      have H : |inner ℝ x (EuclideanSpace.single i 1)|≤‖x‖ := by
        simpa using abs_real_inner_le_norm x (EuclideanSpace.single i (1:ℝ))
      exact H.trans hx2
    change |(2-(n:ℝ))*‖x‖^(-(n:ℝ))*inner ℝ x (EuclideanSpace.single i 1)|≤_
    rw [abs_mul,abs_mul,abs_of_nonneg (Real.rpow_nonneg (norm_nonneg x) _)]
    exact (mul_le_mul (mul_le_mul_of_nonneg_left hp (abs_nonneg _)) hi (abs_nonneg _) (by positivity)).trans_eq (by ring)
  have hEach (i : Fin n) : ‖-w • C i-b i • u‖^2≤2*‖C i‖^2+8*|2-(n:ℝ)|^2*‖u‖^2 := by
    have hFirst : ‖-w • C i‖≤‖C i‖ := by
      rw [norm_smul,Real.norm_eq_abs,abs_neg,abs_of_nonneg hw0]
      exact (mul_le_mul_of_nonneg_right hw1 (norm_nonneg _)).trans_eq (one_mul _)
    have hSecond : ‖b i • u‖≤(2*|2-(n:ℝ)|)*‖u‖ := by
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right (hb i) (norm_nonneg _)
    have H₁ := pow_le_pow_left₀ (norm_nonneg _) hFirst 2
    have H₂ := pow_le_pow_left₀ (norm_nonneg _) hSecond 2
    have H := norm_sub_sq_le_two (-w • C i) (b i • u)
    rw [mul_pow,mul_pow] at H₂
    nlinarith only [H,H₁,H₂]
  calc
    _ ≤ ∑i : Fin n,(2*‖C i‖^2+8*|2-(n:ℝ)|^2*‖u‖^2) := Finset.sum_le_sum (fun i _=>hEach i)
    _ = 2*hsNormSq C+(8*(n:ℝ)*|2-(n:ℝ)|^2)*‖u‖^2 := by
      rw [Finset.sum_add_distrib,← Finset.mul_sum]
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,hsNormSq]
      ring
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hC (by norm_num : (0:ℝ)≤2)) le_rfl

/-- Actual native W0 unit-ball data give a uniform local gradient-energy bound for their literal odd Kelvin reflection on every sphere-centered query ball of radius at most one. -/
theorem exists_odd_kelvin_boundary_gradient_energy_bound (n : ℕ) (hn : 2≤n) :
    ∃ K : ℝ,0<K ∧ ∀ (q : ℕ) (u : Domain n → Ambient q) (Du : Domain n → Gradient n q),
      HasZeroBoundaryValues (ballDomain (0 : Domain n) 1) u Du →
      ∀ (a : Domain n),‖a‖=1 → ∀ (r : ℝ),0<r → r≤1 →
        let I := inversion (0 : Domain n) 1
        let w := fun x : Domain n=>‖x‖^(2-(n:ℝ))
        let C := fun x i=>∑j : Fin n,(fderiv ℝ I x (EuclideanSpace.single i 1)) j • Du (I x) j
        let DU := fun (x : Domain n) (i : Fin n)=>if ‖x‖≤1 then Du x i else
          -w x • C x i-((2-(n:ℝ))*‖x‖^(-(n:ℝ))*inner ℝ x (EuclideanSpace.single i 1)) • u (I x)
        let D₀ := fun x i=>(Metric.ball (0 : Domain n) 1).indicator (fun y=>Du y i) x
        IntegrableOn (fun x=>hsNormSq (DU x)) (Metric.ball a r) volume ∧
          (∫ x in Metric.ball a r,hsNormSq (DU x))≤K*(∫ x in Metric.ball a r,hsNormSq (D₀ x)) := by
  let B : ℝ := (2 : ℝ)^(2*n)
  let P : ℝ := (1+(4 : ℝ)^n)*(2 : ℝ)^(n+1)
  let L : ℝ := 8*(n:ℝ)*|2-(n:ℝ)|^2
  let K := 1+B*(2+L*P)
  have hB : 0<B := by dsimp only [B];positivity
  have hP : 0≤P := by dsimp only [P];positivity
  have hL : 0≤L := by dsimp only [L];positivity
  refine ⟨K,by dsimp only [K];positivity,?_⟩
  intro q u Du hu a ha r hr hr1 I w C DU D₀
  let Q := Metric.ball a r
  let S := Q∩{x : Domain n | 1<‖x‖}
  let μ := volume.restrict Q
  let ν := volume.restrict S
  let U₀ := (Metric.ball (0 : Domain n) 1).indicator u
  have hS : MeasurableSet S := measurableSet_ball.inter (isOpen_lt continuous_const continuous_norm).measurableSet
  have hUpper (x : Domain n) (hx : x∈Q) : ‖x‖≤2 := by
    have H := dist_triangle x a (0 : Domain n)
    rw [dist_zero_right,dist_zero_right,ha] at H
    have hDist : dist x a<r := hx
    linarith
  have hS0 (x : Domain n) (hx : x∈S) : x≠0 := norm_pos_iff.mp (zero_lt_one.trans hx.2)
  have hImageSub : I '' S⊆Q∩Metric.ball (0 : Domain n) 1 :=
    unit_inversion_image_exterior_boundary_ball_subset a ha r
  have hInvImage : I '' S=I ⁻¹' S := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      simpa only [mem_preimage,I,inversion_inversion _ (by norm_num : (1:ℝ)≠0)] using hx
    · intro hy
      exact ⟨I y,hy,inversion_inversion _ (by norm_num : (1:ℝ)≠0) _⟩
  have hImageMeas : MeasurableSet (I '' S) := by rw [hInvImage];exact hS.preimage (measurable_unit_inversion n)
  have hMeasure : volume.restrict (I '' S)≤volume.restrict (Metric.ball (0 : Domain n) 1) :=
    Measure.restrict_mono_set volume (hImageSub.trans inter_subset_right)
  have hPullU := unit_inversion_L2_transport_bounded_set S hS hS0 2 (by norm_num)
    (fun x hx=>hUpper x hx.1) u (hu.1.2.1.mono_measure hMeasure)
  have hPullD (j : Fin n) := unit_inversion_L2_transport_bounded_set S hS hS0 2 (by norm_num)
    (fun x hx=>hUpper x hx.1) (fun y=>Du y j) ((hu.1.2.2 j).mono_measure hMeasure)
  obtain ⟨hZeroNative,hPoincare⟩ := zeroBoundary_zeroExtension_boundary_poincare u Du hu a ha r hr
  have hD₀I : Integrable (fun x=>hsNormSq (D₀ x)) μ := hZeroNative.integrable_hsNormSq
  have hU₀I : Integrable (fun x=>‖U₀ x‖^2) μ := hZeroNative.2.1.integrable_norm_pow (by decide : (2:ℕ)≠0)
  have hOriginalGrad : (∫ y in I '' S,hsNormSq (Du y))≤∫ x,hsNormSq (D₀ x) ∂μ := by
    calc
      _ = ∫ y in I '' S,hsNormSq (D₀ y) := by
        apply setIntegral_congr_fun hImageMeas
        intro y hy
        simp only [D₀,indicator_of_mem (hImageSub hy).2]
      _ ≤ _ := setIntegral_mono_set hD₀I (Eventually.of_forall fun _=>hsNormSq_nonneg _)
        (Eventually.of_forall fun _ hy=>(hImageSub hy).1)
  have hOriginalMap : (∫ y in I '' S,‖u y‖^2)≤∫ x,‖U₀ x‖^2 ∂μ := by
    calc
      _ = ∫ y in I '' S,‖U₀ y‖^2 := by
        apply setIntegral_congr_fun hImageMeas
        intro y hy
        change ‖u y‖^2=‖U₀ y‖^2
        rw [show U₀ y=u y from indicator_of_mem (hImageSub hy).2 u]
      _ ≤ _ := setIntegral_mono_set hU₀I (Eventually.of_forall fun _=>sq_nonneg _)
        (Eventually.of_forall fun _ hy=>(hImageSub hy).1)
  have hPullGradI : Integrable (fun x=>hsNormSq (Du (I x))) ν :=
    integrable_finsetSum _ (fun j _=>(hPullD j).1.integrable_norm_pow (by decide : (2:ℕ)≠0))
  have hPullGrad : (∫ x,hsNormSq (Du (I x)) ∂ν)≤B*(∫ x,hsNormSq (D₀ x) ∂μ) := by
    calc
      _ ≤ B*(∫ y in I '' S,hsNormSq (Du y)) := by
        change (∫ x,∑j : Fin n,‖Du (I x) j‖^2 ∂ν)≤B*(∫ y in I '' S,∑j : Fin n,‖Du y j‖^2)
        rw [integral_finsetSum _ (fun j _=>(hPullD j).1.integrable_norm_pow (by decide : (2:ℕ)≠0)),
          integral_finsetSum _ (fun j _=>((hu.1.2.2 j).mono_measure hMeasure).integrable_norm_pow (by decide : (2:ℕ)≠0)),Finset.mul_sum]
        exact Finset.sum_le_sum (fun j _=>(hPullD j).2)
      _ ≤ _ := mul_le_mul_of_nonneg_left hOriginalGrad hB.le
  have hPoincare' : (∫ x,‖U₀ x‖^2 ∂μ)≤P*(∫ x,hsNormSq (D₀ x) ∂μ) := by
    have hrSq : r^2≤1 := pow_le_one₀ hr.le hr1
    calc
      _ ≤ P*r^2*(∫ x,hsNormSq (D₀ x) ∂μ) := by simpa only [P,mul_assoc] using hPoincare
      _ ≤ _ := mul_le_mul_of_nonneg_right
        ((mul_le_mul_of_nonneg_left hrSq hP).trans_eq (mul_one _)) (integral_nonneg fun _=>hsNormSq_nonneg _)
  have hPullMap : (∫ x,‖u (I x)‖^2 ∂ν)≤B*P*(∫ x,hsNormSq (D₀ x) ∂μ) := by
    exact hPullU.2.trans ((mul_le_mul_of_nonneg_left (hOriginalMap.trans hPoincare') hB.le).trans_eq (by ring))
  let G := fun x=>2*hsNormSq (Du (I x))+L*‖u (I x)‖^2
  have hGI : Integrable G ν := (hPullGradI.const_mul 2).add
    ((hPullU.1.integrable_norm_pow (by decide : (2:ℕ)≠0)).const_mul L)
  have hIndicatorI : Integrable (S.indicator G) μ :=
    ((integrable_indicator_iff hS).mpr hGI).mono_measure Measure.restrict_le_self
  have hLeftI : Integrable (fun x=>hsNormSq (DU x)) μ := by
    have H := memW12_odd_kelvin_extension_ball hn 3 (by norm_num) u Du hu
    have hClosed : Metric.closedBall a r⊆Metric.ball (0 : Domain n) 3 := by
      intro x hx
      have H := dist_triangle x a (0 : Domain n)
      rw [dist_zero_right,dist_zero_right,ha] at H
      have hd : dist x a≤r := hx
      rw [Metric.mem_ball,dist_zero_right]
      linarith
    exact (H.to_memW12Loc.memW12_ball hClosed).integrable_hsNormSq
  have hSphere : ∀ᵐ x : Domain n ∂volume,‖x‖≠1 := by
    filter_upwards [HarmonicMaps.ball_ae_eq_closedBall (0 : Domain n) (by norm_num : (0:ℝ)<1)] with x hx
    intro hxNorm
    have hCB : x∈Metric.closedBall (0 : Domain n) 1 := by rw [Metric.mem_closedBall,dist_zero_right,hxNorm]
    have hBall : x∈Metric.ball (0 : Domain n) 1 := Eq.mpr hx hCB
    rw [Metric.mem_ball,dist_zero_right,hxNorm] at hBall
    exact (lt_irrefl (1:ℝ)) hBall
  have hPoint : ∀ᵐ x ∂μ,hsNormSq (DU x)≤hsNormSq (D₀ x)+S.indicator G x := by
    filter_upwards [ae_restrict_mem measurableSet_ball,ae_restrict_of_ae hSphere] with x hxQ hxNorm
    by_cases hxIn : ‖x‖<1
    · have hxBall : x∈Metric.ball (0 : Domain n) 1 := by simpa only [Metric.mem_ball,dist_zero_right] using hxIn
      have hxS : x∉S := fun h=>not_lt_of_ge hxIn.le h.2
      simp only [DU,if_pos hxIn.le,D₀,indicator_of_mem hxBall,indicator_of_notMem hxS,add_zero,le_refl]
    · have hxOut : 1<‖x‖ := lt_of_le_of_ne (le_of_not_gt hxIn) hxNorm.symm
      have hxBall : x∉Metric.ball (0 : Domain n) 1 := by simpa only [Metric.mem_ball,dist_zero_right,not_lt] using hxOut.le
      have hxS : x∈S := ⟨hxQ,hxOut⟩
      simpa only [DU,if_neg (not_le.mpr hxOut),D₀,indicator_of_notMem hxBall,
        hsNormSq,norm_zero,zero_pow (by decide : (2:ℕ)≠0),Finset.sum_const_zero,zero_add,
        indicator_of_mem hxS,G,L,C,w] using odd_kelvin_gradient_hs_bound hn x hxOut.le (hUpper x hxQ) (u (I x)) (Du (I x))
  have hIndicatorEq : (∫ x,S.indicator G x ∂μ)=∫ x,G x ∂ν := by
    rw [integral_indicator hS,show μ.restrict S=ν from by
      rw [Measure.restrict_restrict hS,inter_eq_left.mpr inter_subset_left]]
  refine ⟨hLeftI,?_⟩
  calc
    _ ≤ ∫ x,hsNormSq (D₀ x)+S.indicator G x ∂μ := integral_mono_ae hLeftI (hD₀I.add hIndicatorI) hPoint
    _ = (∫ x,hsNormSq (D₀ x) ∂μ)+(2*(∫ x,hsNormSq (Du (I x)) ∂ν)+L*(∫ x,‖u (I x)‖^2 ∂ν)) := by
      rw [integral_add hD₀I hIndicatorI,hIndicatorEq,integral_add (hPullGradI.const_mul 2)
        ((hPullU.1.integrable_norm_pow (by decide : (2:ℕ)≠0)).const_mul L),integral_const_mul,integral_const_mul]
    _ ≤ (∫ x,hsNormSq (D₀ x) ∂μ)+(2*(B*(∫ x,hsNormSq (D₀ x) ∂μ))+L*(B*P*(∫ x,hsNormSq (D₀ x) ∂μ))) :=
      add_le_add le_rfl (add_le_add (mul_le_mul_of_nonneg_left hPullGrad (by norm_num))
        (mul_le_mul_of_nonneg_left hPullMap hL))
    _ = _ := by dsimp only [K];ring

end StationaryHarmonicMaps.Analysis

end
