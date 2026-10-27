module

public import StationaryHarmonicMaps.Analysis.NeumannKelvinReflection

/-!
# Actual derivatives of the Neumann Kelvin reflection

Differentiation in the direction parameter keeps the original derivative
inside the genuine radial integral. The radial and direction identities
then determine the derivative of the actual spatial reflection.
-/

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped ContDiff Topology

namespace StationaryHarmonicMaps.Analysis

/-- The original ray has the actual Fréchet derivative in its direction parameter. -/
theorem neumannKelvinRay_hasFDerivAt_direction {n q : ℕ}
    (upper : ℝ) (hUpper : 0 < upper) (u : Domain n → Ambient q) (hu : ContDiff ℝ ∞ u)
    (r : ℝ) (hr : 0 < r) (θ : Domain n) :
    HasFDerivAt (fun z : Domain n => neumannKelvinRay upper u z r)
      (r ^ (1-(n : ℝ)) • fderiv ℝ u (r⁻¹ • θ) + ((n : ℝ)-2) •
        (∫ t in r⁻¹..upper, t ^ ((n : ℝ)-2) • fderiv ℝ u (t • θ))) θ := by
  let τ := fun s : ℝ => r⁻¹+(upper-r⁻¹)*s
  let W : Set (Domain n × ℝ) := {p | 0 < τ p.2}
  let J := fun p : Domain n × ℝ =>
    (upper-r⁻¹) • ((τ p.2) ^ ((n : ℝ)-3) • u ((τ p.2) • p.1))
  have hτ : ContDiff ℝ ∞ τ := contDiff_const.add (contDiff_const.mul contDiff_id)
  have hW : IsOpen W := isOpen_lt continuous_const (hτ.continuous.comp continuous_snd)
  have hPairs : ∀ z ∈ (univ : Set (Domain n)), ∀ s : Icc (0 : ℝ) 1, (z, (s : ℝ)) ∈ W :=
    fun _ _ s => positive_neumann_radial_interpolation upper hUpper r hr s
  have hJ : ContDiffOn ℝ ∞ J W := by
    intro p hp
    exact (((((hτ.comp contDiff_snd).contDiffAt.rpow_const_of_ne hp.ne').smul
      (hu.contDiffAt.comp p (((hτ.comp contDiff_snd).contDiffAt).smul contDiffAt_fst))).const_smul
        (upper-r⁻¹))).contDiffWithinAt
  have HI := compactParametricIntegral_hasFDerivAt (volume : Measure (Icc (0 : ℝ) 1))
    (fun s : Icc (0 : ℝ) 1 => (s : ℝ)) continuous_subtype_val
    univ isOpen_univ W hW hPairs J hJ θ (mem_univ θ)
  have hPartial (s : Icc (0 : ℝ) 1) :
      (fderiv ℝ J (θ, (s : ℝ))).comp (ContinuousLinearMap.inl ℝ (Domain n) ℝ) =
        (upper-r⁻¹) • ((τ s) ^ ((n : ℝ)-2) • fderiv ℝ u ((τ s) • θ)) := by
    have ht : 0 < τ s := positive_neumann_radial_interpolation upper hUpper r hr s
    have hSlice := (((hu.differentiable (by simp) ((τ s) • θ)).hasFDerivAt.comp θ
      ((hasFDerivAt_id (𝕜 := ℝ) θ).const_smul (τ s))).const_smul
        ((τ s) ^ ((n : ℝ)-3))).const_smul (upper-r⁻¹)
    have hWeight : (τ s) ^ ((n : ℝ)-3) * τ s = (τ s) ^ ((n : ℝ)-2) := by
      calc
        _ = (τ s) ^ ((n : ℝ)-3) * (τ s) ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = (τ s) ^ (((n : ℝ)-3)+1) := (Real.rpow_add ht _ _).symm
        _ = _ := by congr 1; ring
    have hEq : (upper-r⁻¹) • ((τ s) ^ ((n : ℝ)-3) •
        ((fderiv ℝ u ((τ s) • θ)).comp ((τ s) • ContinuousLinearMap.id ℝ (Domain n)))) =
          (upper-r⁻¹) • ((τ s) ^ ((n : ℝ)-2) • fderiv ℝ u ((τ s) • θ)) := by
      apply ContinuousLinearMap.ext
      intro v
      simp only [smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, map_smul, smul_smul]
      rw [mul_assoc, hWeight]
    rw [hEq] at hSlice
    have hJD := (hJ.contDiffAt (hW.mem_nhds (hPairs θ (mem_univ θ) s))).differentiableAt (by simp)
    have hPair : HasFDerivAt (fun z : Domain n => (z, (s : ℝ)))
        (ContinuousLinearMap.inl ℝ (Domain n) ℝ) θ := hasFDerivAt_prodMk_left θ (s : ℝ)
    have HJ := hJD.hasFDerivAt.comp θ hPair
    exact HJ.unique hSlice
  have hIntegral : (∫ s : Icc (0 : ℝ) 1,
      (fderiv ℝ J (θ, (s : ℝ))).comp (ContinuousLinearMap.inl ℝ (Domain n) ℝ)) =
      ∫ t in r⁻¹..upper, t ^ ((n : ℝ)-2) • fderiv ℝ u (t • θ) := by
    rw [integral_congr_ae (Eventually.of_forall hPartial)]
    exact (neumann_radial_intervalIntegral_affine_unit
      (fun t => t ^ ((n : ℝ)-2) • fderiv ℝ u (t • θ)) r⁻¹ upper).symm
  rw [hIntegral] at HI
  have HFirst := ((hu.differentiable (by simp) (r⁻¹ • θ)).hasFDerivAt.comp θ
    ((hasFDerivAt_id (𝕜 := ℝ) θ).const_smul r⁻¹)).const_smul (r ^ (2-(n : ℝ)))
  have hWeight : r ^ (2-(n : ℝ)) * r⁻¹ = r ^ (1-(n : ℝ)) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hr]
    congr 1
    ring
  have hFirstEq : r ^ (2-(n : ℝ)) • ((fderiv ℝ u (r⁻¹ • θ)).comp
      (r⁻¹ • ContinuousLinearMap.id ℝ (Domain n))) = r ^ (1-(n : ℝ)) • fderiv ℝ u (r⁻¹ • θ) := by
    ext v
    simp only [smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, map_smul]
    rw [← mul_smul, hWeight]
  rw [hFirstEq] at HFirst
  have H := HFirst.add (HI.const_smul ((n : ℝ)-2))
  apply H.congr_of_eventuallyEq
  exact Eventually.of_forall fun z => neumannKelvinRay_eq_compactIntegral upper u z r


/-- The joint derivative is the sum of the actual direction and radial derivatives. -/
theorem neumannKelvinRay_joint_fderiv_apply {n q : ℕ}
    (upper : ℝ) (hUpper : 0 < upper) (u : Domain n → Ambient q) (hu : ContDiff ℝ ∞ u)
    (r : ℝ) (hr : 0 < r) (θ v : Domain n) (s : ℝ) :
    fderiv ℝ (fun z : Domain n × ℝ => neumannKelvinRay upper u z.1 z.2) (θ,r) (v,s) =
      r ^ (1-(n : ℝ)) • fderiv ℝ u (r⁻¹ • θ) v + ((n : ℝ)-2) •
        (∫ t in r⁻¹..upper, t ^ ((n : ℝ)-2) • fderiv ℝ u (t • θ) v) -
      (s * r ^ (-(n : ℝ))) • fderiv ℝ u (r⁻¹ • θ) θ := by
  let F := fun z : Domain n × ℝ => neumannKelvinRay upper u z.1 z.2
  have hOpen : IsOpen ({z : Domain n × ℝ | 0 < z.2}) := isOpen_lt continuous_const continuous_snd
  have hIn : (θ,r) ∈ {z : Domain n × ℝ | 0 < z.2} := hr
  have hF : HasFDerivAt F (fderiv ℝ F (θ,r)) (θ,r) :=
    ((neumannKelvinRay_contDiffOn upper hUpper u hu).contDiffAt
      (hOpen.mem_nhds hIn)).differentiableAt (by simp) |>.hasFDerivAt
  have hLeft : (fderiv ℝ F (θ,r)).comp (ContinuousLinearMap.inl ℝ (Domain n) ℝ) =
      r ^ (1-(n : ℝ)) • fderiv ℝ u (r⁻¹ • θ) + ((n : ℝ)-2) •
        (∫ t in r⁻¹..upper, t ^ ((n : ℝ)-2) • fderiv ℝ u (t • θ)) := by
    have hPair : HasFDerivAt (fun z : Domain n => (z,r))
        (ContinuousLinearMap.inl ℝ (Domain n) ℝ) θ := hasFDerivAt_prodMk_left θ r
    have H := hF.comp θ hPair
    exact H.unique (neumannKelvinRay_hasFDerivAt_direction upper hUpper u hu r hr θ)
  have hRight : fderiv ℝ F (θ,r) (0,1) =
      (-(r ^ (-(n : ℝ)))) • fderiv ℝ u (r⁻¹ • θ) θ := by
    have Hcurve : HasDerivAt (fun z : ℝ => (θ,z)) (0,1) r :=
      (hasDerivAt_const r θ).prodMk (hasDerivAt_id r)
    have HR := hF.comp_hasDerivAt r Hcurve
    exact HR.unique (neumannKelvinRay_hasDerivAt upper hUpper u hu θ r hr)
  have hInt : IntervalIntegrable (fun t : ℝ =>
      t ^ ((n : ℝ)-2) • fderiv ℝ u (t • θ)) volume r⁻¹ upper := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    have htpos : 0 < t := (lt_min (inv_pos.mpr hr) hUpper).trans_le ht.1
    exact ((Real.continuousAt_rpow_const t ((n : ℝ)-2) (Or.inl htpos.ne')).smul
      ((hu.continuous_fderiv (by simp)).continuousAt.comp
        (continuousAt_id.smul continuousAt_const))).continuousWithinAt
  have hLeftApply := congrArg (fun L : Domain n →L[ℝ] Ambient q => L v) hLeft
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply, add_apply, smul_apply,
    ContinuousLinearMap.intervalIntegral_apply hInt] at hLeftApply
  have hVS : (v,s) = (v,0) + s • ((0,1) : Domain n × ℝ) := by
    simp only [Prod.smul_mk, smul_zero, smul_eq_mul, mul_one, Prod.mk_add_mk, add_zero, zero_add]
  change fderiv ℝ F (θ,r) (v,s) = _
  rw [hVS, map_add, map_smul, hLeftApply, hRight]
  simp only [neg_smul, smul_neg, smul_smul, sub_eq_add_neg]


/-- The genuine spatial reflection has the original inversion derivative and its tangential radial correction, with no map-value term. -/
theorem neumannKelvinReflection_fderiv_apply {n q : ℕ}
    (upper : ℝ) (hUpper : 0 < upper) (u : Domain n → Ambient q) (hu : ContDiff ℝ ∞ u)
    (x v : Domain n) (hx : x ≠ 0) :
    let r := ‖x‖
    let θ := r⁻¹ • x
    let vT := v - (inner ℝ θ v) • θ
    fderiv ℝ (fun y : Domain n => neumannKelvinRay upper u (‖y‖⁻¹ • y) ‖y‖) x v =
      r ^ (-(n : ℝ)) • fderiv ℝ u (r⁻¹ • θ) (v - (2 * inner ℝ θ v) • θ) +
        (((n : ℝ)-2)/r) •
          (∫ t in r⁻¹..upper, t ^ ((n : ℝ)-2) • fderiv ℝ u (t • θ) vT) := by
  intro r θ vT
  have hr : 0 < r := norm_pos_iff.mpr hx
  have hR : HasFDerivAt (fun y : Domain n => ‖y‖) (r⁻¹ • innerSL ℝ x) x := by
    have H := hasFDerivAt_norm_real_power_of_ne_zero 1 x hx
    simpa only [Real.rpow_one, one_mul, show (1 : ℝ)-2 = -1 by ring, Real.rpow_neg_one] using H
  have hRI : HasFDerivAt (fun y : Domain n => ‖y‖⁻¹)
      (-(r ^ (-3 : ℝ)) • innerSL ℝ x) x := by
    have H := hasFDerivAt_norm_real_power_of_ne_zero (-1) x hx
    simpa only [Real.rpow_neg_one, neg_one_mul, show (-1 : ℝ)-2 = -3 by ring] using H
  have hDirection := hRI.smul (hasFDerivAt_id (𝕜 := ℝ) x)
  have hPair := hDirection.prodMk hR
  let F := fun z : Domain n × ℝ => neumannKelvinRay upper u z.1 z.2
  have hOpen : IsOpen ({z : Domain n × ℝ | 0 < z.2}) := isOpen_lt continuous_const continuous_snd
  have hIn : (θ,r) ∈ {z : Domain n × ℝ | 0 < z.2} := hr
  have hF : HasFDerivAt F (fderiv ℝ F (θ,r)) (θ,r) :=
    ((neumannKelvinRay_contDiffOn upper hUpper u hu).contDiffAt
      (hOpen.mem_nhds hIn)).differentiableAt (by simp) |>.hasFDerivAt
  have HC := (hF.comp x hPair).fderiv
  have hThetaFn : ((fun y : Domain n => ‖y‖⁻¹) • (id : Domain n → Domain n)) =
      (fun y : Domain n => ‖y‖⁻¹ • y) := by funext y; rfl
  rw [hThetaFn] at HC
  have hTriple : r ^ (-3 : ℝ) = r⁻¹ * r⁻¹ * r⁻¹ := by
    rw [Real.rpow_neg hr.le, Real.rpow_ofNat]
    simp only [pow_succ, pow_zero, one_mul, mul_inv_rev]
    ring
  have hRadial : (r⁻¹ • innerSL ℝ x) v = inner ℝ θ v := by
    simp only [θ, smul_apply, innerSL_apply_apply, real_inner_smul_left, smul_eq_mul]
  have hTangent : (‖x‖⁻¹ • ContinuousLinearMap.id ℝ (Domain n) +
      (-(r ^ (-3 : ℝ)) • innerSL ℝ x).smulRight x) v = r⁻¹ • vT := by
    simp only [vT, θ, add_apply, smul_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, real_inner_smul_left,
      smul_sub, smul_smul, hTriple]
    change r⁻¹ • v + (-(r⁻¹*r⁻¹*r⁻¹)*inner ℝ x v) • x =
      r⁻¹ • v - (r⁻¹ * (r⁻¹ * inner ℝ x v * r⁻¹)) • x
    module
  have hComp : fderiv ℝ (fun y : Domain n => neumannKelvinRay upper u (‖y‖⁻¹ • y) ‖y‖) x v =
      fderiv ℝ F (θ,r) (r⁻¹ • vT, inner ℝ θ v) := by
    have H := congrArg (fun L : Domain n →L[ℝ] Ambient q => L v) HC
    simpa only [Function.comp_def, F, id_eq, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.prod_apply, hTangent, hRadial] using H
  rw [hComp, neumannKelvinRay_joint_fderiv_apply upper hUpper u hu r hr θ (r⁻¹ • vT) (inner ℝ θ v)]
  have hPower : r ^ (1-(n : ℝ)) * r⁻¹ = r ^ (-(n : ℝ)) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hr]
    congr 1
    ring
  have hInt : (∫ t in r⁻¹..upper, t ^ ((n : ℝ)-2) • fderiv ℝ u (t • θ) (r⁻¹ • vT)) =
      r⁻¹ • (∫ t in r⁻¹..upper, t ^ ((n : ℝ)-2) • fderiv ℝ u (t • θ) vT) := by
    have hPoint (t : ℝ) : t ^ ((n : ℝ)-2) • fderiv ℝ u (t • θ) (r⁻¹ • vT) =
        r⁻¹ • (t ^ ((n : ℝ)-2) • fderiv ℝ u (t • θ) vT) := by
      rw [map_smul, smul_comm]
    rw [intervalIntegral.integral_congr (fun t _ => hPoint t), intervalIntegral.integral_smul]
  rw [map_smul, ← mul_smul, hPower, hInt]
  simp only [vT, map_sub, map_smul, smul_sub, smul_smul, div_eq_mul_inv]
  module

end StationaryHarmonicMaps.Analysis

end
