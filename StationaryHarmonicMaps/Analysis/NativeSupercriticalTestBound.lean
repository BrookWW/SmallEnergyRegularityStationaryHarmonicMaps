module

public import StationaryHarmonicMaps.Analysis.SupercriticalGradientGrowth
public import StationaryHarmonicMaps.Analysis.ZeroBoundaryZeroExtension
public import StationaryHarmonicMaps.Analysis.LpMorreyRepresentative
public import StationaryHarmonicMaps.Analysis.EffectiveHolderConstants
public import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Actual native zero-boundary supercritical tests

The original W0 graph has a genuine full-space zero extension. Original
higher-Lp columns give the actual full HS growth. The proved global
Campanato representative applies at quadratic exponent. Its continuous
representative is zero at an actual exterior anchor by AE uniqueness on
an open ball. The same representative bound returns to the original
map almost everywhere on its original ball, with the correct radius
power and a constant chosen before target dimension.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- Original native W0 data and actual supercritical Ls columns produce the same original test's essential bound and true L-infinity membership. -/

@[expose] noncomputable def nativeZeroBoundarySupercriticalConstant (n : ℕ) (s : ℝ) : ℝ :=
  globalLpMorreyRepresentativeConstant n 2 (1-(n : ℝ)/s) *
    (volume.real (Metric.ball (0 : Domain n) 1))^((1/2 : ℝ)-1/s) *
      (4 : ℝ)^(1-(n : ℝ)/s)

@[expose] def nativeZeroBoundaryFixedSupercriticalMajorant (n : ℕ) : ℕ :=
  4 * explicitLpMorreyRepresentativeMajorant n * (1 + 2^n)

theorem nativeZeroBoundarySupercriticalConstant_uniform_le (n : ℕ) (hn : 2 ≤ n)
    (s : ℝ) (hsn : (n : ℝ) < s) (hHalf : (1/2 : ℝ) ≤ 1-(n : ℝ)/s) :
    nativeZeroBoundarySupercriticalConstant n s ≤
      (nativeZeroBoundaryFixedSupercriticalMajorant n : ℝ) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  let α : ℝ := 1-(n : ℝ)/s
  let V : ℝ := volume.real (Metric.ball (0 : Domain n) 1)
  have hs : 0 < s := by linarith only [hnR, hsn]
  have hαHalf : (1/2 : ℝ) ≤ α := hHalf
  have hαOne : α ≤ 1 := by
    dsimp only [α]
    linarith only [div_nonneg (Nat.cast_nonneg n) hs.le]
  have hC := globalLpMorreyRepresentativeConstant_le_of_half_le n 2 α (by norm_num) hαHalf hαOne
  have ht0 : 0 ≤ (1/2 : ℝ)-1/s := by
    have H : 1/s ≤ (1/2 : ℝ) := (div_le_iff₀ hs).mpr (by linarith only [hnR, hsn])
    linarith only [H]
  have ht1 : (1/2 : ℝ)-1/s ≤ 1 := by have H := one_div_pos.mpr hs; linarith only [H]
  have hV : 0 ≤ V := measureReal_nonneg
  have hVpow : V^((1/2 : ℝ)-1/s) ≤ 1+(2 : ℝ)^n := by
    by_cases hOne : V ≤ 1
    · exact (Real.rpow_le_one hV hOne ht0).trans (le_add_of_nonneg_right (by positivity))
    · exact (Real.rpow_le_self_of_one_le (not_le.mp hOne).le ht1).trans
        ((euclidean_unit_ball_volume_upper_bound n).trans (by linarith only [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) n]))
  have hfour : (4 : ℝ)^α ≤ 4 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 4) hαOne
  have H := mul_le_mul (mul_le_mul hC hVpow (Real.rpow_nonneg hV _)
    (by positivity : 0 ≤ (explicitLpMorreyRepresentativeMajorant n : ℝ))) hfour
    (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 4) α) (by positivity)
  change globalLpMorreyRepresentativeConstant n 2 α * V^((1/2 : ℝ)-1/s) * (4 : ℝ)^α ≤ _
  calc
    _ ≤ (explicitLpMorreyRepresentativeMajorant n : ℝ)*(1+(2 : ℝ)^n)*4 := H
    _ = _ := by unfold nativeZeroBoundaryFixedSupercriticalMajorant; push_cast; ring

theorem nativeZeroBoundarySupercriticalConstant_fixed_le (n : ℕ) (hn : 2 ≤ n) :
    nativeZeroBoundarySupercriticalConstant n (2*(n : ℝ)+1) ≤
      (nativeZeroBoundaryFixedSupercriticalMajorant n : ℝ) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  let s : ℝ := 2*(n : ℝ)+1
  let α : ℝ := 1-(n : ℝ)/s
  let V : ℝ := volume.real (Metric.ball (0 : Domain n) 1)
  have hs : 0 < s := by dsimp only [s]; linarith only [hnR]
  have hαHalf : (1/2 : ℝ) ≤ α := by
    dsimp only [α]
    have H : (n : ℝ)/s ≤ 1/2 := (div_le_iff₀ hs).mpr (by dsimp only [s]; linarith)
    linarith only [H]
  have hαOne : α ≤ 1 := by
    dsimp only [α]
    linarith only [div_nonneg (Nat.cast_nonneg n) hs.le]
  have hC := globalLpMorreyRepresentativeConstant_le_of_half_le n 2 α (by norm_num) hαHalf hαOne
  have ht0 : 0 ≤ (1/2 : ℝ)-1/s := by
    have H : 1/s ≤ (1/2 : ℝ) := (div_le_iff₀ hs).mpr (by dsimp only [s]; linarith only [hnR])
    linarith only [H]
  have ht1 : (1/2 : ℝ)-1/s ≤ 1 := by have H := one_div_pos.mpr hs; linarith only [H]
  have hV : 0 ≤ V := measureReal_nonneg
  have hVpow : V^((1/2 : ℝ)-1/s) ≤ 1+(2 : ℝ)^n := by
    by_cases hOne : V ≤ 1
    · exact (Real.rpow_le_one hV hOne ht0).trans (le_add_of_nonneg_right (by positivity))
    · exact (Real.rpow_le_self_of_one_le (not_le.mp hOne).le ht1).trans
        ((euclidean_unit_ball_volume_upper_bound n).trans (by linarith only [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) n]))
  have hfour : (4 : ℝ)^α ≤ 4 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 4) hαOne
  have H := mul_le_mul (mul_le_mul hC hVpow (Real.rpow_nonneg hV _)
    (by positivity : 0 ≤ (explicitLpMorreyRepresentativeMajorant n : ℝ))) hfour
    (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 4) α) (by positivity)
  change globalLpMorreyRepresentativeConstant n 2 α * V^((1/2 : ℝ)-1/s) * (4 : ℝ)^α ≤ _
  calc
    _ ≤ (explicitLpMorreyRepresentativeMajorant n : ℝ)*(1+(2 : ℝ)^n)*4 := H
    _ = _ := by unfold nativeZeroBoundaryFixedSupercriticalMajorant; push_cast; ring

theorem exists_native_zeroBoundary_supercritical_bound_explicit (n : ℕ) (hn : 2≤n)
    (s : ℝ) (hsn : (n : ℝ)<s) :
    ∃ C : ℝ,0<C ∧ C = nativeZeroBoundarySupercriticalConstant n s ∧ ∀ (q : ℕ) (a : Domain n) (R : ℝ)
      (u : Domain n → Ambient q) (Du : Domain n → Gradient n q),0<R →
      HasZeroBoundaryValues (ballDomain a R) u Du →
      (∀ i,MemLp (fun x=>Du x i) (ENNReal.ofReal s) (volume.restrict (Metric.ball a R))) →
      IntegrableOn (fun x=>(Real.sqrt (hsNormSq (Du x)))^s) (Metric.ball a R) volume ∧
        (∀ᵐ x ∂volume.restrict (Metric.ball a R),‖u x‖≤
          C*R^(1-(n : ℝ)/s)*(∫ y in Metric.ball a R,(Real.sqrt (hsNormSq (Du y)))^s)^(1/s)) ∧
        MemLp u ⊤ (volume.restrict (Metric.ball a R)) := by
  have hnReal : (2 : ℝ)≤n := by exact_mod_cast hn
  have hs2 : 2≤s := hnReal.trans hsn.le
  have hs0 : 0<s := lt_of_lt_of_le (by norm_num : (0 : ℝ)<2) hs2
  have hn0 : (0 : ℝ)<n := lt_of_lt_of_le (by norm_num : (0 : ℝ)<2) hnReal
  let α := 1-(n : ℝ)/s
  have hα : 0<α := sub_pos.mpr ((div_lt_one hs0).mpr hsn)
  have hαOne : α<1 := by dsimp only [α];linarith [div_pos hn0 hs0]
  let V := volume.real (Metric.ball (0 : Domain n) 1)
  have hV : 0<V := HolderToCK.ball_volume_real_pos 0 (by norm_num)
  obtain ⟨C₀,hC₀,hC₀Formula,Hrep⟩ := existsUnique_continuous_representative_of_lp_gradient_growth_explicit n 2 α
    (by norm_num) le_rfl hα hαOne
  let C := C₀*V^((1/2 : ℝ)-1/s)*(4 : ℝ)^α
  have hC : 0<C := mul_pos (mul_pos hC₀ (Real.rpow_pos_of_pos hV _)) (Real.rpow_pos_of_pos (by norm_num) _)
  refine ⟨C,hC,?_,?_⟩
  · dsimp only [C, V, α, nativeZeroBoundarySupercriticalConstant]
    rw [hC₀Formula]
  intro q a R u Du hR hu hDu
  let B := Metric.ball a R
  let U := B.indicator u
  let D₀ := fun x i=>B.indicator (fun y=>Du y i) x
  let J := ∫ y in B,(Real.sqrt (hsNormSq (Du y)))^s
  let K := V^((1/2 : ℝ)-1/s)*J^(1/s)
  have hJ : 0≤J := integral_nonneg fun y=>Real.rpow_nonneg (Real.sqrt_nonneg _) _
  have hK : 0≤K := mul_nonneg (Real.rpow_nonneg hV.le _) (Real.rpow_nonneg hJ _)
  have hOriginalLp := memLp_hsNorm_of_columns Du (ENNReal.ofReal s) hDu
  have hOriginalI : IntegrableOn (fun x=>(Real.sqrt (hsNormSq (Du x)))^s) B volume := by
    have H := hOriginalLp.integrable_norm_rpow (ENNReal.ofReal_pos.mpr hs0).ne' ENNReal.ofReal_ne_top
    simpa only [B,IntegrableOn,ENNReal.toReal_ofReal hs0.le,Real.norm_of_nonneg (Real.sqrt_nonneg _)] using H
  have hColumns (i : Fin n) : MemLp (fun x=>D₀ x i) (ENNReal.ofReal s) volume :=
    (memLp_indicator_iff_restrict measurableSet_ball).mpr (hDu i)
  have hGlobalLp := memLp_hsNorm_of_columns D₀ (ENNReal.ofReal s) hColumns
  obtain ⟨hFull,_hMapEnergy,_hGradEnergy⟩ := zeroBoundary_zeroExtension_univ (ballDomain a R) u Du hu
  have hMoment : (∫ y,(Real.sqrt (hsNormSq (D₀ y)))^s)=J := by
    have hFun : (fun y=>(Real.sqrt (hsNormSq (D₀ y)))^s)=
        B.indicator (fun y=>(Real.sqrt (hsNormSq (Du y)))^s) := by
      funext y
      by_cases hy : y∈B
      · simp only [D₀,indicator_of_mem hy]
      · simp only [D₀,indicator_of_notMem hy,hsNormSq,norm_zero,
          zero_pow (by decide : (2 : ℕ)≠0),Finset.sum_const_zero,Real.sqrt_zero,Real.zero_rpow hs0.ne']
    rw [hFun,integral_indicator measurableSet_ball]
  obtain ⟨_hGlobalI,hGrowth⟩ := global_hs_supercritical_quadratic_growth D₀ s hs2 hGlobalLp
  have hGrowthK (x : Domain n) (r : ℝ) (hr : 0<r) (_hCap : r≤16*R) :
      (∫ y in Metric.ball x r,(Real.sqrt (hsNormSq (D₀ y)))^(2 : ℝ))≤K^(2 : ℝ)*r^((n : ℝ)-2+2*α) := by
    simpa only [hMoment,Real.rpow_two] using hGrowth x r hr
  obtain ⟨w,hw,_hUnique⟩ := Hrep q U D₀ K (16*R) hFull.1.to_memW12Loc hK (by positivity) hGrowthK
  let i₀ : Fin n := ⟨0,by omega⟩
  let e : Domain n := EuclideanSpace.single i₀ 1
  have he : ‖e‖=1 := by simp [e]
  let y := a+(3*R) • e
  have hya : dist y a=3*R := by
    rw [dist_eq_norm]
    have hDiff : y-a=(3*R) • e := by dsimp only [y];abel
    rw [hDiff,norm_smul,Real.norm_of_nonneg (by positivity),he,mul_one]
  have hOutside : Metric.ball y R⊆Bᶜ := by
    intro z hz
    have hzDist : dist z y<R := hz
    have H := dist_triangle y z a
    rw [hya,dist_comm y z] at H
    have hza : R<dist z a := by linarith
    exact not_lt_of_ge hza.le
  have hwZero : w =ᵐ[volume.restrict (Metric.ball y R)](fun _=>0) := by
    filter_upwards [ae_restrict_of_ae hw.2.1,ae_restrict_mem measurableSet_ball] with z hz hzin
    rw [hz]
    exact indicator_of_notMem (hOutside hzin) u
  have hwAnchor : w y=0 :=
    (volume : Measure (Domain n)).eqOn_open_of_ae_eq hwZero Metric.isOpen_ball hw.1.continuousOn continuousOn_const
      (Metric.mem_ball_self hR)
  have hPoint (x : Domain n) (hx : x∈B) : ‖w x‖≤C*R^α*J^(1/s) := by
    have hxa : dist x a<R := hx
    have hxy : dist x y≤4*R := by
      have H := dist_triangle x a y
      rw [dist_comm a y,hya] at H
      linarith
    have hCap : dist x y≤(16*R)/4 := by linarith
    have H := hw.2.2.2.2 x y hCap
    rw [hwAnchor,sub_zero] at H
    calc
      _ ≤ C₀*K*(dist x y)^α := H
      _ ≤ C₀*K*(4*R)^α := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow dist_nonneg hxy hα.le) (mul_nonneg hC₀.le hK)
      _ = _ := by rw [Real.mul_rpow (by norm_num : (0 : ℝ)≤4) hR.le];dsimp only [K,C];ring
  have hBound : ∀ᵐ x ∂volume.restrict B,‖u x‖≤C*R^α*J^(1/s) := by
    filter_upwards [ae_restrict_of_ae hw.2.1,ae_restrict_mem measurableSet_ball] with x hx hxB
    have hEq : w x=u x := hx.trans (indicator_of_mem hxB u)
    rw [← hEq]
    exact hPoint x hxB
  letI : IsFiniteMeasure (volume.restrict B) := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  exact ⟨hOriginalI,hBound,MemLp.of_bound hu.1.2.1.aestronglyMeasurable (C*R^α*J^(1/s)) hBound⟩

theorem exists_native_zeroBoundary_supercritical_bound (n : ℕ) (hn : 2≤n)
    (s : ℝ) (hsn : (n : ℝ)<s) :
    ∃ C : ℝ,0<C ∧ ∀ (q : ℕ) (a : Domain n) (R : ℝ)
      (u : Domain n → Ambient q) (Du : Domain n → Gradient n q),0<R →
      HasZeroBoundaryValues (ballDomain a R) u Du →
      (∀ i,MemLp (fun x=>Du x i) (ENNReal.ofReal s) (volume.restrict (Metric.ball a R))) →
      IntegrableOn (fun x=>(Real.sqrt (hsNormSq (Du x)))^s) (Metric.ball a R) volume ∧
        (∀ᵐ x ∂volume.restrict (Metric.ball a R),‖u x‖≤
          C*R^(1-(n : ℝ)/s)*(∫ y in Metric.ball a R,(Real.sqrt (hsNormSq (Du y)))^s)^(1/s)) ∧
        MemLp u ⊤ (volume.restrict (Metric.ball a R)) := by
  obtain ⟨C,hC,_hFormula,H⟩ := exists_native_zeroBoundary_supercritical_bound_explicit n hn s hsn
  exact ⟨C,hC,H⟩

theorem exists_native_zeroBoundary_supercritical_bound_fixed_explicit (n : ℕ) (hn : 2≤n)
    :
    ∃ C : ℝ,0<C ∧ C = (nativeZeroBoundaryFixedSupercriticalMajorant n : ℝ) ∧ ∀ (q : ℕ) (a : Domain n) (R : ℝ)
      (u : Domain n → Ambient q) (Du : Domain n → Gradient n q),0<R →
      HasZeroBoundaryValues (ballDomain a R) u Du →
      (∀ i,MemLp (fun x=>Du x i) (ENNReal.ofReal (2*(n : ℝ)+1)) (volume.restrict (Metric.ball a R))) →
      IntegrableOn (fun x=>(Real.sqrt (hsNormSq (Du x)))^(2*(n : ℝ)+1)) (Metric.ball a R) volume ∧
        (∀ᵐ x ∂volume.restrict (Metric.ball a R),‖u x‖≤
          C*R^(1-(n : ℝ)/(2*(n : ℝ)+1))*(∫ y in Metric.ball a R,(Real.sqrt (hsNormSq (Du y)))^(2*(n : ℝ)+1))^(1/(2*(n : ℝ)+1))) ∧
        MemLp u ⊤ (volume.restrict (Metric.ball a R)) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  obtain ⟨C,hC,hFormula,H⟩ := exists_native_zeroBoundary_supercritical_bound_explicit n hn
    (2*(n : ℝ)+1) (by linarith only [hnR])
  have hCB : C ≤ (nativeZeroBoundaryFixedSupercriticalMajorant n : ℝ) := by
    rw [hFormula]
    exact nativeZeroBoundarySupercriticalConstant_fixed_le n hn
  refine ⟨(nativeZeroBoundaryFixedSupercriticalMajorant n : ℝ),lt_of_lt_of_le hC hCB,rfl,?_⟩
  intro q a R u Du hR hu hDu
  obtain ⟨hI,hBound,hLp⟩ := H q a R u Du hR hu hDu
  refine ⟨hI,?_,hLp⟩
  filter_upwards [hBound] with x hx
  exact hx.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hCB (Real.rpow_nonneg hR.le _))
    (Real.rpow_nonneg (integral_nonneg fun _ => Real.rpow_nonneg (Real.sqrt_nonneg _) _) _))

theorem exists_native_zeroBoundary_supercritical_bound_uniform_explicit (n : ℕ) (hn : 2≤n)
    (s : ℝ) (hsn : (n : ℝ) < s) (hHalf : (1/2 : ℝ) ≤ 1-(n : ℝ)/s) :
    ∃ C : ℝ,0<C ∧ C = (nativeZeroBoundaryFixedSupercriticalMajorant n : ℝ) ∧ ∀ (q : ℕ) (a : Domain n) (R : ℝ)
      (u : Domain n → Ambient q) (Du : Domain n → Gradient n q),0<R →
      HasZeroBoundaryValues (ballDomain a R) u Du →
      (∀ i,MemLp (fun x=>Du x i) (ENNReal.ofReal s) (volume.restrict (Metric.ball a R))) →
      IntegrableOn (fun x=>(Real.sqrt (hsNormSq (Du x)))^s) (Metric.ball a R) volume ∧
        (∀ᵐ x ∂volume.restrict (Metric.ball a R),‖u x‖≤
          C*R^(1-(n : ℝ)/s)*(∫ y in Metric.ball a R,(Real.sqrt (hsNormSq (Du y)))^s)^(1/s)) ∧
        MemLp u ⊤ (volume.restrict (Metric.ball a R)) := by
  obtain ⟨C,hC,hFormula,H⟩ := exists_native_zeroBoundary_supercritical_bound_explicit n hn s hsn
  have hCB : C ≤ (nativeZeroBoundaryFixedSupercriticalMajorant n : ℝ) := by
    rw [hFormula]
    exact nativeZeroBoundarySupercriticalConstant_uniform_le n hn s hsn hHalf
  refine ⟨(nativeZeroBoundaryFixedSupercriticalMajorant n : ℝ),lt_of_lt_of_le hC hCB,rfl,?_⟩
  intro q a R u Du hR hu hDu
  obtain ⟨hI,hBound,hLp⟩ := H q a R u Du hR hu hDu
  refine ⟨hI,?_,hLp⟩
  filter_upwards [hBound] with x hx
  exact hx.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hCB (Real.rpow_nonneg hR.le _))
    (Real.rpow_nonneg (integral_nonneg fun _ => Real.rpow_nonneg (Real.sqrt_nonneg _) _) _))

end StationaryHarmonicMaps.Analysis

end
