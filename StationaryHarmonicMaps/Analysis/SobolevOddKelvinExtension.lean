module

public import StationaryHarmonicMaps.Analysis.SmoothOddKelvinExtension
public import StationaryHarmonicMaps.Analysis.AnnularInversionGradientTransport
public import StationaryHarmonicMaps.Analysis.SobolevStrongCompleteness
public import HarmonicMaps.Analysis.BallAverageDifferentiation
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-!
# Native Sobolev odd Kelvin gluing

Actual compact smooth W0 approximants are reflected by the genuine smooth
Kelvin gluing. Inversion transports their original strong L2 map and
column limits on each bounded exterior annulus. The native weak-gradient
closure identifies the resulting literal piecewise map and columns.
No reflected weak Poisson equation or boundary regularity estimate is
assumed or asserted by this graph construction.
-/

public section

open HarmonicMaps EuclideanGeometry MeasureTheory Filter Set
open StationaryHarmonicMaps.Geometry
open scoped ContDiff Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

private theorem strong_L2_mono_measure {X : Type*} [MeasurableSpace X] {q : ℕ}
    (μ ν : Measure X) (hν : ν≤μ) (f : ℕ → X → Ambient q) (v : X → Ambient q)
    (hConv : Tendsto (fun k=>eLpNorm (f k-v) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun k=>eLpNorm (f k-v) 2 ν) atTop (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hConv (fun _=>zero_le)
    (fun k=>eLpNorm_mono_measure (f k-v) hν)

private theorem fixed_coefficient_L2 {X : Type*} [MeasurableSpace X] {q : ℕ}
    (μ : Measure X) (a : X → ℝ) (ha : AEStronglyMeasurable a μ)
    {C : ℝ} (hBound : ∀ᵐx∂μ,‖a x‖≤C)
    (f : X → Ambient q) (hf : MemLp f 2 μ) : MemLp (fun x=>a x • f x) 2 μ := by
  apply hf.of_le_mul (c:=C) (ha.smul hf.aestronglyMeasurable)
  filter_upwards [hBound] with x hx
  change ‖a x • f x‖≤C*‖f x‖
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)

private theorem tendsto_fixed_coefficient_L2 {X : Type*} [MeasurableSpace X] {q : ℕ}
    (μ : Measure X) (a : X → ℝ) {C : ℝ} (hBound : ∀ᵐx∂μ,‖a x‖≤C)
    (f : ℕ → X → Ambient q) (v : X → Ambient q)
    (hConv : Tendsto (fun k=>eLpNorm (f k-v) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun k=>eLpNorm ((fun x=>a x • f k x)-(fun x=>a x • v x)) 2 μ) atTop (𝓝 0) := by
  have hUpper := ENNReal.Tendsto.const_mul (a:=ENNReal.ofReal C) hConv (Or.inr ENNReal.ofReal_ne_top)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa only [mul_zero] using hUpper) (fun _=>zero_le)
  intro k
  apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul (p:=2)
  filter_upwards [hBound] with x hx
  change ‖a x • f k x-a x • v x‖≤C*‖f k x-v x‖
  rw [← smul_sub,norm_smul]
  exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)

private theorem tendsto_sub_L2 {X : Type*} [MeasurableSpace X] {q : ℕ}
    (μ : Measure X) (f g : ℕ → X → Ambient q) (v w : X → Ambient q)
    (hf : ∀k,MemLp (f k) 2 μ) (hg : ∀k,MemLp (g k) 2 μ)
    (hv : MemLp v 2 μ) (hw : MemLp w 2 μ)
    (hF : Tendsto (fun k=>eLpNorm (f k-v) 2 μ) atTop (𝓝 0))
    (hG : Tendsto (fun k=>eLpNorm (g k-w) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun k=>eLpNorm ((f k-g k)-(v-w)) 2 μ) atTop (𝓝 0) := by
  have hUpper : Tendsto (fun k=>eLpNorm (f k-v) 2 μ+eLpNorm (g k-w) 2 μ) atTop (𝓝 0) := by
    simpa only [add_zero] using hF.add hG
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hUpper (fun _=>zero_le)
  intro k
  have heq : (f k-g k)-(v-w)=(f k-v)-(g k-w) := by
    funext x
    simp only [Pi.sub_apply]
    abel
  change eLpNorm ((f k-g k)-(v-w)) 2 μ≤eLpNorm (f k-v) 2 μ+eLpNorm (g k-w) 2 μ
  rw [heq]
  exact eLpNorm_sub_le ((hf k).sub hv).aestronglyMeasurable ((hg k).sub hw).aestronglyMeasurable (by norm_num)

private theorem tendsto_piecewise_L2 {X : Type*} [MeasurableSpace X] {q : ℕ}
    (μ : Measure X) (S : Set X) [DecidablePred (·∈S)] (hS : MeasurableSet S)
    (f g : ℕ → X → Ambient q) (v w : X → Ambient q)
    (hf : ∀k,MemLp (f k) 2 (μ.restrict S)) (hg : ∀k,MemLp (g k) 2 (μ.restrict Sᶜ))
    (hv : MemLp v 2 (μ.restrict S)) (hw : MemLp w 2 (μ.restrict Sᶜ))
    (hF : Tendsto (fun k=>eLpNorm (f k-v) 2 (μ.restrict S)) atTop (𝓝 0))
    (hG : Tendsto (fun k=>eLpNorm (g k-w) 2 (μ.restrict Sᶜ)) atTop (𝓝 0)) :
    Tendsto (fun k=>eLpNorm ((S.piecewise (f k) (g k))-(S.piecewise v w)) 2 μ) atTop (𝓝 0) := by
  classical
  have hUpper : Tendsto (fun k=>eLpNorm (f k-v) 2 (μ.restrict S)+
      eLpNorm (g k-w) 2 (μ.restrict Sᶜ)) atTop (𝓝 0) := by
    simpa only [add_zero] using hF.add hG
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hUpper (fun _=>zero_le)
  intro k
  have heq : (S.piecewise (f k) (g k))-(S.piecewise v w)=
      S.indicator (f k-v)+Sᶜ.indicator (g k-w) := by
    funext x
    by_cases hx : x∈S <;> simp only [Pi.sub_apply,Pi.add_apply,piecewise,indicator,hx,mem_compl_iff,
      not_true_eq_false,not_false_eq_true,if_true,if_false,add_zero,zero_add]
  change eLpNorm ((S.piecewise (f k) (g k))-(S.piecewise v w)) 2 μ≤
    eLpNorm (f k-v) 2 (μ.restrict S)+eLpNorm (g k-w) 2 (μ.restrict Sᶜ)
  rw [heq]
  have hFI := (memLp_indicator_iff_restrict hS).mpr ((hf k).sub hv)
  have hGI := (memLp_indicator_iff_restrict hS.compl).mpr ((hg k).sub hw)
  simpa only [eLpNorm_indicator_eq_eLpNorm_restrict hS,eLpNorm_indicator_eq_eLpNorm_restrict hS.compl] using
    eLpNorm_add_le hFI.aestronglyMeasurable hGI.aestronglyMeasurable (by norm_num : (1:ℝ≥0∞)≤2)

/-- The literal odd Kelvin reflection of an actual native W0 graph is a genuine native Sobolev graph on each larger finite ball, with all reflected columns produced from the original ones. -/
theorem memW12_odd_kelvin_extension_ball {n q : ℕ} (hn : 2≤n) (R : ℝ) (hR : 1<R)
    (u : Domain n → Ambient q) (Du : Domain n → Gradient n q)
    (hu : HasZeroBoundaryValues (ballDomain (0:Domain n) 1) u Du) :
    let I := inversion (0:Domain n) 1
    let w := fun x : Domain n=>‖x‖^(2-(n:ℝ))
    let C := fun x i=>∑j : Fin n,(fderiv ℝ I x (EuclideanSpace.single i 1)) j • Du (I x) j
    let U := fun x : Domain n=>if ‖x‖≤1 then u x else -w x • u (I x)
    let DU := fun (x : Domain n) (i : Fin n)=>if ‖x‖≤1 then Du x i else
      -w x • C x i-((2-(n:ℝ))*‖x‖^(-(n:ℝ))*inner ℝ x (EuclideanSpace.single i 1)) • u (I x)
    MemW12 (ballDomain (0:Domain n) R) U DU := by
  classical
  intro I w C U DU
  let Ω := ballDomain (0:Domain n) R
  let μ := volume.restrict (Metric.ball (0:Domain n) R)
  let B := Metric.closedBall (0:Domain n) 1
  let S := Bᶜ∩Metric.ball (0:Domain n) R
  let ν := volume.restrict S
  let ρ := volume.restrict (I '' S)
  have hR0 : 0<R := zero_lt_one.trans hR
  have hS : MeasurableSet S := measurableSet_closedBall.compl.inter measurableSet_ball
  have hLower (x : Domain n) (hx : x∈S) : 1≤‖x‖ := by
    have H : ¬‖x‖≤1 := by simpa only [B,mem_compl_iff,Metric.mem_closedBall,dist_zero_right] using hx.1
    exact (not_le.mp H).le
  have hUpper (x : Domain n) (hx : x∈S) : ‖x‖≤R :=
    (by simpa only [Metric.mem_ball,dist_zero_right] using hx.2 : ‖x‖<R).le
  have hS0 (x : Domain n) (hx : x∈S) : x≠0 := norm_pos_iff.mp (zero_lt_one.trans_le (hLower x hx))
  have hImage : I '' S⊆Metric.ball (0:Domain n) 1 := by
    rintro _ ⟨x,hx,rfl⟩
    have H : 1<‖x‖ := by
      have H : ¬‖x‖≤1 := by simpa only [B,mem_compl_iff,Metric.mem_closedBall,dist_zero_right] using hx.1
      exact not_le.mp H
    rw [Metric.mem_ball,dist_zero_right,show ‖I x‖=‖x‖⁻¹ from norm_unit_inversion x]
    exact (inv_lt_one₀ (zero_lt_one.trans H)).mpr H
  have hImageMeasure : ρ≤volume.restrict (Metric.ball (0:Domain n) 1) :=
    Measure.restrict_mono_set volume hImage
  have hInner : μ.restrict B=volume.restrict (Metric.ball (0:Domain n) 1) := by
    have hSub : B⊆Metric.ball (0:Domain n) R :=
      (Metric.closedBall_subset_ball hR)
    rw [show μ.restrict B=volume.restrict (B∩Metric.ball (0:Domain n) R) from
      Measure.restrict_restrict measurableSet_closedBall,inter_eq_left.mpr hSub]
    exact (Measure.restrict_congr_set (HarmonicMaps.ball_ae_eq_closedBall (0:Domain n) (by norm_num : (0:ℝ)<1))).symm
  have hOuter : μ.restrict Bᶜ=ν := Measure.restrict_restrict measurableSet_closedBall.compl
  obtain ⟨huW,ψ,hψ,hcψ,hMap,hColumns⟩ := hu
  let Dψ := fun (k : ℕ) (x : Domain n) (i : Fin n)=>fderiv ℝ (ψ k) x (EuclideanSpace.single i 1)
  have hψL (k : ℕ) : MemLp (ψ k) 2 (volume.restrict (Metric.ball (0:Domain n) 1)) :=
    (hψ k).continuous.memLp_of_hasCompactSupport (hcψ k).1
  have hDψL (k : ℕ) (i : Fin n) : MemLp (fun x=>Dψ k x i) 2
      (volume.restrict (Metric.ball (0:Domain n) 1)) :=
    (((hψ k).continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      ((hcψ k).1.fderiv_apply ℝ (EuclideanSpace.single i 1))
  have hDConv (i : Fin n) : Tendsto (fun k=>eLpNorm (fun x=>Dψ k x i-Du x i) 2
      (volume.restrict (Metric.ball (0:Domain n) 1))) atTop (𝓝 0) := hColumns i
  have hψImage (k : ℕ) : MemLp (ψ k) 2 ρ := (hψL k).mono_measure hImageMeasure
  have huImage : MemLp u 2 ρ := huW.2.1.mono_measure hImageMeasure
  have hDψImage (k : ℕ) (i : Fin n) : MemLp (fun x=>Dψ k x i) 2 ρ :=
    (hDψL k i).mono_measure hImageMeasure
  have hDuImage (i : Fin n) : MemLp (fun x=>Du x i) 2 ρ := (huW.2.2 i).mono_measure hImageMeasure
  have hMapImage := strong_L2_mono_measure _ ρ hImageMeasure ψ u hMap
  have hColumnsImage (i : Fin n) := strong_L2_mono_measure _ ρ hImageMeasure
    (fun k x=>Dψ k x i) (fun x=>Du x i) (hDConv i)
  let P := fun k x=>ψ k (I x)
  let v := fun x=>u (I x)
  let A := fun k x i=>∑j : Fin n,(fderiv ℝ I x (EuclideanSpace.single i 1)) j • Dψ k (I x) j
  have hP (k : ℕ) : MemLp (P k) 2 ν :=
    (unit_inversion_L2_transport_bounded_set S hS hS0 R hR0 hUpper (ψ k) (hψImage k)).1
  have hv : MemLp v 2 ν :=
    (unit_inversion_L2_transport_bounded_set S hS hS0 R hR0 hUpper u huImage).1
  have hPConv : Tendsto (fun k=>eLpNorm (P k-v) 2 ν) atTop (𝓝 0) :=
    tendsto_unit_inversion_L2_transport S hS hS0 R hR0 hUpper ψ u hψImage huImage hMapImage
  have hA (k : ℕ) : ∀i,MemLp (fun x=>A k x i) 2 ν :=
    (unit_inversion_L2_gradient_columns_transport S hS 1 R (by norm_num) hR0 hLower hUpper
      (Dψ k) (hDψImage k)).1
  have hC : ∀i,MemLp (fun x=>C x i) 2 ν :=
    (unit_inversion_L2_gradient_columns_transport S hS 1 R (by norm_num) hR0 hLower hUpper Du hDuImage).1
  have hAConv : ∀i,Tendsto (fun k=>eLpNorm (fun x=>A k x i-C x i) 2 ν) atTop (𝓝 0) :=
    tendsto_unit_inversion_L2_gradient_columns S hS 1 R (by norm_num) hR0 hLower hUpper
      Dψ Du hDψImage hDuImage hColumnsImage
  let r := fun (i : Fin n) (x : Domain n)=>(2-(n:ℝ))*‖x‖^(-(n:ℝ))*inner ℝ x (EuclideanSpace.single i 1)
  have hwMeas : AEStronglyMeasurable (fun x=> -w x) ν :=
    ((measurable_norm.pow_const (2-(n:ℝ))).neg).aestronglyMeasurable
  have hwBound : ∀ᵐx∂ν,‖-w x‖≤1 := by
    filter_upwards [ae_restrict_mem hS] with x hx
    rw [norm_neg,Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg x) _)]
    exact Real.rpow_le_one_of_one_le_of_nonpos (hLower x hx) (sub_nonpos.mpr (by exact_mod_cast hn))
  have hrMeas (i : Fin n) : AEStronglyMeasurable (r i) ν :=
    ((measurable_const.mul (measurable_norm.pow_const (-(n:ℝ)))).mul
      (continuous_id.inner continuous_const).measurable).aestronglyMeasurable
  have hrBound (i : Fin n) : ∀ᵐx∂ν,‖r i x‖≤|2-(n:ℝ)| *R := by
    filter_upwards [ae_restrict_mem hS] with x hx
    have hPow : ‖x‖^(-(n:ℝ))≤1 := Real.rpow_le_one_of_one_le_of_nonpos (hLower x hx) (neg_nonpos.mpr (Nat.cast_nonneg n))
    have hInn : |inner ℝ x (EuclideanSpace.single i 1)|≤R := by
      have H : |inner ℝ x (EuclideanSpace.single i 1)|≤‖x‖ := by
        simpa using abs_real_inner_le_norm x (EuclideanSpace.single i (1:ℝ))
      exact H.trans (hUpper x hx)
    change |(2-(n:ℝ))*‖x‖^(-(n:ℝ))*inner ℝ x (EuclideanSpace.single i 1)|≤_
    rw [abs_mul,abs_mul,abs_of_nonneg (Real.rpow_nonneg (norm_nonneg x) _)]
    calc
      _ ≤ (|2-(n:ℝ)| *1)*R := mul_le_mul
        (mul_le_mul_of_nonneg_left hPow (abs_nonneg _)) hInn (abs_nonneg _) (by positivity)
      _ = _ := by ring
  let O := fun k x=> -w x • P k x
  let o := fun x=> -w x • v x
  let DO := fun k x i=> -w x • A k x i-r i x • P k x
  let dO := fun x i=> -w x • C x i-r i x • v x
  have hO (k : ℕ) : MemLp (O k) 2 ν := fixed_coefficient_L2 ν _ hwMeas hwBound _ (hP k)
  have ho : MemLp o 2 ν := fixed_coefficient_L2 ν _ hwMeas hwBound _ hv
  have hOConv : Tendsto (fun k=>eLpNorm (O k-o) 2 ν) atTop (𝓝 0) :=
    tendsto_fixed_coefficient_L2 ν _ hwBound P v hPConv
  have hDO (k : ℕ) (i : Fin n) : MemLp (fun x=>DO k x i) 2 ν :=
    (fixed_coefficient_L2 ν _ hwMeas hwBound _ (hA k i)).sub
      (fixed_coefficient_L2 ν _ (hrMeas i) (hrBound i) _ (hP k))
  have hdO (i : Fin n) : MemLp (fun x=>dO x i) 2 ν :=
    (fixed_coefficient_L2 ν _ hwMeas hwBound _ (hC i)).sub
      (fixed_coefficient_L2 ν _ (hrMeas i) (hrBound i) _ hv)
  have hDOConv (i : Fin n) : Tendsto (fun k=>eLpNorm (fun x=>DO k x i-dO x i) 2 ν) atTop (𝓝 0) :=
    tendsto_sub_L2 ν (fun k x=> -w x • A k x i) (fun k x=>r i x • P k x)
      (fun x=> -w x • C x i) (fun x=>r i x • v x)
      (fun k=>fixed_coefficient_L2 ν _ hwMeas hwBound _ (hA k i))
      (fun k=>fixed_coefficient_L2 ν _ (hrMeas i) (hrBound i) _ (hP k))
      (fixed_coefficient_L2 ν _ hwMeas hwBound _ (hC i))
      (fixed_coefficient_L2 ν _ (hrMeas i) (hrBound i) _ hv)
      (tendsto_fixed_coefficient_L2 ν _ hwBound (fun k x=>A k x i) (fun x=>C x i) (hAConv i))
      (tendsto_fixed_coefficient_L2 ν _ (hrBound i) P v hPConv)
  choose Uψ hUψ hUψIn hUψOut hDUψIn hDUψOut using fun k=>
    exists_smooth_odd_kelvin_extension (ψ k) (hψ k) (hcψ k).2
  have hPieceU : U=B.piecewise u o := by
    funext x
    simp only [U,piecewise,B,Metric.mem_closedBall,dist_zero_right,o,v]
  have hPieceDU (i : Fin n) : (fun x=>DU x i)=B.piecewise (fun x=>Du x i) (fun x=>dO x i) := by
    funext x
    simp only [DU,piecewise,B,Metric.mem_closedBall,dist_zero_right,dO,v,r]
  have huL : MemLp U 2 μ := by
    rw [hPieceU]
    apply MemLp.piecewise measurableSet_closedBall
    · rw [hInner];exact huW.2.1
    · rw [hOuter];exact ho
  have hDUL (i : Fin n) : MemLp (fun x=>DU x i) 2 μ := by
    rw [hPieceDU i]
    apply MemLp.piecewise measurableSet_closedBall
    · rw [hInner];exact huW.2.2 i
    · rw [hOuter];exact hdO i
  have hUψPiece (k : ℕ) : Uψ k=B.piecewise (ψ k) (O k) := by
    funext x
    by_cases hx : x∈B
    · rw [piecewise_eq_of_mem B _ _ hx]
      exact hUψIn k x (by simpa only [B,Metric.mem_closedBall,dist_zero_right] using hx)
    · rw [piecewise_eq_of_notMem B _ _ hx]
      exact hUψOut k x (not_le.mp (by simpa only [B,Metric.mem_closedBall,dist_zero_right] using hx)).le
  have hMapLimit : Tendsto (fun k=>eLpNorm (Uψ k-U) 2 μ) atTop (𝓝 0) := by
    simp_rw [hUψPiece,hPieceU]
    apply tendsto_piecewise_L2 μ B measurableSet_closedBall ψ O u o
    · intro k;rw [hInner];exact hψL k
    · intro k;rw [hOuter];exact hO k
    · rw [hInner];exact huW.2.1
    · rw [hOuter];exact ho
    · rw [hInner];exact hMap
    · rw [hOuter];exact hOConv
  have hClassicalChain (k : ℕ) (x z : Domain n) :
      fderiv ℝ (ψ k) (I x) z=∑j : Fin n,z j • Dψ k (I x) j := by
    have hZ : (∑j : Fin n,z j • EuclideanSpace.single j 1)=z := by
      simpa only [EuclideanSpace.basisFun_repr,EuclideanSpace.basisFun_apply] using
        (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr z
    calc
      _ = fderiv ℝ (ψ k) (I x) (∑j : Fin n,z j • EuclideanSpace.single j 1) :=
        congrArg (fderiv ℝ (ψ k) (I x)) hZ.symm
      _ = _ := by rw [map_sum];simp only [map_smul,Dψ]
  have hDerivPiece (k : ℕ) (i : Fin n) :
      (fun x=>fderiv ℝ (Uψ k) x (EuclideanSpace.single i 1)) =ᵐ[μ]
        B.piecewise (fun x=>Dψ k x i) (fun x=>DO k x i) := by
    have hBallClosed : Metric.ball (0:Domain n) 1 =ᵐ[μ] B :=
      (HarmonicMaps.ball_ae_eq_closedBall (0:Domain n) (by norm_num : (0:ℝ)<1)).filter_mono
        (ae_mono Measure.restrict_le_self)
    filter_upwards [hBallClosed] with x hx
    by_cases hInnerX : x∈B
    · rw [piecewise_eq_of_mem B _ _ hInnerX]
      have hNorm : ‖x‖<1 := by
        have H : x∈Metric.ball (0:Domain n) 1 := Eq.mpr hx hInnerX
        simpa only [Metric.mem_ball,dist_zero_right] using H
      exact congrArg (fun L : Domain n →L[ℝ] Ambient q=>L (EuclideanSpace.single i 1)) (hDUψIn k x hNorm)
    · rw [piecewise_eq_of_notMem B _ _ hInnerX]
      have hNorm : 1<‖x‖ := not_le.mp (by simpa only [B,Metric.mem_closedBall,dist_zero_right] using hInnerX)
      rw [hDUψOut k x (EuclideanSpace.single i 1) hNorm,hClassicalChain]
  have hUψW (k : ℕ) : MemW12 Ω (Uψ k)
      (fun x i=>fderiv ℝ (Uψ k) x (EuclideanSpace.single i 1)) := by
    have hMapLp : MemLp (Uψ k) 2 μ := by
      rw [hUψPiece k]
      apply MemLp.piecewise measurableSet_closedBall
      · rw [hInner];exact hψL k
      · rw [hOuter];exact hO k
    have hDerivLp (i : Fin n) : MemLp
        (fun x=>fderiv ℝ (Uψ k) x (EuclideanSpace.single i 1)) 2 μ := by
      have hPW : MemLp (B.piecewise (fun x=>Dψ k x i) (fun x=>DO k x i)) 2 μ := by
        apply MemLp.piecewise measurableSet_closedBall
        · rw [hInner];exact hDψL k i
        · rw [hOuter];exact hDO k i
      exact MemLp.ae_eq (hDerivPiece k i).symm hPW
    exact memW12_of_c1 Ω ((hUψ k).of_le (by simp)) hMapLp hDerivLp
  have hGradLimit (i : Fin n) : Tendsto (fun k=>eLpNorm
      (fun x=>fderiv ℝ (Uψ k) x (EuclideanSpace.single i 1)-DU x i) 2 μ) atTop (𝓝 0) := by
    have H : Tendsto (fun k=>eLpNorm
        (B.piecewise (fun x=>Dψ k x i) (fun x=>DO k x i)-
          B.piecewise (fun x=>Du x i) (fun x=>dO x i)) 2 μ) atTop (𝓝 0) := by
      apply tendsto_piecewise_L2 μ B measurableSet_closedBall
      · intro k;rw [hInner];exact hDψL k i
      · intro k;rw [hOuter];exact hDO k i
      · rw [hInner];exact huW.2.2 i
      · rw [hOuter];exact hdO i
      · rw [hInner];exact hDConv i
      · rw [hOuter];exact hDOConv i
    apply H.congr
    intro k
    apply eLpNorm_congr_ae
    filter_upwards [hDerivPiece k i] with x hx
    rw [hx]
    change (B.piecewise (fun x=>Dψ k x i) (fun x=>DO k x i)) x-
      (B.piecewise (fun x=>Du x i) (fun x=>dO x i)) x=
      (B.piecewise (fun x=>Dψ k x i) (fun x=>DO k x i)) x-DU x i
    exact congrArg (fun z : Ambient q=>(B.piecewise (fun x=>Dψ k x i) (fun x=>DO k x i)) x-z)
      (congrFun (hPieceDU i) x).symm
  have hWeak (i : Fin n) (g : Domain n → Ambient q) (hg : MemLp g 2 μ) :=
    HolderToCK.tendsto_integral_inner_of_L2 (fun k=>(hUψW k).2.2 i) (hDUL i) hg (hGradLimit i)
  exact memW12_of_strong_map_weak_gradient_L2 Ω Uψ
    (fun k x i=>fderiv ℝ (Uψ k) x (EuclideanSpace.single i 1)) hUψW U DU huL hDUL hMapLimit
    (fun i g hg=>by simpa only [real_inner_comm] using hWeak i g hg)

end StationaryHarmonicMaps.Analysis

end
