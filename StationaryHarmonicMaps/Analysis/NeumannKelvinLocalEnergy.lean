/- Copyright (c) 2026. All rights reserved. -/
module

public import StationaryHarmonicMaps.Analysis.NeumannKelvinL2Transport
public import StationaryHarmonicMaps.Analysis.NeumannRadialL2Local
public import StationaryHarmonicMaps.Analysis.BoundaryInversionGeometry
public import HolderToCK.Analysis.Harmonic.GradientVariance
public import HarmonicMaps.Analysis.AffineEnergyScaling
public import HarmonicMaps.Analysis.BallAverageDifferentiation

/-!
# Local full-gradient energy of the actual Neumann reflection

Inversion and every radial sample preserve the original sphere-centered
cap. The actual exterior gradient uses only original gradient columns.
Its full Hilbert--Schmidt energy is controlled by those columns on the
same cap, with no native map or differential equation assumed.
-/

public section

open HarmonicMaps EuclideanGeometry MeasureTheory Filter Set Metric
open StationaryHarmonicMaps.Geometry
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- The same literal Neumann reflected raw columns have a full local HS energy
bound by the original columns on the same boundary cap. -/
theorem neumann_kelvin_local_gradient_energy {n q : ℕ} (hn : 2≤n)
    (D : Domain n → Gradient n q)
    (hD : ∀j,MemLp (fun x=>D x j) 2 (volume.restrict (ball (0 : Domain n) 1)))
    (c : Domain n) (hc : ‖c‖=1) (s : ℝ) (_hs : 0<s) (hsHalf : s≤1/2) :
    let I := inversion (0 : Domain n) 1
    let B := fun x j=>‖x‖^(n-2) • (∫t in (‖x‖⁻¹)^2..‖x‖⁻¹,t^(n-2) • D (t • x) j)
    let DO := fun x i=>‖x‖^(2-(n:ℝ)) •
      (∑j : Fin n,(fderiv ℝ I x (EuclideanSpace.single i 1)) j • D (I x) j)+
        ((n:ℝ)-2) • (∑j : Fin n,((ℝ ∙ x)ᗮ.starProjection (EuclideanSpace.single i 1)) j • B x j)
    let DU := fun x i=>if ‖x‖≤1 then D x i else DO x i
    IntegrableOn (fun x=>hsNormSq (DU x)) (ball c s) volume ∧
      (∫x in ball c s,hsNormSq (DU x))≤
        (1+2*(2:ℝ)^(2*n)+2*((n:ℝ)-2)^2*(2:ℝ)^(2*(n-2))*(4:ℝ)^n)*
          (∫x in ball (0 : Domain n) 1∩ball c s,hsNormSq (D x)) := by
  intro I B DO DU
  let A := {x : Domain n | 1<‖x‖ ∧ ‖x‖<2}
  let S := ball c s∩{x : Domain n | 1<‖x‖}
  let Q := fun x i=>∑j : Fin n,(fderiv ℝ I x (EuclideanSpace.single i 1)) j • D (I x) j
  let T := fun x i=>∑j : Fin n,((ℝ ∙ x)ᗮ.starProjection (EuclideanSpace.single i 1)) j • B x j
  let E := ∫x in ball (0 : Domain n) 1∩ball c s,hsNormSq (D x)
  let R := (2:ℝ)^(2*(n-2))*(4:ℝ)^n
  have hA : MeasurableSet A := (measurableSet_lt measurable_const measurable_norm).inter
    (measurableSet_lt measurable_norm measurable_const)
  have hS : MeasurableSet S := measurableSet_ball.inter (measurableSet_lt measurable_const measurable_norm)
  have hNormCap (x : Domain n) (hx : x∈ball c s) : ‖x‖<2 := by
    have H := dist_triangle x c (0 : Domain n)
    have hxc : dist x c<s := hx
    rw [dist_zero_right,dist_zero_right,hc] at H
    linarith only [H,hxc,hsHalf]
  have hSA : S⊆A := fun x hx=>⟨hx.2,hNormCap x hx.1⟩
  have hSEq : S=A∩ball c s := by
    ext x
    constructor
    · intro hx
      exact ⟨hSA hx,hx.1⟩
    · intro hx
      exact ⟨hx.2,hx.1.1⟩
  have hImage : I '' S⊆ball (0 : Domain n) 1∩ball c s := by
    intro y hy
    have H := unit_inversion_image_exterior_boundary_ball_subset c hc s hy
    exact ⟨H.2,H.1⟩
  have hDImage (j : Fin n) : MemLp (fun x=>D x j) 2 (volume.restrict (I '' S)) :=
    (hD j).mono_measure (Measure.restrict_mono_set volume (hImage.trans inter_subset_left))
  have hDLocal (j : Fin n) : MemLp (fun x=>D x j) 2
      (volume.restrict (ball (0 : Domain n) 1∩ball c s)) :=
    (hD j).mono_measure (Measure.restrict_mono_set volume inter_subset_left)
  have hEI : IntegrableOn (fun x=>hsNormSq (D x)) (ball (0 : Domain n) 1∩ball c s) volume :=
    integrable_hsNormSq_of_columns D hDLocal
  have hQData := unit_inversion_L2_gradient_columns_transport S hS 1 2 (by norm_num) (by norm_num)
    (fun x hx=>hx.2.le) (fun x hx=>(hNormCap x hx.1).le) D hDImage
  have hQLp (j : Fin n) : MemLp (fun x=>Q x j) 2 (volume.restrict S) := hQData.1 j
  have hQI : IntegrableOn (fun x=>hsNormSq (Q x)) S volume := integrable_hsNormSq_of_columns Q hQLp
  have hQE : (∫x in S,hsNormSq (Q x))≤(2:ℝ)^(2*n)*E := by
    have H : (∫x in S,hsNormSq (Q x))≤(2:ℝ)^(2*n)*(∫y in I '' S,hsNormSq (D y)) := by
      simpa only [one_pow,inv_one,one_mul] using hQData.2
    exact H.trans (mul_le_mul_of_nonneg_left
      (integral_mono_measure (Measure.restrict_mono_set volume hImage)
        (Eventually.of_forall fun y=>hsNormSq_nonneg _) hEI) (by positivity))
  have hBLp (j : Fin n) : MemLp (fun x=>B x j) 2 (volume.restrict S) := by
    rw [hSEq]
    exact (neumann_radial_interval_local_L2 (n-2) (n-2) c hc s (fun x=>D x j) (hD j)).1
  have hBI : IntegrableOn (fun x=>hsNormSq (B x)) S volume := integrable_hsNormSq_of_columns B hBLp
  have hBE : (∫x in S,hsNormSq (B x))≤R*E := by
    rw [show (∫x in S,hsNormSq (B x))=∑j : Fin n,∫x in S,‖B x j‖^2 from
      integral_finsetSum _ (fun j _=>(hBLp j).integrable_norm_pow (by decide : (2:ℕ)≠0))]
    calc
      _≤∑j : Fin n,R*(∫x in ball (0 : Domain n) 1∩ball c s,‖D x j‖^2) := by
        apply Finset.sum_le_sum
        intro j _
        rw [hSEq]
        exact (neumann_radial_interval_local_L2 (n-2) (n-2) c hc s (fun x=>D x j) (hD j)).2
      _=R*E := by
        rw [← Finset.mul_sum,← integral_finsetSum _
          (fun j _=>(hDLocal j).integrable_norm_pow (by decide : (2:ℕ)≠0))]
        rfl
  have hTLp (j : Fin n) : MemLp (fun x=>T x j) 2 (volume.restrict S) :=
    ((neumann_radial_tangent_columns_L2 (n-2) D hD).1 j).mono_measure (Measure.restrict_mono_set volume hSA)
  have hTI : IntegrableOn (fun x=>hsNormSq (T x)) S volume := integrable_hsNormSq_of_columns T hTLp
  have hTPoint (x : Domain n) : hsNormSq (T x)≤hsNormSq (B x) := by
    have H := hsNormSq_right_comp_le_of_norm_le (B x) ((ℝ ∙ x)ᗮ.starProjection)
      ((ℝ ∙ x)ᗮ.starProjection_norm_le)
    simpa only [one_pow,one_mul] using H
  have hTE : (∫x in S,hsNormSq (T x))≤R*E := (integral_mono hTI hBI hTPoint).trans hBE
  have hOLp (j : Fin n) : MemLp (fun x=>DO x j) 2 (volume.restrict S) :=
    ((neumann_kelvin_outer_memLp hn (fun _=>(0:Ambient q)) D MemLp.zero' hD).2 j).mono_measure
      (Measure.restrict_mono_set volume hSA)
  have hOI : IntegrableOn (fun x=>hsNormSq (DO x)) S volume := integrable_hsNormSq_of_columns DO hOLp
  have hOPoint : ∀ᵐx∂volume.restrict S,hsNormSq (DO x)≤
      2*hsNormSq (Q x)+2*((n:ℝ)-2)^2*hsNormSq (T x) := by
    filter_upwards [ae_restrict_mem hS] with x hx
    let w := ‖x‖^(2-(n:ℝ))
    have hw0 : 0≤w := Real.rpow_nonneg (norm_nonneg _) _
    have hw1 : w≤1 := Real.rpow_le_one_of_one_le_of_nonpos hx.2.le
      (sub_nonpos.mpr (by exact_mod_cast hn))
    have hQw : hsNormSq (fun i=>w • Q x i)≤hsNormSq (Q x) := by
      rw [hsNormSq_const_smul]
      exact mul_le_of_le_one_left (hsNormSq_nonneg _) (by nlinarith only [hw0,hw1])
    have H := HolderToCK.hsNormSq_add_le (fun i=>w • Q x i) (fun i=>((n:ℝ)-2) • T x i)
    change hsNormSq (DO x)≤_ at H
    simp only [hsNormSq_const_smul] at H
    rw [hsNormSq_const_smul] at hQw
    exact H.trans (by nlinarith only [hQw])
  have hOE : (∫x in S,hsNormSq (DO x))≤
      2*((2:ℝ)^(2*n)*E)+2*((n:ℝ)-2)^2*(R*E) := by
    calc
      _≤∫x in S,2*hsNormSq (Q x)+2*((n:ℝ)-2)^2*hsNormSq (T x) :=
        integral_mono_ae hOI ((hQI.const_mul 2).add (hTI.const_mul (2*((n:ℝ)-2)^2))) hOPoint
      _=2*(∫x in S,hsNormSq (Q x))+2*((n:ℝ)-2)^2*(∫x in S,hsNormSq (T x)) := by
        rw [integral_add (hQI.const_mul 2) (hTI.const_mul (2*((n:ℝ)-2)^2)),integral_const_mul,integral_const_mul]
      _≤_ := add_le_add (mul_le_mul_of_nonneg_left hQE (by norm_num))
        (mul_le_mul_of_nonneg_left hTE (by positivity))
  let F := (ball (0 : Domain n) 1).indicator (fun x=>hsNormSq (D x))
  let G := S.indicator (fun x=>hsNormSq (DO x))
  have hBaseI : IntegrableOn (fun x=>hsNormSq (D x)) (ball (0 : Domain n) 1) volume :=
    integrable_hsNormSq_of_columns D hD
  have hFI : IntegrableOn F (ball c s) volume :=
    (hBaseI.integrable_indicator measurableSet_ball).integrableOn
  have hGI : IntegrableOn G (ball c s) volume := (hOI.integrable_indicator hS).integrableOn
  have hSphere : ∀ᵐ(x : Domain n)∂volume,‖x‖≠1 := by
    filter_upwards [HarmonicMaps.ball_ae_eq_closedBall (0 : Domain n) (by norm_num : (0:ℝ)<1)] with x hx
    intro hNorm
    have hcB : x∈closedBall (0 : Domain n) 1 := by rw [mem_closedBall,dist_zero_right,hNorm]
    have hoB : x∈ball (0 : Domain n) 1 := Eq.mpr hx hcB
    rw [mem_ball,dist_zero_right,hNorm] at hoB
    exact (lt_irrefl (1:ℝ)) hoB
  have hDensity : (fun x=>hsNormSq (DU x)) =ᵐ[volume.restrict (ball c s)] (fun x=>F x+G x) := by
    filter_upwards [ae_restrict_mem measurableSet_ball,ae_restrict_of_ae hSphere] with x hx hxSphere
    by_cases hxIn : ‖x‖<1
    · have hBall : x∈ball (0 : Domain n) 1 := mem_ball_zero_iff.mpr hxIn
      have hNotS : x∉S := fun h=>not_lt_of_ge hxIn.le h.2
      simp only [DU,if_pos hxIn.le,F,G,indicator_of_mem hBall,indicator_of_notMem hNotS,add_zero]
    · have hxOut : 1<‖x‖ := lt_of_le_of_ne (le_of_not_gt hxIn) hxSphere.symm
      have hNotBall : x∉ball (0 : Domain n) 1 := fun h=>not_lt_of_ge hxOut.le (mem_ball_zero_iff.mp h)
      have hInS : x∈S := ⟨hx,hxOut⟩
      simp only [DU,if_neg (not_le.mpr hxOut),F,G,indicator_of_notMem hNotBall,indicator_of_mem hInS,zero_add]
  have hDUI : IntegrableOn (fun x=>hsNormSq (DU x)) (ball c s) volume := (hFI.add hGI).congr hDensity.symm
  have hInside : (∫x in ball c s,F x)=E := by
    rw [setIntegral_indicator measurableSet_ball]
    simp only [E,inter_comm]
  have hOutside : (∫x in ball c s,G x)=∫x in S,hsNormSq (DO x) := by
    rw [setIntegral_indicator hS,inter_eq_right.mpr inter_subset_left]
  refine ⟨hDUI,?_⟩
  calc
    _=(∫x in ball c s,F x)+(∫x in ball c s,G x) :=
      (integral_congr_ae hDensity).trans (integral_add hFI hGI)
    _=E+(∫x in S,hsNormSq (DO x)) := by rw [hInside,hOutside]
    _≤E+(2*((2:ℝ)^(2*n)*E)+2*((n:ℝ)-2)^2*(R*E)) := add_le_add le_rfl hOE
    _=_ := by dsimp only [R,E];ring

end StationaryHarmonicMaps.Analysis

end
