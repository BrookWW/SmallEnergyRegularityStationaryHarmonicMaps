module

public import StationaryHarmonicMaps.Analysis.BoundaryCenteredCoexactEnergy
public import StationaryHarmonicMaps.Analysis.BoundaryLocalizedTest
public import StationaryHarmonicMaps.Analysis.BoundaryEvenPowerGrowth

/-!
# Local compensated relative responses on boundary queries

For an alternating bilinear coefficient, localization of a centered map
has no quadratic cutoff error. The original all-ball critical bound and
original power growth therefore control the actual relative response of
the localized forcing, including for queries crossing the source sphere.
-/

public section

open HarmonicMaps EuclideanGeometry MeasureTheory Filter Set Metric
open StationaryHarmonicMaps.Geometry
open scoped Topology ENNReal ContDiff

namespace StationaryHarmonicMaps.Analysis

/-- A localized alternating forcing has a real natural relative response
whose total energy gains the critical smallness factor and the original
query-scale power, including at the boundary. -/
theorem exists_alternating_boundary_near_coexact_energy (n : ℕ) (hn : 2≤n)
    (m k : ℕ) (B : Ambient m →L[ℝ] (Ambient m →L[ℝ] Ambient k))
    (hAlt : ∀z : Ambient m,B z z=0) (ν : ℝ) :
    ∃C : ℝ,0<C ∧ ∀ (u : Domain n → Ambient m) (Du : Domain n → Gradient n m)
      (η M K : ℝ),MemW12 (ballDomain (0 : Domain n) 1) u Du → 0≤η →
      (∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),‖u x‖≤M) →
      criticalGradientMorreySquare Du (ball (0 : Domain n) 1)≤ENNReal.ofReal (η^2) → 0≤K →
      (∀a∈ball (0 : Domain n) 1,∀r : ℝ,0<r →
        (∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (Du x))≤K*r^ν) →
      ∀a∈ball (0 : Domain n) 1,∀r : ℝ,0<r → r≤1/8 →
      ∃ (χ : Domain n → ℝ) (c : Ambient m) (P : Domain n → Gradient n k)
        (v : Domain n → Ambient k),
        ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ⊆ball a (2*r) ∧
        (∀x∈closedBall a r,χ x=1) ∧ (∀x,0≤χ x ∧ χ x≤1) ∧
        (∀i,MemLp (fun x=>P x i) 2 (volume.restrict (ball (0 : Domain n) 1))) ∧
        MemW12 (ballDomain (0 : Domain n) 1) v
          (fun x i=>χ x • B (u x-c) (Du x i)-P x i) ∧
        (∀ (ψ : Domain n → Ambient k) (Dψ : Domain n → Gradient n k),
          MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ →
          IntegrableOn (fun x=>∑i : Fin n,inner ℝ (P x i) (Dψ x i)) (ball (0 : Domain n) 1) volume ∧
          (∫x in ball (0 : Domain n) 1,∑i : Fin n,inner ℝ (P x i) (Dψ x i))=0) ∧
        (∫x in ball (0 : Domain n) 1,hsNormSq (P x))≤C*η^2*K*r^ν := by
  obtain ⟨D,hD,HD⟩ := exists_boundary_centered_coexact_compensated_energy n hn m k B
  obtain ⟨L,hL,HL⟩ := exists_boundary_localized_native_test_energy n
  let A := (2 : ℝ)^ν*(1+(2 : ℝ)^(2*n))
  have hA : 0<A := by dsimp only [A];positivity
  refine ⟨D*L*A*(4 : ℝ)^ν,by positivity,?_⟩
  intro u Du η M K hu hη hBound hCritical hK hGrowth a ha r hr hrCap
  let I := inversion (0 : Domain n) 1
  let U := fun x=>if ‖x‖≤1 then u x else u (I x)
  let DU := fun x i=>if ‖x‖≤1 then Du x i else
    ∑j : Fin n,(fderiv ℝ I x (EuclideanSpace.single i 1)) j • Du (I x) j
  have hU : MemW12 (ballDomain (0 : Domain n) 2) U DU :=
    memW12_even_inversion_extension_ball_two hn u Du hu
  obtain ⟨χ,hχ,hcχ,hsχ,hOne,hBounds,hW,hWEnergy⟩ := HL m U DU hU a ha r hr hrCap
  let c := ⨍x in ball a (4*r),U x
  let W := fun x=>χ x • (u x-c)
  let DW := fun x i=>χ x • Du x i+fderiv ℝ χ x (EuclideanSpace.single i 1) • (u x-c)
  let DWext := fun x i=>χ x • DU x i+fderiv ℝ χ x (EuclideanSpace.single i 1) • (U x-c)
  let μ := volume.restrict (ball (0 : Domain n) 1)
  have hAgree (x : Domain n) (hx : x∈ball (0 : Domain n) 1) : U x=u x ∧ DU x=Du x := by
    have hxNorm : ‖x‖≤1 := (mem_ball_zero_iff.mp hx).le
    exact ⟨if_pos hxNorm,funext fun i=>if_pos hxNorm⟩
  have hDWEq : DW=ᵐ[μ]DWext := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    obtain ⟨hUx,hDx⟩ := hAgree x hx
    simp only [DW,DWext,hUx,hDx]
  have hWOriginal : MemW12 (ballDomain (0 : Domain n) 1) W DW := by
    apply (memW12_of_openDomain_subset hW (subset_univ _)).congr_ae ?_ hDWEq.symm
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    rw [(hAgree x hx).1]
  obtain ⟨_b,_Db,P,v,Dv,hv,_hb,hP,_hSkew,_hClosed,_hDiv,_hNormal,hPN,hDecomp,hPEnergy⟩ :=
    HD u Du η M hu hη hBound hCritical W DW hWOriginal c
  have hAlgebra (x : Domain n) (i : Fin n) :
      B (u x-c) (DW x i)=χ x • B (u x-c) (Du x i) := by
    dsimp only [DW]
    rw [map_add,map_smul,map_smul,hAlt,smul_zero,add_zero]
  have hv' : MemW12 (ballDomain (0 : Domain n) 1) v
      (fun x i=>χ x • B (u x-c) (Du x i)-P x i) := by
    apply hv.congr_ae (Eventually.of_forall fun _=>rfl)
    filter_upwards [hDecomp] with x hx
    funext i
    apply eq_sub_iff_add_eq.mpr
    exact (hx i).symm.trans (hAlgebra x i)
  have hQuery : ball a (4*r)⊆ball (0 : Domain n) 2 := by
    intro x hx
    have hTri := dist_triangle x a (0 : Domain n)
    have hxa : dist x a<4*r := hx
    have ha0 : dist a (0 : Domain n)<1 := ha
    change dist x (0 : Domain n)<2
    linarith only [hTri,hxa,ha0,hrCap]
  have hUEnergy : (∫x in ball a (4*r),hsNormSq (DU x))≤A*K*(4*r)^ν := by
    have H := even_inversion_power_growth_unitBall hn ν u Du hu K hK hGrowth a (4*r) (by positivity)
    simpa only [inter_eq_left.mpr hQuery] using H
  have hDWEnergy : (∫x,hsNormSq (DW x) ∂μ)≤L*(A*K*(4*r)^ν) := by
    rw [integral_congr_ae (hDWEq.mono fun _ hx=>congrArg hsNormSq hx)]
    exact hWEnergy.trans (mul_le_mul_of_nonneg_left hUEnergy hL.le)
  refine ⟨χ,c,P,v,hχ,hcχ,hsχ,hOne,hBounds,hP,hv',hPN,?_⟩
  exact hPEnergy.trans ((mul_le_mul_of_nonneg_left hDWEnergy (by positivity : 0≤D*η^2)).trans_eq (by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ)≤4) hr.le]
    ring))

end StationaryHarmonicMaps.Analysis

end
