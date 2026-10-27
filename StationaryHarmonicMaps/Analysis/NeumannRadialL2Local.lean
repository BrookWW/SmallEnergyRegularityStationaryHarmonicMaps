/- Copyright (c) 2026. All rights reserved. -/
module

public import StationaryHarmonicMaps.Analysis.NeumannRadialL2Interval
public import StationaryHarmonicMaps.Analysis.NeumannRadialGeometry

/-!
# Local boundary-cap energy of the actual radial correction

Every original radial sample stays in the same sphere-centered cap.
Restricting the original data to that cap therefore preserves its actual
radial average there. The global L2 estimate gives a local energy bound
with no loss in the cap radius.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- The actual radial interval only samples its original boundary cap. -/
theorem neumann_radial_interval_cap_identity {n q : ℕ} (a b : ℕ)
    (c : Domain n) (hc : ‖c‖=1) (s : ℝ) (u : Domain n → Ambient q)
    (x : Domain n) (hx : 1<‖x‖) (hxCap : x∈ball c s) :
    (‖x‖^a • (∫t in (‖x‖⁻¹)^2..‖x‖⁻¹,t^b • (ball c s).indicator u (t • x)))=
      ‖x‖^a • (∫t in (‖x‖⁻¹)^2..‖x‖⁻¹,t^b • u (t • x)) := by
  have hr : 0<‖x‖ := zero_lt_one.trans hx
  have hi : 0≤‖x‖⁻¹ := inv_nonneg.mpr hr.le
  have hOne : ‖x‖⁻¹≤1 := (inv_le_one₀ hr).mpr hx.le
  have hOrder : (‖x‖⁻¹)^2≤‖x‖⁻¹ := by nlinarith only [hi,hOne]
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  have htI : t∈Icc ((‖x‖⁻¹)^2) (‖x‖⁻¹) := by simpa only [uIcc_of_le hOrder] using ht
  have hInside := neumann_reflection_sample_mem_boundary_ball c x s hc hx.le hxCap t
    (by simpa only [inv_pow] using htI.1) htI.2
  dsimp only
  rw [indicator_of_mem hInside u]

/-- The original variable radial average has a genuine boundary-cap L2 bound
by the original data on the same cap, uniformly in its radius. -/
theorem neumann_radial_interval_local_L2 {n q : ℕ} (a b : ℕ)
    (c : Domain n) (hc : ‖c‖=1) (s : ℝ)
    (u : Domain n → Ambient q)
    (hu : MemLp u 2 (volume.restrict (ball (0 : Domain n) 1))) :
    let A := {x : Domain n | 1<‖x‖ ∧ ‖x‖<2}
    let V := fun x : Domain n=>‖x‖^a • (∫t in (‖x‖⁻¹)^2..‖x‖⁻¹,t^b • u (t • x))
    MemLp V 2 (volume.restrict (A∩ball c s)) ∧
      (∫x in A∩ball c s,‖V x‖^2)≤(2:ℝ)^(2*a)*(4:ℝ)^n*
        (∫x in ball (0 : Domain n) 1∩ball c s,‖u x‖^2) := by
  intro A V
  let f := (ball c s).indicator u
  let W := fun x : Domain n=>‖x‖^a • (∫t in (‖x‖⁻¹)^2..‖x‖⁻¹,t^b • f (t • x))
  have hf : MemLp f 2 (volume.restrict (ball (0 : Domain n) 1)) := hu.indicator measurableSet_ball
  obtain ⟨_hJ,_hJ2,_hJE,_hAv,hW,hE⟩ := neumann_radial_interval_L2 a b f hf
  have hA : MeasurableSet A := (measurableSet_lt measurable_const measurable_norm).inter
    (measurableSet_lt measurable_norm measurable_const)
  have hSame : W=ᵐ[volume.restrict (A∩ball c s)]V := by
    filter_upwards [ae_restrict_mem (hA.inter measurableSet_ball)] with x hx
    exact neumann_radial_interval_cap_identity a b c hc s u x hx.1.1 hx.2
  have hInput : (∫x in ball (0 : Domain n) 1,‖f x‖^2)=
      ∫x in ball (0 : Domain n) 1∩ball c s,‖u x‖^2 := by
    have hPoint : (fun x=>‖f x‖^2)=(ball c s).indicator (fun x=>‖u x‖^2) := by
      funext x
      by_cases hx : x∈ball c s
      · simp only [f,indicator_of_mem hx]
      · simp only [f,indicator_of_notMem hx,norm_zero,zero_pow (by decide : (2:ℕ)≠0)]
    rw [hPoint,setIntegral_indicator measurableSet_ball]
  have hWM : MemLp W 2 (volume.restrict (A∩ball c s)) :=
    hW.mono_measure (Measure.restrict_mono_set volume inter_subset_left)
  refine ⟨hWM.ae_eq hSame,?_⟩
  calc
    _=∫x in A∩ball c s,‖W x‖^2 :=
      (integral_congr_ae (hSame.mono fun x hx=>congrArg (fun z=>‖z‖^2) hx)).symm
    _≤∫x in A,‖W x‖^2 := integral_mono_measure (Measure.restrict_mono_set volume inter_subset_left)
      (Eventually.of_forall fun x=>sq_nonneg _) (hW.integrable_norm_pow (by decide : (2:ℕ)≠0))
    _≤_ := by simpa only [hInput] using hE

end StationaryHarmonicMaps.Analysis

end
