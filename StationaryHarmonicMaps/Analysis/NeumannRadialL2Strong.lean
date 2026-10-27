/- Copyright (c) 2026. All rights reserved. -/
module

public import StationaryHarmonicMaps.Analysis.NeumannRadialL2Interval
public import HarmonicMaps.Analysis.VariableMollificationL2

/-!
# Strong L2 transport through the actual radial reflection interval

The joint weighted pullbacks and the actual variable-interval averages
preserve strong convergence of the original raw L2 representatives.
Linearity is applied only after genuine fibre integrability is established.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- The same actual radial averages preserve subtraction after the original
joint integrability supplies both fibre integrals. -/
theorem neumann_radial_interval_sub_ae {n q : ℕ} (a b : ℕ)
    (u v : Domain n → Ambient q)
    (hu : MemLp u 2 (volume.restrict (ball (0 : Domain n) 1)))
    (hv : MemLp v 2 (volume.restrict (ball (0 : Domain n) 1))) :
    let A := {x : Domain n | 1<‖x‖ ∧ ‖x‖<2}
    let V := fun (f : Domain n → Ambient q) (x : Domain n)=>‖x‖^a •
      (∫t in (‖x‖⁻¹)^2..‖x‖⁻¹,t^b • f (t • x))
    V (u-v)=ᵐ[volume.restrict A](V u-V v) := by
  intro A V
  have hA : MeasurableSet A := (measurableSet_lt measurable_const measurable_norm).inter
    (measurableSet_lt measurable_norm measurable_const)
  obtain ⟨hJU,_hJU2,_hUJE,hUA,_hUM,_hUE⟩ := neumann_radial_interval_L2 a b u hu
  obtain ⟨hJV,_hJV2,_hVJE,hVA,_hVM,_hVE⟩ := neumann_radial_interval_L2 a b v hv
  have hDA := (neumann_radial_interval_L2 a b (u-v) (hu.sub hv)).2.2.2.1
  filter_upwards [ae_restrict_mem hA,
    hJU.prod_right_ae.filter_mono (ae_mono Measure.restrict_le_self),
    hJV.prod_right_ae.filter_mono (ae_mono Measure.restrict_le_self)] with x hx hUx hVx
  let w := fun t : ℝ=>if x∈A ∧ (‖x‖⁻¹)^2≤t ∧ t≤‖x‖⁻¹ then ‖x‖^a*t^b else 0
  have hLin : (∫t in Icc (1/4:ℝ) 1,w t • (u-v) (t • x))=
      (∫t in Icc (1/4:ℝ) 1,w t • u (t • x))-
        ∫t in Icc (1/4:ℝ) 1,w t • v (t • x) := by
    simp only [Pi.sub_apply,smul_sub]
    exact integral_sub hUx hVx
  exact (hDA x hx).symm.trans (hLin.trans
    (congrArg₂ (fun s t : Ambient q=>s-t) (hUA x hx) (hVA x hx)))

/-- Equality of the original B1 representatives almost everywhere is preserved
by the same actual radial interval average on the exterior annulus. -/
theorem neumann_radial_interval_congr_ae {n q : ℕ} (a b : ℕ)
    (u v : Domain n → Ambient q)
    (hu : MemLp u 2 (volume.restrict (ball (0 : Domain n) 1)))
    (hv : MemLp v 2 (volume.restrict (ball (0 : Domain n) 1)))
    (hEq : u=ᵐ[volume.restrict (ball (0 : Domain n) 1)]v) :
    let A := {x : Domain n | 1<‖x‖ ∧ ‖x‖<2}
    let V := fun (f : Domain n → Ambient q) (x : Domain n)=>‖x‖^a •
      (∫t in (‖x‖⁻¹)^2..‖x‖⁻¹,t^b • f (t • x))
    V u=ᵐ[volume.restrict A]V v := by
  intro A V
  obtain ⟨_hJ,_hJ2,_hJE,_hAv,hM,hE⟩ := neumann_radial_interval_L2 a b (u-v) (hu.sub hv)
  have hZeroInput : (∫x in ball (0 : Domain n) 1,‖(u-v) x‖^2)=0 := by
    calc
      _=∫_x in ball (0 : Domain n) 1,(0:ℝ) := integral_congr_ae
        (hEq.mono fun x hx=>by simp only [Pi.sub_apply,hx,sub_self,norm_zero,zero_pow (by decide : (2:ℕ)≠0)])
      _=0 := by simp only [integral_zero]
  rw [hZeroInput,mul_zero] at hE
  have hZero : (∫x in A,‖V (u-v) x‖^2)=0 :=
    le_antisymm hE (integral_nonneg fun x=>sq_nonneg ‖V (u-v) x‖)
  have hNorm : ∀ᵐx∂volume.restrict A,‖V (u-v) x‖^2=0 :=
    (integral_eq_zero_iff_of_nonneg (fun x=>sq_nonneg _) (hM.integrable_norm_pow (by decide : (2:ℕ)≠0))).mp hZero
  filter_upwards [hNorm,neumann_radial_interval_sub_ae a b u v hu hv] with x hx hSub
  have hz : V (u-v) x=0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hx)
  have hh : V u x-V v x=0 := hSub.symm.trans hz
  exact sub_eq_zero.mp hh

/-- Strong convergence of the original field gives strong convergence of both
actual joint radial integrands and the same variable-interval averages. -/
theorem neumann_radial_interval_strong_L2 {n q : ℕ} (a b : ℕ)
    (u : ℕ → Domain n → Ambient q) (v : Domain n → Ambient q)
    (hu : ∀k,MemLp (u k) 2 (volume.restrict (ball (0 : Domain n) 1)))
    (hv : MemLp v 2 (volume.restrict (ball (0 : Domain n) 1)))
    (hConv : Tendsto (fun k=>eLpNorm (u k-v) 2
      (volume.restrict (ball (0 : Domain n) 1))) atTop (𝓝 0)) :
    let A := {x : Domain n | 1<‖x‖ ∧ ‖x‖<2}
    let w := fun p : Domain n × ℝ=>if p.1∈A ∧ (‖p.1‖⁻¹)^2≤p.2 ∧ p.2≤‖p.1‖⁻¹
      then ‖p.1‖^a*p.2^b else 0
    let V := fun (f : Domain n → Ambient q) (x : Domain n)=>‖x‖^a •
      (∫t in (‖x‖⁻¹)^2..‖x‖⁻¹,t^b • f (t • x))
    Tendsto (fun k=>eLpNorm (fun p : Domain n × ℝ=>
        w p • (u k (p.2 • p.1)-v (p.2 • p.1))) 2
          (volume.prod (volume.restrict (Icc (1/4:ℝ) 1)))) atTop (𝓝 0) ∧
      Tendsto (fun k=>eLpNorm (V (u k)-V v) 2 (volume.restrict A)) atTop (𝓝 0) := by
  intro A w V
  let μ := volume.restrict (ball (0 : Domain n) 1)
  let ν := volume.restrict A
  let σ := volume.restrict (Icc (1/4:ℝ) 1)
  let C := (2:ℝ)^(2*a)*(4:ℝ)^n
  have hF (k : ℕ) : MemLp (u k-v) 2 μ := (hu k).sub hv
  have hInput : Tendsto (fun k=>∫x,‖(u k-v) x‖^2 ∂μ) atTop (𝓝 0) :=
    tendsto_integral_norm_sq_zero_of_eLpNorm_two hF hConv
  have hUpper : Tendsto (fun k=>C*(∫x,‖(u k-v) x‖^2 ∂μ)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hInput.const_mul C
  let J := fun (k : ℕ) (p : Domain n × ℝ)=>w p • (u k (p.2 • p.1)-v (p.2 • p.1))
  have hJointData (k : ℕ) := neumann_radial_interval_L2 a b (u k-v) (hF k)
  have hJM (k : ℕ) : MemLp (J k) 2 (volume.prod σ) :=
    (memLp_two_iff_integrable_sq_norm (hJointData k).1.aestronglyMeasurable).mpr (hJointData k).2.1
  have hJE : Tendsto (fun k=>∫p,‖J k p‖^2 ∂volume.prod σ) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hUpper
      (fun k=>integral_nonneg fun p=>sq_nonneg ‖J k p‖) (fun k=>(hJointData k).2.2.1)
  refine ⟨tendsto_eLpNorm_two_zero_of_integral_norm_sq hJM hJE,?_⟩
  obtain ⟨_hJV,_hJV2,_hVJE,_hVA,hVM,_hVE⟩ := neumann_radial_interval_L2 a b v hv
  have hUM (k : ℕ) : MemLp (V (u k)) 2 ν := (neumann_radial_interval_L2 a b (u k) (hu k)).2.2.2.2.1
  have hDM (k : ℕ) : MemLp (V (u k)-V v) 2 ν := (hUM k).sub hVM
  have hLinearity (k : ℕ) : V (u k-v)=ᵐ[ν](V (u k)-V v) :=
    neumann_radial_interval_sub_ae a b (u k) v (hu k) hv
  have hOutBound (k : ℕ) : (∫x,‖(V (u k)-V v) x‖^2 ∂ν)≤C*(∫x,‖(u k-v) x‖^2 ∂μ) := by
    rw [← integral_congr_ae ((hLinearity k).mono fun x hx=>congrArg (fun z=>‖z‖^2) hx)]
    exact (hJointData k).2.2.2.2.2
  have hOutE : Tendsto (fun k=>∫x,‖(V (u k)-V v) x‖^2 ∂ν) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hUpper
      (fun k=>integral_nonneg fun x=>sq_nonneg ‖(V (u k)-V v) x‖) hOutBound
  exact tendsto_eLpNorm_two_zero_of_integral_norm_sq hDM hOutE

end StationaryHarmonicMaps.Analysis

end
