module

public import StationaryHarmonicMaps.Analysis.ZeroBoundaryZeroExtension
public import HarmonicMaps.Analysis.SobolevPoincare
public import HolderToCK.Foundation.BallVolume

/-!
# Actual local boundary Poincare for the original zero extension

A unit-sphere point has a genuine exterior quarter-radius ball inside
every centered query ball. The original W0 graph gives a true full-space
zero extension, zero on that actual subball. The original native Poincare
variance and the exact volume ratio control its local map energy by the
same query ball's gradient energy. No trace or local estimate is assumed.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

private theorem integral_norm_sq_variance_identity {n q : ℕ}
    (μ : Measure (Domain n)) [IsFiniteMeasure μ]
    (u : Domain n → Ambient q) (hu : MemLp u 2 μ) :
    (∫ x,‖u x‖^2 ∂μ)=(∫ x,‖u x-(⨍ y,u y ∂μ)‖^2 ∂μ)+
      μ.real univ*‖(⨍ y,u y ∂μ)‖^2 := by
  let c := ⨍ y,u y ∂μ
  let g := fun x=>u x-c
  have hg : MemLp g 2 μ := hu.sub (memLp_const _)
  have hgi : Integrable g μ := hg.integrable (by norm_num)
  have hsq : Integrable (fun x=>‖g x‖^2) μ := hg.integrable_norm_pow (by decide : (2 : ℕ)≠0)
  have hz : (∫ x,g x ∂μ)=0 := integral_sub_average μ u
  have hi : Integrable (fun x=>2*inner ℝ c (g x)) μ := (hgi.const_inner c).const_mul 2
  have heq (x : Domain n) : u x=g x+c := by dsimp only [g];abel
  have hcomm (x : Domain n) : inner ℝ (g x) c=inner ℝ c (g x) := real_inner_comm _ _
  change (∫ x,‖u x‖^2 ∂μ)=(∫ x,‖g x‖^2 ∂μ)+μ.real univ*‖c‖^2
  conv_lhs => simp only [heq,norm_add_sq_real,hcomm]
  have hsum : Integrable (fun x=>‖g x‖^2+2*inner ℝ c (g x)) μ := hsq.add hi
  rw [integral_add hsum (integrable_const _),integral_add hsq hi,
    integral_const_mul,integral_inner hgi,hz,inner_zero_right,mul_zero,add_zero,integral_const]
  rfl

/-- Every positive query radius about an actual unit-sphere point contains a true exterior quarter-radius ball. -/
theorem sphere_exterior_quarter_ball {n : ℕ} (a : Domain n) (ha : ‖a‖=1)
    (r : ℝ) (hr : 0<r) :
    let z := (1+r/2) • a
    Metric.ball z (r/4)⊆Metric.ball a r ∧
      Metric.ball z (r/4)⊆(Metric.ball (0 : Domain n) 1)ᶜ := by
  intro z
  have hza : dist z a=r/2 := by
    rw [dist_eq_norm]
    have heq : z-a=(r/2) • a := by dsimp only [z];module
    rw [heq,norm_smul,Real.norm_of_nonneg (by positivity),ha,mul_one]
  have hzNorm : ‖z‖=1+r/2 := by
    rw [show z=(1+r/2) • a from rfl,norm_smul,Real.norm_of_nonneg (by positivity),ha,mul_one]
  constructor
  · intro x hx
    have hdist : dist x z<r/4 := hx
    change dist x a<r
    exact lt_of_le_of_lt (dist_triangle x z a) (by rw [hza];linarith)
  · intro x hx
    have hdist : ‖x-z‖<r/4 := by simpa only [Metric.mem_ball,dist_eq_norm] using hx
    have hTriangle : ‖z‖≤‖x‖+‖x-z‖ := by
      calc
        _ = ‖x-(x-z)‖ := by congr 1;abel
        _ ≤ _ := norm_sub_le _ _
    have hOutside : 1≤‖x‖ := by rw [hzNorm] at hTriangle;linarith
    simpa only [mem_compl_iff,Metric.mem_ball,dist_zero_right,not_lt] using hOutside

private theorem native_ball_poincare_zero_quarter_ball {n q : ℕ}
    (a z : Domain n) {r : ℝ} (hr : 0<r)
    (u : Domain n → Ambient q) (Du : Domain n → Gradient n q)
    (hu : MemW12 (ballDomain a r) u Du)
    (hSub : Metric.ball z (r/4)⊆Metric.ball a r)
    (hZero : u =ᵐ[volume.restrict (Metric.ball z (r/4))] (fun _=>0)) :
    (∫ x in Metric.ball a r,‖u x‖^2)≤
      (1+(4 : ℝ)^n)*((2 : ℝ)^(n+1)*r^2)*(∫ x in Metric.ball a r,hsNormSq (Du x)) := by
  let B := Metric.ball a r
  let Z := Metric.ball z (r/4)
  let μ := volume.restrict B
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  letI : IsFiniteMeasure (volume.restrict Z) := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  let c := ⨍ y,u y ∂μ
  let V := ∫ x,‖u x-c‖^2 ∂μ
  have hUL : MemLp u 2 μ := hu.2.1
  have hCenterLp : MemLp (fun x=>u x-c) 2 μ := hUL.sub (memLp_const _)
  have hCentered : Integrable (fun x=>‖u x-c‖^2) μ :=
    hCenterLp.integrable_norm_pow (by decide : (2 : ℕ)≠0)
  have hSubEnergy : volume.real Z*‖c‖^2≤V := by
    calc
      _ = ∫ x in Z,‖u x-c‖^2 := by
        calc
          _ = ∫ x in Z,‖c‖^2 := by rw [integral_const,measureReal_restrict_apply_univ,smul_eq_mul]
          _ = _ := integral_congr_ae (hZero.mono fun x hx=>by change u x=0 at hx; rw [hx,zero_sub,norm_neg])
      _ ≤ V := setIntegral_mono_set hCentered (Eventually.of_forall fun _=>sq_nonneg _)
        (Eventually.of_forall fun _ hx=>hSub hx)
  have hMass : (4 : ℝ)^n*volume.real Z=volume.real B := by
    rw [HolderToCK.ball_volume_real z (by positivity : 0<r/4),HolderToCK.ball_volume_real a hr]
    calc
      _ = ((4 : ℝ)*(r/4))^n*volume.real (Metric.ball (0 : Domain n) 1) := by rw [mul_pow];ring
      _ = _ := by congr 2;ring
  have hMean : volume.real B*‖c‖^2≤(4 : ℝ)^n*V := by
    rw [← hMass,mul_assoc]
    exact mul_le_mul_of_nonneg_left hSubEnergy (by positivity)
  have hIdentity := integral_norm_sq_variance_identity μ u hu.2.1
  have hPoincare : V≤(2 : ℝ)^(n+1)*r^2*(∫ x in B,hsNormSq (Du x)) := hu.poincare_ball hr
  calc
    _ = V+volume.real B*‖c‖^2 := by
      have hMassμ : μ.real univ=volume.real B := measureReal_restrict_apply_univ B
      rw [hMassμ] at hIdentity
      exact hIdentity
    _ ≤ V+(4 : ℝ)^n*V := add_le_add le_rfl hMean
    _ = (1+(4 : ℝ)^n)*V := by ring
    _ ≤ _ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hPoincare (by positivity : 0≤1+(4 : ℝ)^n)

/-- The literal zero extension of an original native W0 unit-ball graph satisfies genuine local boundary Poincare on every ball centered on the actual sphere. -/
theorem zeroBoundary_zeroExtension_boundary_poincare {n q : ℕ}
    (u : Domain n → Ambient q) (Du : Domain n → Gradient n q)
    (hu : HasZeroBoundaryValues (ballDomain (0 : Domain n) 1) u Du)
    (a : Domain n) (ha : ‖a‖=1) (r : ℝ) (hr : 0<r) :
    let U := (Metric.ball (0 : Domain n) 1).indicator u
    let DU := fun x i=>(Metric.ball (0 : Domain n) 1).indicator (fun y=>Du y i) x
    MemW12 (ballDomain a r) U DU ∧
      (∫ x in Metric.ball a r,‖U x‖^2)≤
        (1+(4 : ℝ)^n)*((2 : ℝ)^(n+1)*r^2)*(∫ x in Metric.ball a r,hsNormSq (DU x)) := by
  intro U DU
  obtain ⟨hFull,_hMap,_hGrad⟩ := zeroBoundary_zeroExtension_univ (ballDomain (0 : Domain n) 1) u Du hu
  have hNative : MemW12 (ballDomain a r) U DU :=
    ⟨hFull.1.1.mono (subset_univ _),hFull.1.2.1.mono_measure (Measure.restrict_mono_set volume (subset_univ _)),
      fun i=>(hFull.1.2.2 i).mono_measure (Measure.restrict_mono_set volume (subset_univ _))⟩
  obtain ⟨hSub,hOutside⟩ := sphere_exterior_quarter_ball a ha r hr
  have hZero : U =ᵐ[volume.restrict (Metric.ball ((1+r/2) • a) (r/4))] (fun _=>0) := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    exact indicator_of_notMem (hOutside hx) u
  exact ⟨hNative,native_ball_poincare_zero_quarter_ball a _ hr U DU hNative hSub hZero⟩

end StationaryHarmonicMaps.Analysis

end
