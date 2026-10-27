module

public import StationaryHarmonicMaps.Analysis.BoundaryEvenPowerGrowth
public import StationaryHarmonicMaps.Analysis.SobolevCutoff
public import StationaryHarmonicMaps.Analysis.CutoffGradientHSBound
public import HarmonicMaps.Analysis.SobolevPoincare
public import HarmonicMaps.Analysis.SobolevLocality

/-!
# Boundary-compatible native tests with homogeneous energy control

Even inversion and a fixed cutoff extend a native ball graph, after one
constant subtraction, to a zero-boundary graph on the double ball. Its
original gradient is unchanged throughout the source ball, and its full
energy is controlled by the original gradient energy alone.
-/

public section

open HarmonicMaps EuclideanGeometry MeasureTheory Filter Set Metric
open StationaryHarmonicMaps.Geometry
open scoped Topology ENNReal ContDiff

namespace StationaryHarmonicMaps.Analysis

/-- Every native graph has a genuine zero-boundary extension of its centered
value with exactly its original gradient on the entire source ball. -/
theorem exists_native_boundary_test_extension (n : ℕ) (hn : 2≤n) :
    ∃ C : ℝ,0<C ∧ ∀ (q : ℕ) (w : Domain n → Ambient q)
      (Dw : Domain n → Gradient n q),MemW12 (ballDomain (0 : Domain n) 1) w Dw →
      ∃ (c : Ambient q) (W : Domain n → Ambient q) (DW : Domain n → Gradient n q),
        HasZeroBoundaryValues (ballDomain (0 : Domain n) 2) W DW ∧
        (∀ x∈ball (0 : Domain n) 1,W x=w x-c) ∧
        (∀ x∈ball (0 : Domain n) 1,∀ i,DW x i=Dw x i) ∧
        (∫x in ball (0 : Domain n) 2,hsNormSq (DW x))≤
          C*(∫x in ball (0 : Domain n) 1,hsNormSq (Dw x)) := by
  let χ : ContDiffBump (0 : Domain n) := ⟨1,3/2,by norm_num,by norm_num⟩
  have hχ : ContDiff ℝ ∞ (χ : Domain n → ℝ) := χ.contDiff
  obtain ⟨B,hB⟩ := (χ.hasCompactSupport.fderiv ℝ).exists_bound_of_continuous
    (hχ.continuous_fderiv (by simp))
  have hDχ (x : Domain n) (i : Fin n) :
      |fderiv ℝ (χ : Domain n → ℝ) x (EuclideanSpace.single i 1)|≤|B| := by
    calc
      _≤‖fderiv ℝ (χ : Domain n → ℝ) x‖*‖EuclideanSpace.single i (1 : ℝ)‖ :=
        (fderiv ℝ (χ : Domain n → ℝ) x).le_opNorm _
      _=‖fderiv ℝ (χ : Domain n → ℝ) x‖ := by simp only [PiLp.norm_single,norm_one,mul_one]
      _≤|B| := (hB x).trans (le_abs_self B)
  let A := 2+2*(n : ℝ)*|B|^2*((2 : ℝ)^(n+1)*2^2)
  let E := 1+(2 : ℝ)^(2*n)
  have hA : 0<A := by dsimp only [A];positivity
  have hE : 0<E := by dsimp only [E];positivity
  refine ⟨A*E,mul_pos hA hE,?_⟩
  intro q w Dw hw
  let I := inversion (0 : Domain n) 1
  let U := fun x=>if ‖x‖≤1 then w x else w (I x)
  let DU := fun x i=>if ‖x‖≤1 then Dw x i else
    ∑j : Fin n,(fderiv ℝ I x (EuclideanSpace.single i 1)) j • Dw (I x) j
  have hU : MemW12 (ballDomain (0 : Domain n) 2) U DU :=
    memW12_even_inversion_extension_ball_two hn w Dw hw
  let μ := volume.restrict (ball (0 : Domain n) 2)
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  let c := ⨍x in ball (0 : Domain n) 2,U x
  let W := fun x=>χ x • (U x-c)
  let DW := fun x i=>χ x • DU x i+fderiv ℝ (χ : Domain n → ℝ) x (EuclideanSpace.single i 1) • (U x-c)
  have hsχ : tsupport (χ : Domain n → ℝ)⊆ball (0 : Domain n) 2 := by
    rw [χ.tsupport_eq]
    exact closedBall_subset_ball (by norm_num)
  have hW : MemW12 (ballDomain (0 : Domain n) 2) W DW :=
    memW12_cutoff_sub_const hU.to_memW12Loc c χ hχ χ.hasCompactSupport hsχ
  have hW0 : HasZeroBoundaryValues (ballDomain (0 : Domain n) 2) W DW :=
    hW.zeroBoundary_of_compactSupport_ball (by norm_num)
      (χ.hasCompactSupport.smul_right) ((tsupport_smul_subset_left _ _).trans hsχ)
  have hDW (x : Domain n) (hx : x∈ball (0 : Domain n) 1) (i : Fin n) : DW x i=Dw x i := by
    have hOne : χ x=1 := χ.one_of_mem_closedBall (ball_subset_closedBall hx)
    have hdZero : fderiv ℝ (χ : Domain n → ℝ) x=0 := by
      rw [(χ.eventuallyEq_one_of_mem_ball hx).fderiv_eq]
      exact (hasFDerivAt_const (1 : ℝ) x).fderiv
    have hxNorm : ‖x‖≤1 := (mem_ball_zero_iff.mp hx).le
    simp only [DW,hOne,one_smul,hdZero,zero_apply,zero_smul,add_zero,DU,if_pos hxNorm]
  have hULp : MemLp U 2 μ := hU.2.1
  have hUI : Integrable (fun x=>hsNormSq (DU x)) μ := hU.integrable_hsNormSq
  have hCenteredI : Integrable (fun x=>‖U x-c‖^2) μ :=
    (hULp.sub (memLp_const c)).integrable_norm_pow (by decide : (2 : ℕ)≠0)
  have hEnergy : (∫x in ball (0 : Domain n) 2,hsNormSq (DU x))≤
      E*(∫x in ball (0 : Domain n) 1,hsNormSq (Dw x)) := by
    have hGrowth (a : Domain n) (_ha : a∈ball (0 : Domain n) 1) (r : ℝ) (_hr : 0<r) :
        (∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (Dw x))≤
          (∫x in ball (0 : Domain n) 1,hsNormSq (Dw x))*r^(0 : ℝ) := by
      rw [Real.rpow_zero,mul_one]
      exact setIntegral_mono_set hw.integrable_hsNormSq
        (Eventually.of_forall fun _=>hsNormSq_nonneg _) (Eventually.of_forall fun _ hx=>hx.2)
    have H := even_inversion_power_growth_unitBall hn 0 w Dw hw
      (∫x in ball (0 : Domain n) 1,hsNormSq (Dw x))
      (integral_nonneg fun _=>hsNormSq_nonneg _) hGrowth (0 : Domain n) 2 (by norm_num)
    simpa only [Real.rpow_zero,one_mul,mul_one,inter_self] using H
  refine ⟨c,W,DW,hW0,?_,hDW,?_⟩
  · intro x hx
    have hxNorm : ‖x‖≤1 := (mem_ball_zero_iff.mp hx).le
    simp only [W,χ.one_of_mem_closedBall (ball_subset_closedBall hx),one_smul,U,if_pos hxNorm]
  · have hPoint (x : Domain n) : hsNormSq (DW x)≤
        2*hsNormSq (DU x)+(2*(n : ℝ)*|B|^2)*‖U x-c‖^2 := by
      simpa only [one_pow,mul_one] using cutoff_gradient_hsNormSq_le (A:=1) (B:=|B|) (DU x) (U x-c)
        (χ x) (fun i=>fderiv ℝ (χ : Domain n → ℝ) x (EuclideanSpace.single i 1))
        (by rw [abs_of_nonneg χ.nonneg];exact χ.le_one) (hDχ x)
    have H := hU.poincare_ball (by norm_num : (0 : ℝ)<2)
    calc
      _≤∫x in ball (0 : Domain n) 2,2*hsNormSq (DU x)+(2*(n : ℝ)*|B|^2)*‖U x-c‖^2 :=
        integral_mono hW.integrable_hsNormSq
          ((hU.integrable_hsNormSq.const_mul 2).add (hCenteredI.const_mul _)) hPoint
      _=2*(∫x in ball (0 : Domain n) 2,hsNormSq (DU x))+
          (2*(n : ℝ)*|B|^2)*(∫x in ball (0 : Domain n) 2,‖U x-c‖^2) := by
        change (∫x,2*hsNormSq (DU x)+(2*(n : ℝ)*|B|^2)*‖U x-c‖^2 ∂μ)=_
        rw [integral_add (hUI.const_mul 2) (hCenteredI.const_mul _),
          integral_const_mul,integral_const_mul]
      _≤A*(∫x in ball (0 : Domain n) 2,hsNormSq (DU x)) := by
        dsimp only [A]
        nlinarith only [mul_le_mul_of_nonneg_left H (by positivity : 0≤2*(n : ℝ)*|B|^2)]
      _≤A*(E*(∫x in ball (0 : Domain n) 1,hsNormSq (Dw x))) :=
        mul_le_mul_of_nonneg_left hEnergy hA.le
      _=_ := by ring

end StationaryHarmonicMaps.Analysis

end
