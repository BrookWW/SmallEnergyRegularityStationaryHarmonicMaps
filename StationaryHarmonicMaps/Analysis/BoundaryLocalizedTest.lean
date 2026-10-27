module

public import StationaryHarmonicMaps.Analysis.ScaledBallCutoff
public import StationaryHarmonicMaps.Analysis.SobolevCutoff
public import StationaryHarmonicMaps.Analysis.CutoffGradientHSBound
public import HarmonicMaps.Analysis.SobolevPoincare
public import StationaryHarmonicMaps.Analysis.CriticalMorreyMeanOscillation

/-!
# Localized native tests across the source sphere

A fixed scaled cutoff of a native graph on the double ball has its actual
Leibniz columns. Centering on a larger query ball removes the zero-order
energy by Poincare, including for queries crossing the unit sphere.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped ContDiff Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

@[expose] def effectiveBoundaryLocalizedTestConstant (n : ℕ) : ℕ :=
  2 + 2 * n * (2 ^ 22) ^ 2 * (2 ^ (n + 1) * 16)

theorem effectiveBoundaryLocalizedTestConstant_pos (n : ℕ) :
    0 < (effectiveBoundaryLocalizedTestConstant n : ℝ) := by
  simp only [effectiveBoundaryLocalizedTestConstant, Nat.cast_add, Nat.cast_mul,
    Nat.cast_pow, Nat.cast_ofNat]
  positivity

/-- Every small query centered in the source ball has a genuine compact native
test with homogeneous energy controlled on the enlarged query ball. -/
theorem effective_boundary_localized_native_test_energy (n : ℕ) :
    ∀ (q : ℕ) (U : Domain n → Ambient q) (DU : Domain n → Gradient n q),
      MemW12 (ballDomain (0 : Domain n) 2) U DU →
      ∀ (a : Domain n),a∈ball (0 : Domain n) 1 → ∀ (r : ℝ),0<r → r≤1/8 →
      ∃χ : Domain n → ℝ,ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
        tsupport χ⊆ball a (2*r) ∧ (∀x∈closedBall a r,χ x=1) ∧
        (∀x,0≤χ x ∧ χ x≤1) ∧
        let c := ⨍x in ball a (4*r),U x
        let W := fun x=>χ x • (U x-c)
        let DW := fun x i=>χ x • DU x i+fderiv ℝ χ x (EuclideanSpace.single i 1) • (U x-c)
        MemW12 (⟨univ,isOpen_univ⟩ : OpenDomain n) W DW ∧
        (∫x in ball (0 : Domain n) 1,hsNormSq (DW x))≤
          (effectiveBoundaryLocalizedTestConstant n : ℝ)*(∫x in ball a (4*r),hsNormSq (DU x)) := by
  let A : ℝ := (2 : ℝ) ^ 22
  have Hχ := scaled_ball_cutoff_explicit n
  let C := 2+(2*(n : ℝ)*A^2)*((2 : ℝ)^(n+1)*16)
  have hC : 0<C := by dsimp only [C];positivity
  have hEq : (effectiveBoundaryLocalizedTestConstant n : ℝ) = C := by
    simp only [effectiveBoundaryLocalizedTestConstant, Nat.cast_add, Nat.cast_mul,
      Nat.cast_pow, Nat.cast_ofNat, C, A]
  rw [hEq]
  intro q U DU hU a ha r hr hrCap
  obtain ⟨χ,hχ,hcχ,hsχ,hOne,hBounds,hDχ⟩ := Hχ a r hr
  have hQuery : ball a (4*r)⊆ball (0 : Domain n) 2 := by
    intro x hx
    have hTri := dist_triangle x a (0 : Domain n)
    have hxa : dist x a<4*r := hx
    have ha0 : dist a (0 : Domain n)<1 := ha
    change dist x (0 : Domain n)<2
    linarith only [hTri,hxa,ha0,hrCap]
  have hLocal : MemW12 (ballDomain a (4*r)) U DU := memW12_of_openDomain_subset hU hQuery
  have hsLocal : tsupport χ⊆ball a (4*r) :=
    hsχ.trans (ball_subset_ball (by linarith only [hr] : 2*r≤4*r))
  refine ⟨χ,hχ,hcχ,hsχ,hOne,hBounds,?_⟩
  intro c W DW
  have hW : MemW12 (⟨univ,isOpen_univ⟩ : OpenDomain n) W DW :=
    memW12_cutoff_sub_const_univ hLocal.to_memW12Loc c χ hχ hcχ hsLocal
  let μ := volume.restrict (ball a (4*r))
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  have hUI : Integrable (fun x=>hsNormSq (DU x)) μ := hLocal.integrable_hsNormSq
  have hULp : MemLp U 2 μ := hLocal.2.1
  have hValueI : Integrable (fun x=>‖U x-c‖^2) μ :=
    (hULp.sub (memLp_const c)).integrable_norm_pow (by decide : (2 : ℕ)≠0)
  have hWI : Integrable (fun x=>hsNormSq (DW x)) volume := by
    have H := hW.integrable_hsNormSq
    change Integrable (fun x=>hsNormSq (DW x)) (volume.restrict univ) at H
    simpa only [Measure.restrict_univ] using H
  have hZero (x : Domain n) (hx : x∉ball a (4*r)) : hsNormSq (DW x)=0 := by
    have hxSupport : x∉tsupport χ := fun h=>hx (hsLocal h)
    simp only [DW,image_eq_zero_of_notMem_tsupport hxSupport,
      fderiv_of_notMem_tsupport (𝕜:=ℝ) hxSupport,zero_apply,zero_smul,add_zero,
      hsNormSq,norm_zero,zero_pow (by decide : (2 : ℕ)≠0),Finset.sum_const_zero]
  have hDeriv (x : Domain n) (i : Fin n) :
      |fderiv ℝ χ x (EuclideanSpace.single i 1)|≤A/r := by
    calc
      _≤‖fderiv ℝ χ x‖*‖EuclideanSpace.single i (1 : ℝ)‖ := (fderiv ℝ χ x).le_opNorm _
      _=‖fderiv ℝ χ x‖ := by simp only [PiLp.norm_single,norm_one,mul_one]
      _≤_ := hDχ x
  have hPoint (x : Domain n) : hsNormSq (DW x)≤
      2*hsNormSq (DU x)+(2*(n : ℝ)*(A/r)^2)*‖U x-c‖^2 := by
    simpa only [one_pow,mul_one] using cutoff_gradient_hsNormSq_le (A:=1) (B:=A/r)
      (DU x) (U x-c) (χ x) (fun i=>fderiv ℝ χ x (EuclideanSpace.single i 1))
      (by rw [abs_of_nonneg (hBounds x).1];exact (hBounds x).2) (hDeriv x)
  have hPoincare := hLocal.poincare_ball (mul_pos (by norm_num : (0 : ℝ)<4) hr)
  have hScale : (A/r)^2*(4*r)^2=A^2*16 := by field_simp;ring
  refine ⟨hW,?_⟩
  calc
    _≤∫x,hsNormSq (DW x) := integral_mono_measure Measure.restrict_le_self
      (Eventually.of_forall fun x=>hsNormSq_nonneg _) hWI
    _=∫x in ball a (4*r),hsNormSq (DW x) :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero hZero).symm
    _≤∫x in ball a (4*r),2*hsNormSq (DU x)+(2*(n : ℝ)*(A/r)^2)*‖U x-c‖^2 :=
      integral_mono hWI.integrableOn ((hUI.const_mul 2).add (hValueI.const_mul _)) hPoint
    _=2*(∫x in ball a (4*r),hsNormSq (DU x))+
        (2*(n : ℝ)*(A/r)^2)*(∫x in ball a (4*r),‖U x-c‖^2) := by
      change (∫x,2*hsNormSq (DU x)+(2*(n : ℝ)*(A/r)^2)*‖U x-c‖^2 ∂μ)=_
      rw [integral_add (hUI.const_mul 2) (hValueI.const_mul _),integral_const_mul,integral_const_mul]
    _≤C*(∫x in ball a (4*r),hsNormSq (DU x)) := by
      have H := mul_le_mul_of_nonneg_left hPoincare (show 0≤2*(n : ℝ)*(A/r)^2 by positivity)
      have hCoeff : (2*(n : ℝ)*(A/r)^2)*((2 : ℝ)^(n+1)*(4*r)^2)=
          (2*(n : ℝ)*A^2)*((2 : ℝ)^(n+1)*16) := by
        calc
          _=(2*(n : ℝ)*(2 : ℝ)^(n+1))*((A/r)^2*(4*r)^2) := by ring
          _=_ := by rw [hScale];ring
      rw [← mul_assoc] at H
      rw [hCoeff] at H
      dsimp only [C]
      linarith only [H]

/-- Every small query centered in the source ball has a genuine compact native
test with homogeneous energy controlled on the enlarged query ball. -/
theorem exists_boundary_localized_native_test_energy (n : ℕ) :
    ∃C : ℝ,0<C ∧ ∀ (q : ℕ) (U : Domain n → Ambient q) (DU : Domain n → Gradient n q),
      MemW12 (ballDomain (0 : Domain n) 2) U DU →
      ∀ (a : Domain n),a∈ball (0 : Domain n) 1 → ∀ (r : ℝ),0<r → r≤1/8 →
      ∃χ : Domain n → ℝ,ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
        tsupport χ⊆ball a (2*r) ∧ (∀x∈closedBall a r,χ x=1) ∧
        (∀x,0≤χ x ∧ χ x≤1) ∧
        let c := ⨍x in ball a (4*r),U x
        let W := fun x=>χ x • (U x-c)
        let DW := fun x i=>χ x • DU x i+fderiv ℝ χ x (EuclideanSpace.single i 1) • (U x-c)
        MemW12 (⟨univ,isOpen_univ⟩ : OpenDomain n) W DW ∧
        (∫x in ball (0 : Domain n) 1,hsNormSq (DW x))≤
          C*(∫x in ball a (4*r),hsNormSq (DU x)) := by
  exact ⟨(effectiveBoundaryLocalizedTestConstant n : ℝ), effectiveBoundaryLocalizedTestConstant_pos n,
    effective_boundary_localized_native_test_energy n⟩

end StationaryHarmonicMaps.Analysis

end
