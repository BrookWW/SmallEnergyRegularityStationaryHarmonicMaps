module

public import StationaryHarmonicMaps.Analysis.C1SobolevPostcompositionLocal
public import HarmonicMaps.SobolevLemmas
public import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Linear operations on the actual local Sobolev graph

Continuous functions and their continuous C¹ derivative columns are L² on
compact subsets. Addition and fixed continuous linear maps preserve the
same explicitly displayed weak-gradient columns.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped ContDiff

namespace StationaryHarmonicMaps.Analysis

/-- A continuous Euclidean map is locally L² on every open domain. -/
theorem continuous_locallyMemL2 {n q : ℕ} (Ω : OpenDomain n)
    {f : Domain n → Ambient q} (hf : Continuous f) : LocallyMemL2 Ω f := by
  intro K hK _hs
  letI : IsFiniteMeasure (volume.restrict K) :=
    isFiniteMeasure_restrict.mpr hK.measure_ne_top
  obtain ⟨C, _hC, hbound⟩ := (hK.image hf).isBounded.exists_pos_norm_le
  apply MemLp.of_bound hf.aestronglyMeasurable C
  filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
  exact hbound (f x) ⟨x, hx, rfl⟩

/-- The actual C¹ differential supplies local Sobolev membership. -/
theorem memW12Loc_of_c1 {n q : ℕ} (Ω : OpenDomain n)
    {f : Domain n → Ambient q} (hf : ContDiff ℝ 1 f) :
    MemW12Loc Ω f (fun x i => fderiv ℝ f x (EuclideanSpace.single i 1)) :=
  ⟨hasWeakGradient_of_c1 Ω hf, continuous_locallyMemL2 Ω hf.continuous,
    fun _ => continuous_locallyMemL2 Ω
      ((hf.continuous_fderiv (by simp)).clm_apply continuous_const)⟩

/-- Weak-gradient addition uses the sum of the original displayed columns. -/
theorem hasWeakGradient_add {n q : ℕ} {Ω : OpenDomain n}
    {u v : Domain n → Ambient q} {Du Dv : Domain n → Gradient n q}
    (hu : HasWeakGradient Ω u Du) (hv : HasWeakGradient Ω v Dv) :
    HasWeakGradient Ω (u + v) (fun x i => Du x i + Dv x i) := by
  refine ⟨hu.1.add hv.1, fun i => (hu.2.1 i).add (hv.2.1 i), ?_⟩
  intro i φ hφ hc hs
  simp only [Pi.add_apply, smul_add]
  rw [integral_add (hu.integrable_test_derivative i hφ hc hs)
      (hv.integrable_test_derivative i hφ hc hs),
    integral_add (hu.integrable_test_gradient i hφ hc hs)
      (hv.integrable_test_gradient i hφ hc hs),
    hu.2.2 i φ hφ hc hs, hv.2.2 i φ hφ hc hs]
  abel

/-- Addition preserves literal W¹,² local membership and its original columns. -/
theorem memW12Loc_add {n q : ℕ} {Ω : OpenDomain n}
    {u v : Domain n → Ambient q} {Du Dv : Domain n → Gradient n q}
    (hu : MemW12Loc Ω u Du) (hv : MemW12Loc Ω v Dv) :
    MemW12Loc Ω (u + v) (fun x i => Du x i + Dv x i) :=
  ⟨hasWeakGradient_add hu.1 hv.1,
    fun K hK hs => (hu.2.1 K hK hs).add (hv.2.1 K hK hs),
    fun i K hK hs => (hu.2.2 i K hK hs).add (hv.2.2 i K hK hs)⟩

/-- A fixed continuous linear map acts on the given Sobolev gradient columns. -/
theorem memW12Loc_continuousLinearMap {n q k : ℕ} {Ω : OpenDomain n}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12Loc Ω u Du) (L : Ambient q →L[ℝ] Ambient k) :
    MemW12Loc Ω (fun x => L (u x)) (fun x i => L (Du x i)) := by
  have H := memW12Loc_postcompose_c1 hu L L.contDiff ‖L‖
    (fun y => by rw [L.fderiv])
  simpa only [L.fderiv, Function.comp_def] using H

end StationaryHarmonicMaps.Analysis

end
