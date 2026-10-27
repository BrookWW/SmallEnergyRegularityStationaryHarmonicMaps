module

public import StationaryHarmonicMaps.Analysis.SobolevWeakGradientClosure
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
public import HarmonicMaps.Energy

/-!
# The actual zero extension of a native zero-boundary graph

The original compact graph approximants and all their actual derivative
columns vanish outside the original open domain. Their global L2 errors
are exactly the original restricted errors. Actual strong/weak graph
closure therefore gives the full-space native graph, and the same
approximants give its genuine W0 closure. Both map and HS gradient square
energies are exactly the original restricted energies.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff

namespace StationaryHarmonicMaps.Analysis

/-- A genuine native W0 graph extends by literal zero to a genuine full-space W0 graph, preserving both actual energies. -/
theorem zeroBoundary_zeroExtension_univ {n q : ℕ} (Ω : OpenDomain n)
    (u : Domain n → Ambient q) (Du : Domain n → Gradient n q)
    (hu : HasZeroBoundaryValues Ω u Du) :
    HasZeroBoundaryValues (⟨univ,isOpen_univ⟩ : OpenDomain n) (Ω.val.indicator u)
      (fun x i => Ω.val.indicator (fun y => Du y i) x) ∧
      (∫ x,‖Ω.val.indicator u x‖^2)=(∫ x in Ω.val,‖u x‖^2) ∧
      (∫ x,hsNormSq (fun i => Ω.val.indicator (fun y => Du y i) x))=
        ∫ x in Ω.val,hsNormSq (Du x) := by
  obtain ⟨huW,f,hf,hc,hlim,hDlim⟩ := hu
  let U : OpenDomain n := ⟨univ,isOpen_univ⟩
  let v : Domain n → Ambient q := Ω.val.indicator u
  let Dv : Domain n → Gradient n q := fun x i => Ω.val.indicator (fun y => Du y i) x
  let Df : ℕ → Domain n → Gradient n q := fun k x i => coordinateDerivative (f k) (hf k) i x
  have hv : MemLp v 2 volume := (memLp_indicator_iff_restrict Ω.property.measurableSet).mpr huW.2.1
  have hDv (i : Fin n) : MemLp (fun x => Dv x i) 2 volume :=
    (memLp_indicator_iff_restrict Ω.property.measurableSet).mpr (huW.2.2 i)
  have hfL (k : ℕ) : MemLp (f k) 2 volume := (hf k).continuous.memLp_of_hasCompactSupport (hc k).1
  have hDfL (k : ℕ) (i : Fin n) : MemLp (fun x => Df k x i) 2 volume :=
    ((hf k).continuous_fderiv (by simp) |>.clm_apply continuous_const).memLp_of_hasCompactSupport
      ((hc k).1.fderiv_apply ℝ (EuclideanSpace.single i 1))
  have hfZero (k : ℕ) (x : Domain n) (hx : x∉Ω.val) : f k x=0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hx ((hc k).2 h))
  have hDfZero (k : ℕ) (i : Fin n) (x : Domain n) (hx : x∉Ω.val) : Df k x i=0 := by
    change fderiv ℝ (f k) x (EuclideanSpace.single i 1)=0
    rw [fderiv_of_notMem_tsupport (𝕜 := ℝ) (fun h => hx ((hc k).2 h)),zero_apply]
  have hMapEq (k : ℕ) : Ω.val.indicator (f k-u)=f k-v := by
    funext x
    by_cases hx : x∈Ω.val
    · simp only [indicator_of_mem hx,Pi.sub_apply,v]
    · simp only [indicator_of_notMem hx,Pi.sub_apply,v]
      rw [hfZero k x hx,sub_zero]
  have hGradEq (k : ℕ) (i : Fin n) :
      Ω.val.indicator (fun x => Df k x i-Du x i)=(fun x => Df k x i-Dv x i) := by
    funext x
    by_cases hx : x∈Ω.val
    · simp only [indicator_of_mem hx,Dv]
    · simp only [indicator_of_notMem hx,Dv]
      rw [hDfZero k i x hx,sub_zero]
  have hMapNorm (k : ℕ) : eLpNorm (f k-v) 2 volume=eLpNorm (f k-u) 2 (volume.restrict Ω.val) := by
    rw [← hMapEq,eLpNorm_indicator_eq_eLpNorm_restrict Ω.property.measurableSet]
  have hGradNorm (k : ℕ) (i : Fin n) : eLpNorm (fun x => Df k x i-Dv x i) 2 volume=
      eLpNorm (fun x => Df k x i-Du x i) 2 (volume.restrict Ω.val) := by
    rw [← hGradEq,eLpNorm_indicator_eq_eLpNorm_restrict Ω.property.measurableSet]
  have hMapLim : Tendsto (fun k => eLpNorm (f k-v) 2 volume) atTop (𝓝 0) := by
    simpa only [hMapNorm] using hlim
  have hGradLim (i : Fin n) : Tendsto (fun k => eLpNorm (fun x => Df k x i-Dv x i) 2 volume)
      atTop (𝓝 0) := by
    simpa only [hGradNorm] using hDlim i
  have hSeq (k : ℕ) : MemW12 U (f k) (Df k) := by
    refine ⟨hasWeakGradient_of_c1 U ((hf k).of_le (by simp)),?_,?_⟩
    · simpa only [U,Measure.restrict_univ] using hfL k
    · intro i
      simpa only [U,Measure.restrict_univ] using hDfL k i
  have hWeak (i : Fin n) (g : Domain n → Ambient q) (hg : MemLp g 2 (volume.restrict U.val)) :
      Tendsto (fun k => ∫ x in U.val,inner ℝ (Df k x i) (g x)) atTop
        (𝓝 (∫ x in U.val,inner ℝ (Dv x i) (g x))) := by
    have hg' : MemLp g 2 volume := by simpa only [U,Measure.restrict_univ] using hg
    have H := HolderToCK.tendsto_integral_inner_of_L2 (fun k => hDfL k i) (hDv i) hg' (hGradLim i)
    simpa only [U,Measure.restrict_univ,real_inner_comm] using H
  have hW : MemW12 U v Dv := memW12_of_strong_map_weak_gradient_L2 U f Df hSeq v Dv
    (by simpa only [U,Measure.restrict_univ] using hv)
    (fun i => by simpa only [U,Measure.restrict_univ] using hDv i)
    (by simpa only [U,Measure.restrict_univ] using hMapLim) hWeak
  have hZero : HasZeroBoundaryValues U v Dv := by
    refine ⟨hW,f,hf,fun k => ⟨(hc k).1,subset_univ _⟩,?_,?_⟩
    · simpa only [U,Measure.restrict_univ] using hMapLim
    · intro i
      simpa only [U,Measure.restrict_univ] using hGradLim i
  have hMapEnergy : (fun x => ‖v x‖^2)=Ω.val.indicator (fun x => ‖u x‖^2) := by
    funext x
    by_cases hx : x∈Ω.val
    · simp only [v,indicator_of_mem hx]
    · simp only [v,indicator_of_notMem hx,norm_zero,zero_pow (by decide : (2 : ℕ)≠0)]
  have hGradEnergy : (fun x => hsNormSq (Dv x))=Ω.val.indicator (fun x => hsNormSq (Du x)) := by
    funext x
    by_cases hx : x∈Ω.val
    · simp only [Dv,indicator_of_mem hx]
    · simp only [Dv,indicator_of_notMem hx,hsNormSq,norm_zero,zero_pow (by decide : (2 : ℕ)≠0),Finset.sum_const_zero]
  refine ⟨hZero,?_,?_⟩
  · change (∫ x,‖v x‖^2)=_
    rw [hMapEnergy,integral_indicator Ω.property.measurableSet]
  · change (∫ x,hsNormSq (Dv x))=_
    rw [hGradEnergy,integral_indicator Ω.property.measurableSet]

end StationaryHarmonicMaps.Analysis

end
