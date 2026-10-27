module

public import StationaryHarmonicMaps.Analysis.ZeroBoundaryZeroExtension
public import StationaryHarmonicMaps.Analysis.NeumannGradientSpace
public import HarmonicMaps.Analysis.SmoothBallZeroBoundary
public import HarmonicMaps.Analysis.SobolevDifference

/-!
# Native gluing of smooth fields with matching sphere values

The smooth difference has actual zero-boundary graph closure on the ball.
Its literal zero extension supplies the native interface, without requiring
matching normal derivatives. This applies to the continuous sphere matching
in the Neumann Kelvin reflection.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped ContDiff Topology

namespace StationaryHarmonicMaps.Analysis

/-- Matching smooth sphere values produce the genuine native piecewise graph and its original inside/outside derivative columns. -/
theorem memW12_smooth_sphere_gluing_ball {n q : ℕ} (hn : 2≤n) (r : PositiveRadius)
    (u v : Domain n → Ambient q) (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (hSphere : ∀x∈sphere (0 : Domain n) r.val,u x=v x) (R : ℝ) :
    let Du := fun x i=>fderiv ℝ u x (EuclideanSpace.single i 1)
    let Dv := fun x i=>fderiv ℝ v x (EuclideanSpace.single i 1)
    let U := fun x=>v x+(ball (0 : Domain n) r.val).indicator (u-v) x
    let DU := fun x i=>Dv x i+(ball (0 : Domain n) r.val).indicator (fun y=>Du y i-Dv y i) x
    MemW12 (ballDomain (0 : Domain n) R) U DU ∧
      (∀x∈ball (0 : Domain n) r.val,U x=u x ∧ DU x=Du x) ∧
      (∀x∉ball (0 : Domain n) r.val,U x=v x ∧ DU x=Dv x) := by
  intro Du Dv U DU
  let B := ball (0 : Domain n) r.val
  let Ω := ballDomain (0 : Domain n) R
  have hDiffSmooth : ContDiff ℝ ∞ (u-v) := hu.sub hv
  have hDiffBoundary : ∀x∈sphere (0 : Domain n) r.val,(u-v) x=0 := by
    intro x hx
    exact sub_eq_zero.mpr (hSphere x hx)
  have hD (x : Domain n) (i : Fin n) :
      fderiv ℝ (u-v) x (EuclideanSpace.single i 1)=Du x i-Dv x i := by
    rw [fderiv_sub (hu.differentiable (by simp) x) (hv.differentiable (by simp) x)]
    rfl
  have hW0 := smooth_zeroBoundary_ball hn r univ isOpen_univ (subset_univ _) (u-v)
    hDiffSmooth.contDiffOn hDiffBoundary
  have hW0' : HasZeroBoundaryValues (ballDomain (0 : Domain n) r.val) (u-v)
      (fun x i=>Du x i-Dv x i) := by simpa only [hD] using hW0
  have hExt := (zeroBoundary_zeroExtension_univ (ballDomain (0 : Domain n) r.val) (u-v)
    (fun x i=>Du x i-Dv x i) hW0').1.1
  have hExtΩ : MemW12 Ω (B.indicator (u-v))
      (fun x i=>B.indicator (fun y=>Du y i-Dv y i) x) := by
    refine ⟨hExt.1.mono (subset_univ _),?_,?_⟩
    · have H := hExt.2.1
      change MemLp (B.indicator (u-v)) 2 (volume.restrict univ) at H
      rw [Measure.restrict_univ] at H
      exact H.mono_measure Measure.restrict_le_self
    · intro i
      have H := hExt.2.2 i
      change MemLp (fun x=>B.indicator (fun y=>Du y i-Dv y i) x) 2 (volume.restrict univ) at H
      rw [Measure.restrict_univ] at H
      exact H.mono_measure Measure.restrict_le_self
  have hvW : MemW12 Ω v Dv := memW12_ball_of_ambient_c1 (0 : Domain n) R v (hv.of_le (by simp))
  refine ⟨⟨hasWeakGradient_add hvW.1 hExtΩ.1,hvW.2.1.add hExtΩ.2.1,
    fun i=>(hvW.2.2 i).add (hExtΩ.2.2 i)⟩,?_,?_⟩
  · intro x hx
    constructor
    · dsimp only [U]
      rw [indicator_of_mem hx]
      change v x+(u x-v x)=u x
      abel
    · funext i
      dsimp only [DU]
      rw [indicator_of_mem hx]
      abel
  · intro x hx
    constructor
    · dsimp only [U]
      rw [indicator_of_notMem hx,add_zero]
    · funext i
      dsimp only [DU]
      rw [indicator_of_notMem hx,add_zero]

end StationaryHarmonicMaps.Analysis

end
