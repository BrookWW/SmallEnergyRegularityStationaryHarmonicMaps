module

public import StationaryHarmonicMaps.Analysis.SobolevLinearOperations
public import HarmonicMaps.SobolevRestriction
public import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity

/-!
# Genuine zero-boundary Sobolev graphs under fixed linear maps

The actual compact smooth graph approximation is composed with the given
continuous linear map. Its support stays inside the original support, and
the operator bound transfers both map and original gradient convergence.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped ContDiff Topology

namespace StationaryHarmonicMaps.Analysis

/-- A fixed continuous linear map preserves actual L2 convergence for the same representatives. -/
theorem tendsto_eLpNorm_continuousLinearMap {n q k : ℕ} (μ : Measure (Domain n))
    (L : Ambient q →L[ℝ] Ambient k) (f : ℕ → Domain n → Ambient q) (u : Domain n → Ambient q)
    (hlim : Tendsto (fun j => eLpNorm (f j-u) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun j => eLpNorm ((fun x => L (f j x)) - (fun x => L (u x))) 2 μ) atTop (𝓝 0) := by
  have H := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal ‖L‖) hlim
    (Or.inr ENNReal.ofReal_ne_top)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa only [mul_zero] using H) (fun _ => zero_le)
  intro j
  apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul (p := 2)
  apply Eventually.of_forall
  intro x
  change ‖L (f j x) - L (u x)‖ ≤ ‖L‖ * ‖f j x-u x‖
  rw [← map_sub]
  exact L.le_opNorm _

/-- The actual native W0 graph is preserved by a fixed continuous linear map. -/
theorem zeroBoundary_continuousLinearMap {n q k : ℕ} {Ω : OpenDomain n}
    {g : Domain n → Ambient q} {Dg : Domain n → Gradient n q}
    (hg : HasZeroBoundaryValues Ω g Dg) (L : Ambient q →L[ℝ] Ambient k) :
    HasZeroBoundaryValues Ω (fun x => L (g x)) (fun x i => L (Dg x i)) := by
  obtain ⟨hgW, f, hf, hc, hlim, hDlim⟩ := hg
  have hloc := memW12Loc_continuousLinearMap hgW.to_memW12Loc L
  have hW : MemW12 Ω (fun x => L (g x)) (fun x i => L (Dg x i)) :=
    ⟨hloc.1, L.lipschitz.comp_memLp (map_zero L) hgW.2.1,
      fun i => L.lipschitz.comp_memLp (map_zero L) (hgW.2.2 i)⟩
  have hs (j : ℕ) : ContDiff ℝ ∞ (fun x => L (f j x)) := L.contDiff.comp (hf j)
  have hsupport (j : ℕ) : tsupport (fun x => L (f j x)) ⊆ tsupport (f j) := by
    apply closure_mono
    intro x hx hz
    exact hx (by change L (f j x) = 0; rw [hz, map_zero])
  refine ⟨hW, (fun j x => L (f j x)), hs, ?_,
    tendsto_eLpNorm_continuousLinearMap _ L f g hlim, ?_⟩
  · intro j
    exact ⟨(hc j).1.of_isClosed_subset (isClosed_tsupport _) (hsupport j), (hsupport j).trans (hc j).2⟩
  · intro i
    have hd (j : ℕ) (x : Domain n) :
        coordinateDerivative (fun y => L (f j y)) (hs j) i x =
          L (coordinateDerivative (f j) (hf j) i x) := by
      change fderiv ℝ (L ∘ f j) x (EuclideanSpace.single i 1) = _
      rw [fderiv_comp x L.differentiableAt ((hf j).differentiable (by simp) x), L.fderiv]
      rfl
    have H := tendsto_eLpNorm_continuousLinearMap (volume.restrict Ω.val) L
      (fun j x => coordinateDerivative (f j) (hf j) i x) (fun x => Dg x i) (hDlim i)
    apply H.congr
    intro j
    congr 1
    funext x
    change L (coordinateDerivative (f j) (hf j) i x) - L (Dg x i) =
      coordinateDerivative (fun y => L (f j y)) (hs j) i x - L (Dg x i)
    rw [hd]

end StationaryHarmonicMaps.Analysis

end
