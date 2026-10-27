module

public import HolderToCK.Analysis.WeakPoissonLocality
import HarmonicMaps.Analysis.SmoothWeakGradient
import StationaryHarmonicMaps.Analysis.NaturalCoulombTests

/-!
# The original weak Poisson equation from native natural tests

Smooth compact tests have their actual native graph on the same open
set. The given L2 columns supply the actual pairing integrability, and
the original natural equation gives the literal zero-forcing sign.
-/

public section

open HarmonicMaps MeasureTheory
open scoped ContDiff

namespace StationaryHarmonicMaps.Analysis

/-- Original L2 columns and their all-native natural zero equation imply
WeakPoissonOn for those same columns, on the same open domain and with
literal zero forcing. Every required test graph and integrable pairing
is produced internally. -/
theorem weakPoisson_zero_of_native_natural {n q : ℕ} (Ω : OpenDomain n)
    (Z : Domain n→Gradient n q)
    (hZ : ∀i,MemLp (fun x=>Z x i) 2 (volume.restrict Ω.val))
    (hNatural : ∀(ψ : Domain n→Ambient q) (Dψ : Domain n→Gradient n q),
      MemW12 Ω ψ Dψ →
      (∫x in Ω.val,∑i : Fin n,inner ℝ (Z x i) (Dψ x i))=0) :
    HolderToCK.WeakPoissonOn Ω Z (fun _=>(0 : Ambient q)) := by
  refine ⟨locallyIntegrableOn_zero,?_⟩
  intro ψ hψ hcψ _hsψ
  have hNative : MemW12 Ω ψ (fun x i=>fderiv ℝ ψ x (EuclideanSpace.single i 1)) := by
    apply memW12_of_contDiff Ω hψ
    · exact (hψ.continuous.memLp_of_hasCompactSupport hcψ).mono_measure Measure.restrict_le_self
    · intro i
      exact (((hψ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
        (hcψ.fderiv_apply ℝ (EuclideanSpace.single i 1))).mono_measure Measure.restrict_le_self
  refine ⟨integrable_column_pairing (volume.restrict Ω.val) Z _ hZ hNative.2.2,?_,?_⟩
  · simp only [inner_zero_left]
    exact integrable_zero _ _ _
  · have hZero := hNatural ψ _ hNative
    simpa only [inner_zero_left,integral_zero,neg_zero] using hZero

end StationaryHarmonicMaps.Analysis
