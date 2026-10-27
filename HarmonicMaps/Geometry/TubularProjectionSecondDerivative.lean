module
public import HarmonicMaps.Frozen.TubularProjectionSecondDerivativeWellDefined
@[expose] public section
namespace HarmonicMaps
noncomputable def tubularProjectionSecondDerivative (q : ℕ) (N : CompactSmoothEmbeddedTarget q) :
    tubularTube q N → (Ambient q →L[ℝ] (Ambient q →L[ℝ] Ambient q)) :=
  fun z => Classical.choose (tubularProjectionSecondDerivativeWellDefined q N z)
end HarmonicMaps
end
