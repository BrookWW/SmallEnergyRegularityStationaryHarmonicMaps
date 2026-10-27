module
public import HarmonicMaps.Frozen.TubularProjectionDerivativeWellDefined
@[expose] public section
namespace HarmonicMaps
noncomputable def tubularProjectionDerivative (q : ℕ) (N : CompactSmoothEmbeddedTarget q) :
    tubularTube q N → (Ambient q →L[ℝ] Ambient q) :=
  fun z => Classical.choose (tubularProjectionDerivativeWellDefined q N z)
end HarmonicMaps
end
