module
public import HarmonicMaps.Frozen.TubularProjectionWellDefined
@[expose] public section
namespace HarmonicMaps
noncomputable def tubularBaseRadius (q : ℕ) (N : CompactSmoothEmbeddedTarget q) : ℝ :=
  Classical.choose (tubularProjectionWellDefined q N)
end HarmonicMaps
end
