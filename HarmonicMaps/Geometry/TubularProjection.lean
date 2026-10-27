module
public import HarmonicMaps.Geometry.TubularTube
@[expose] public section
namespace HarmonicMaps
noncomputable def tubularProjection (q : ℕ) (N : CompactSmoothEmbeddedTarget q) :
    tubularTube q N → N.Carrier :=
  Classical.choose ((Classical.choose_spec (tubularProjectionWellDefined q N)).2.2)
end HarmonicMaps
end
