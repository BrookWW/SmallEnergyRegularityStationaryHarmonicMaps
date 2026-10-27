module
public import HarmonicMaps.Geometry.TubularBaseRadius
@[expose] public section
namespace HarmonicMaps
def tubularTube (q : ℕ) (N : CompactSmoothEmbeddedTarget q) : Set (Ambient q) :=
  {z | Metric.infDist z N.carrierSet < 2 * tubularBaseRadius q N}
end HarmonicMaps
end
