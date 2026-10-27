module

public import HarmonicMaps.SobolevLemmas
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Differences of maps with displayed weak gradients

The weak test identities are linear. Subtracting two genuine Sobolev maps
therefore gives their literal difference and the difference of their columns.
-/

public section

open MeasureTheory Set

namespace HarmonicMaps

/-- Distributional weak gradients subtract with the maps. -/
theorem HasWeakGradient.sub {n q : ℕ} {Ω : OpenDomain n}
    {u v : Domain n → Ambient q} {Du Dv : Domain n → Gradient n q}
    (hu : HasWeakGradient Ω u Du) (hv : HasWeakGradient Ω v Dv) :
    HasWeakGradient Ω (u - v) (fun x i => Du x i - Dv x i) := by
  refine ⟨hu.1.sub hv.1, fun i => (hu.2.1 i).sub (hv.2.1 i), ?_⟩
  intro i φ hφ hc hs
  simp only [Pi.sub_apply, smul_sub]
  rw [integral_sub (hu.integrable_test_derivative i hφ hc hs)
    (hv.integrable_test_derivative i hφ hc hs),
    integral_sub (hu.integrable_test_gradient i hφ hc hs)
      (hv.integrable_test_gradient i hφ hc hs),
    hu.2.2 i φ hφ hc hs, hv.2.2 i φ hφ hc hs]
  abel

/-- Finite Sobolev membership is stable under subtraction with the same
explicit weak-gradient witnesses. -/
theorem MemW12.sub {n q : ℕ} {Ω : OpenDomain n}
    {u v : Domain n → Ambient q} {Du Dv : Domain n → Gradient n q}
    (hu : MemW12 Ω u Du) (hv : MemW12 Ω v Dv) :
    MemW12 Ω (u - v) (fun x i => Du x i - Dv x i) :=
  ⟨hu.1.sub hv.1, hu.2.1.sub hv.2.1, fun i => (hu.2.2 i).sub (hv.2.2 i)⟩

end HarmonicMaps
