module

public import HolderToCK.Analysis.Bootstrap.QualitativeLocalData
public import HolderToCK.Analysis.Bootstrap.UniformThreshold

/-! # Local smoothness of Holder weak quadratic Poisson solutions

Finite local data for a positive affine dilation feed the same-map nested-ball
bootstrap with parameter one. Inverse affine transport then gives smoothness
of the original map at every point of its open domain.
-/

public section

open HarmonicMaps MeasureTheory Set
open scoped ContDiff

namespace HolderToCK.Providers.HolderQuadraticPoissonSmooth

theorem result
    (n q : ℕ) (hn : 2 ≤ n) (Ω : OpenDomain n)
    (u : Domain n → Ambient q) (Du : Domain n → Gradient n q)
    (A : Ambient q → Ambient q →L[ℝ] Ambient q →L[ℝ] Ambient q)
    (hA : ContDiff ℝ ∞ A) (hu : MemW12Loc Ω u Du)
    (hHolder : LocallyHolderOn Ω u)
    (hEquation : WeakPoissonOn Ω Du
      (fun x => ∑ i : Fin n, A (u x) (Du x i) (Du x i))) :
    ContDiffOn ℝ ∞ u Ω.val := by
  apply Ω.property.contDiffOn_iff.mpr
  intro a ha
  obtain ⟨r, γ, M, S, _, hγ, hγOne, hM, hvC1, hImage, hCentered, _,
    hNative, _, hNativeHolder, _, _, hvEquation⟩ :=
    holder_quadratic_poisson_affine_initial_data hn Ω u Du A hA hu hHolder hEquation a ha
  obtain ⟨_, _, _, hUpgrade⟩ :=
    quadratic_poisson_smooth_halfBall n q hn γ hγ hγOne A hA (u a) S.val M hM.le
  have hvSmooth : ContDiffOn ℝ ∞ (fun z => u (a + r.val • z))
      (Metric.ball (0 : Domain n) (1 / 2)) := by
    refine (hUpgrade (fun z => u (a + r.val • z)) 1 zero_le_one le_rfl
      hvC1 hImage ?_ ?_ ?_ ?_).1
    · exact hvEquation
    · simpa only [mul_one] using hCentered
    · simpa only [mul_one] using hNative
    · simpa only [mul_one] using hNativeHolder
  have huSmooth : ContDiffOn ℝ ∞ u (Metric.ball a (r.val * (1 / 2))) :=
    contDiffOn_of_affine_pullback a r hvSmooth
  exact huSmooth.contDiffAt
    (Metric.ball_mem_nhds a (mul_pos r.property (by norm_num)))

end HolderToCK.Providers.HolderQuadraticPoissonSmooth
end
