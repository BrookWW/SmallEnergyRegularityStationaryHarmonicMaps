module

public import StationaryHarmonicMaps.Analysis.SkewMorreySmoothing
public import StationaryHarmonicMaps.Analysis.SmoothStrongerMorrey

/-!
# Genuine stronger-class skew approximants of critical ball data

The same actual smooth skew sequence has uniform critical control and
strong L2 convergence. Each term also has finite Morrey growth with
exponent n-1 on the original ball; these stronger constants may depend
on the sequence index.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped ContDiff Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- The original critical skew field produces one actual sequence with uniform critical bounds and genuine termwise stronger Morrey membership. -/
theorem exists_stronger_class_skew_critical_approximation_unitBall {n q : ℕ}
    (hn : 2 ≤ n)
    (E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient (q*q))
    (R : Ambient (q*q) →L[ℝ] (Ambient q →L[ℝ] Ambient q))
    (hRE : ∀ T, R (E T)=T) (hER : ∀ z, E (R z)=z)
    (A : Domain n → Fin n → (Ambient q →L[ℝ] Ambient q))
    (hA : ∀ i, MemLp (fun x => A x i) 2
      (volume.restrict (Metric.ball (0 : Domain n) 1)))
    (hSkew : ∀ i, ∀ᵐ x ∂volume.restrict (Metric.ball (0 : Domain n) 1),
      star (A x i) = -A x i)
    (K : ℝ) (hK : 0 ≤ K)
    (hCritical : criticalGradientMorreySquare (fun x i => E (A x i))
      (Metric.ball (0 : Domain n) 1) ≤ ENNReal.ofReal K) :
    ∃ Aseq : ℕ → Domain n → Fin n → (Ambient q →L[ℝ] Ambient q),
      (∀ j i, ContDiff ℝ ∞ (fun x => Aseq j x i) ∧
        MemLp (fun x => Aseq j x i) 2 volume) ∧
      (∀ j x i, star (Aseq j x i) = -Aseq j x i) ∧
      (∀ j, criticalGradientMorreySquare (fun x i => E (Aseq j x i)) univ ≤
        ENNReal.ofReal ((2 : ℝ)^(n-2)*K)) ∧
      (∀ j, ∃ C : ℝ, 0 < C ∧ ∀ (a : Domain n) (r : ℝ), 0 < r →
        (∫ x in Metric.ball a r ∩ Metric.ball (0 : Domain n) 1,
          hsNormSq (fun i => E (Aseq j x i))) ≤ C*r^((n : ℝ)-1)) ∧
      ∀ i, Tendsto (fun j => eLpNorm (fun x => E (Aseq j x i)-E (A x i)) 2
        (volume.restrict (Metric.ball (0 : Domain n) 1))) atTop (𝓝 0) := by
  obtain ⟨Aseq,hSmooth,hPointwise,hUniform,hStrong⟩ :=
    exists_smooth_skew_critical_approximation_unitBall hn E R hRE hER A hA hSkew K hK hCritical
  refine ⟨Aseq,hSmooth,hPointwise,hUniform,?_,hStrong⟩
  intro j
  exact exists_strongerMorrey_growth_of_continuous (by omega)
    (fun x i => E (Aseq j x i))
    (fun i => E.continuous.comp (hSmooth j i).1.continuous)

end StationaryHarmonicMaps.Analysis

end
