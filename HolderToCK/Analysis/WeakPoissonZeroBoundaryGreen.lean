module

public import HolderToCK.Foundation.WeakPoisson
public import HolderToCK.Analysis.L2PairingContinuity
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-! # Native zero-boundary tests for L2 Poisson data

Compact smooth test identities pass to the actual Sobolev graph limit. The
forcing is explicitly in L2 for this extension; no bounded W0 test extension
for a merely L1 forcing term is assumed.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped ContDiff Topology

namespace HolderToCK

theorem WeakPoissonOn.zeroBoundary_green {n q : ℕ} {Ω : OpenDomain n}
    {Du : Domain n → Gradient n q} {F v : Domain n → Ambient q}
    {Dv : Domain n → Gradient n q} (hEq : WeakPoissonOn Ω Du F)
    (hDu : ∀ i : Fin n, MemLp (fun x => Du x i) 2 (volume.restrict Ω.val))
    (hF : MemLp F 2 (volume.restrict Ω.val)) (hv : HasZeroBoundaryValues Ω v Dv) :
    IntegrableOn (fun x => ∑ i : Fin n, inner ℝ (Du x i) (Dv x i)) Ω.val ∧
    IntegrableOn (fun x => inner ℝ (F x) (v x)) Ω.val ∧
    (∫ x in Ω.val, ∑ i : Fin n, inner ℝ (Du x i) (Dv x i)) =
      -(∫ x in Ω.val, inner ℝ (F x) (v x)) := by
  obtain ⟨a, ha, hc, hconv, hDconv⟩ := hv.2
  have haL (k : ℕ) : MemLp (a k) 2 (volume.restrict Ω.val) :=
    (ha k).continuous.memLp_of_hasCompactSupport (hc k).1
  have haD (k : ℕ) (i : Fin n) : MemLp (coordinateDerivative (a k) (ha k) i) 2
      (volume.restrict Ω.val) := by
    have hcont : Continuous (coordinateDerivative (a k) (ha k) i) :=
      ((ha k).continuous_fderiv (by simp)).clm_apply continuous_const
    exact hcont.memLp_of_hasCompactSupport ((hc k).1.fderiv_apply ℝ (EuclideanSpace.single i 1))
  have hleft (i : Fin n) : IntegrableOn (fun x => inner ℝ (Du x i) (Dv x i)) Ω.val :=
    integrable_inner_of_memLp_two (hDu i) (hv.1.2.2 i)
  have hleftLim : Tendsto (fun k => ∑ i : Fin n,
      ∫ x in Ω.val, inner ℝ (Du x i) (coordinateDerivative (a k) (ha k) i x)) atTop
      (𝓝 (∑ i : Fin n, ∫ x in Ω.val, inner ℝ (Du x i) (Dv x i))) :=
    tendsto_finsetSum Finset.univ (fun i _ =>
      tendsto_integral_inner_of_L2 (fun k => haD k i) (hv.1.2.2 i) (hDu i) (hDconv i))
  have hrightLim := tendsto_integral_inner_of_L2 haL hv.1.2.1 hF hconv
  have hseq (k : ℕ) :
      (∑ i : Fin n, ∫ x in Ω.val, inner ℝ (Du x i) (coordinateDerivative (a k) (ha k) i x)) =
      -(∫ x in Ω.val, inner ℝ (F x) (a k x)) := by
    rw [← integral_finsetSum _ (fun i _ => integrable_inner_of_memLp_two (hDu i) (haD k i))]
    exact (hEq.2 (a k) (ha k) (hc k).1 (hc k).2).2.2
  refine ⟨integrable_finsetSum Finset.univ (fun i _ => hleft i),
    integrable_inner_of_memLp_two hF hv.1.2.1, ?_⟩
  rw [integral_finsetSum _ (fun i _ => hleft i)]
  exact tendsto_nhds_unique hleftLim
    (hrightLim.neg.congr' (Eventually.of_forall fun k => (hseq k).symm))

end HolderToCK
end
