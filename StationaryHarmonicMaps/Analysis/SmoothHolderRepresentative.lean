module

public import StationaryHarmonicMaps.Analysis.SmoothTargetBootstrap
import HarmonicMaps.Analysis.SobolevAECongruence
import HarmonicMaps.SobolevRestriction

/-!
# Smoothness of the same locally Hölder representative

Almost-everywhere replacement preserves the original weak gradient.
The smooth target coefficient is evaluated on the same representative
in the genuine weak Poisson equation on the specified open subdomain.
-/

public section
open HarmonicMaps MeasureTheory Filter
open scoped ContDiff
noncomputable section
namespace StationaryHarmonicMaps.Analysis

theorem smooth_locallyHolder_representative_smooth_target {n q : ℕ} (hn : 2≤n)
    (N : CompactSmoothEmbeddedTarget q) (Ω V : OpenDomain n) (hSub : V.val⊆Ω.val)
    (u w : Domain n→Ambient q) (Du : Domain n→Gradient n q)
    (hu : MemW12Loc Ω u Du)
    (hN : ∀ᵐx∂volume.restrict Ω.val,u x∈N.carrierSet)
    (hweak : IsWeaklyHarmonicByTangentVariations (SmoothTarget.toC2 N) Ω u Du)
    (hAE : w=ᵐ[volume.restrict V.val]u)
    (hHolder : HolderToCK.LocallyHolderOn V w) : ContDiffOn ℝ ∞ w V.val := by
  obtain ⟨G,L,hG,hcG,hGN,_hL,hDG⟩ := SmoothTarget.exists_smooth_normal_projection_extension N
  have hNC2 : ∀ᵐx∂volume.restrict Ω.val,u x∈(SmoothTarget.toC2 N).carrierSet := by
    simpa only [SmoothTarget.toC2_carrierSet] using hN
  have hOriginal := (variational_weakPoissonOn (SmoothTarget.toC2 N) hu hNC2 hweak
    G (hG.of_le (by simp)) hcG hGN hDG).mono hSub
  let A : Ambient q→Ambient q→L[ℝ]Ambient q→L[ℝ]Ambient q := fun y=> -(fderiv ℝ G y)
  have hA : ContDiff ℝ ∞ A := (hG.fderiv_right (m:=∞) (by simp)).neg
  have hForcing : (fun x=> -(∑i : Fin n,fderiv ℝ G (u x) (Du x i) (Du x i)))=ᵐ[
      volume.restrict V.val](fun x=>∑i : Fin n,A (w x) (Du x i) (Du x i)) := by
    filter_upwards [hAE] with x hx
    rw [hx]
    simp only [A,neg_apply,Finset.sum_neg_distrib]
  have hw : MemW12Loc V w Du :=
    (hu.mono hSub).congr_ae hAE.symm (EventuallyEq.refl _ _)
  exact HolderToCK.holderQuadraticPoisson_smooth n q hn V w Du A hA hw hHolder
    (hOriginal.congr (EventuallyEq.refl _ _) hForcing)

end StationaryHarmonicMaps.Analysis
end
