module

public import StationaryHarmonicMaps.Frozen.SmallEnergyRegularity
public import StationaryHarmonicMaps.Analysis.SmoothHolderRepresentative

/-!
# The smooth-target small-energy corollary

The original uniform Hölder constants produce one continuous representative.
Its original weak gradient and smooth-target equation give smoothness on
the same half ball, with the original quantitative estimate and uniqueness.
-/

public section
open HarmonicMaps MeasureTheory Filter Set Metric
open scoped ContDiff Topology ENNReal
noncomputable section
namespace StationaryHarmonicMaps.Providers

theorem smallEnergySmoothRegularity {n q : ℕ} (hn : 2≤n)
    (N : CompactSmoothEmbeddedTarget q) :
    ∃ε α C : ℝ,0<ε ∧ 0<α ∧ α<1 ∧ 0≤C ∧
      ∀(Ω : OpenDomain n) (u : Domain n→Ambient q) (Du : Domain n→Gradient n q),
        MemW12Loc Ω u Du →
        (∀ᵐx∂volume.restrict Ω.val,u x∈N.carrierSet) →
        IsWeaklyHarmonicByTangentVariations (SmoothTarget.toC2 N) Ω u Du →
        IsDomainStationary Ω Du →
        ∀(a : Domain n) (R : PositiveRadius),closedBall a R.val⊆Ω.val →
          normalizedEnergy Du a R≤ENNReal.ofReal ε →
          ∃w : Domain n→Ambient q,
            ContDiffOn ℝ ∞ w (ball a (R.val/2)) ∧
            IsContinuousRepresentative (ballDomain a (R.val/2)) u (fun x=>w x.val) ∧
            (∀x∈ball a (R.val/2),w x∈N.carrierSet) ∧
            (∀x∈ball a (R.val/2),∀y∈ball a (R.val/2),
              ‖w x-w y‖≤C*R.val^(-α)*Real.sqrt (normalizedEnergy Du a R).toReal*(dist x y)^α) ∧
            ∀v : ball a (R.val/2)→Ambient q,
              IsContinuousRepresentative (ballDomain a (R.val/2)) u v →
              v=(fun x=>w x.val) := by
  classical
  obtain ⟨ε,α,C,hε,hα,hαOne,hC,H⟩ := stationary_small_energy_regularity hn (SmoothTarget.toC2 N)
  refine ⟨ε,α,C,hε,hα,hαOne,hC,?_⟩
  intro Ω u Du hu hN hweak hStationary a R hBall hSmall
  have hNC2 : ∀ᵐx∂volume.restrict Ω.val,u x∈(SmoothTarget.toC2 N).carrierSet := by
    simpa only [SmoothTarget.toC2_carrierSet] using hN
  obtain ⟨v,hRep,hVN,hBound,hUnique⟩ := H Ω u Du hu hNC2 hweak hStationary a R hBall hSmall
  let w : Domain n→Ambient q := fun x=>if hx : x∈ball a (R.val/2) then v ⟨x,hx⟩ else u x
  have hValue (x : Domain n) (hx : x∈ball a (R.val/2)) : w x=v ⟨x,hx⟩ := dif_pos hx
  have hSame : (fun x : ball a (R.val/2)=>w x.val)=v :=
    funext fun x=>hValue x.val x.property
  have hRepW : IsContinuousRepresentative (ballDomain a (R.val/2)) u (fun x=>w x.val) := by
    exact hSame.symm ▸ hRep
  have hAE : w=ᵐ[volume.restrict (ball a (R.val/2))]u := by
    filter_upwards [hRep.2,ae_restrict_mem measurableSet_ball] with x hx hxb
    exact (hValue x hxb).trans (hx hxb)
  let B : OpenDomain n := ballDomain a (R.val/2)
  have hSub : B.val⊆Ω.val := ball_subset_closedBall.trans
    ((closedBall_subset_closedBall (by linarith only [R.property] : R.val/2≤R.val)).trans hBall)
  have hBoundW : HolderToCK.HolderBoundOn B.val w α
      (C*R.val^(-α)*Real.sqrt (normalizedEnergy Du a R).toReal) := by
    intro x hx y hy
    rw [hValue x hx,hValue y hy]
    exact hBound ⟨x,hx⟩ ⟨y,hy⟩
  have hLocal : HolderToCK.LocallyHolderOn B w := by
    intro x hx
    obtain ⟨r,hr,hbr⟩ := Metric.isOpen_iff.mp isOpen_ball x hx
    have hClosed : closedBall x (r/2)⊆B.val :=
      (closedBall_subset_ball (by linarith only [hr] : r/2<r)).trans hbr
    refine ⟨⟨r/2,half_pos hr⟩,hClosed,α,
      C*R.val^(-α)*Real.sqrt (normalizedEnergy Du a R).toReal,hα,hαOne,?_,?_⟩
    · exact mul_nonneg (mul_nonneg hC (Real.rpow_nonneg R.property.le _)) (Real.sqrt_nonneg _)
    · exact hBoundW.mono (ball_subset_closedBall.trans hClosed)
  have hSmooth := Analysis.smooth_locallyHolder_representative_smooth_target hn N Ω B hSub
    u w Du hu hN hweak hAE hLocal
  refine ⟨w,hSmooth,hRepW,?_,hBoundW,?_⟩
  · intro x hx
    rw [hValue x hx]
    exact hVN ⟨x,hx⟩
  · intro z hz
    exact (hUnique z hz).trans hSame.symm

end StationaryHarmonicMaps.Providers
end
