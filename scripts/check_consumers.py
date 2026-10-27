#!/usr/bin/env python3
"""Consume all four complete public theorems through the advertised root import."""

import re
import sys
from verification_common import PROJECT, lean_output


CONSUMERS = r'''
module
public import StationaryHarmonicMaps

open HarmonicMaps MeasureTheory Set Metric
open StationaryHarmonicMaps
open scoped ContDiff

example {n q : ℕ} (hn : 2 ≤ n)
    (N : StationaryHarmonicMaps.CompactC2EmbeddedTarget q) :
    ∃ ε α C : ℝ, 0 < ε ∧ 0 < α ∧ α < 1 ∧ 0 ≤ C ∧
      ∀ (Ω : OpenDomain n) (u : Domain n → Ambient q)
        (Du : Domain n → Gradient n q),
        MemW12Loc Ω u Du →
        (∀ᵐ x ∂volume.restrict Ω.val, u x ∈ N.carrierSet) →
        StationaryHarmonicMaps.IsWeaklyHarmonicByTangentVariations N Ω u Du →
        StationaryHarmonicMaps.IsDomainStationary Ω Du →
        ∀ (a : Domain n) (R : PositiveRadius),
          closedBall a R.val ⊆ Ω.val →
          normalizedEnergy Du a R ≤ ENNReal.ofReal ε →
          ∃ w : ball a (R.val / 2) → Ambient q,
            IsContinuousRepresentative (ballDomain a (R.val / 2)) u w ∧
            (∀ x, w x ∈ N.carrierSet) ∧
            (∀ x y,
              ‖w x - w y‖ ≤ C * Real.rpow R.val (-α) *
                Real.sqrt (normalizedEnergy Du a R).toReal *
                Real.rpow (dist (x : Domain n) (y : Domain n)) α) ∧
            ∀ v : ball a (R.val / 2) → Ambient q,
              IsContinuousRepresentative (ballDomain a (R.val / 2)) u v → v = w := by
  exact StationaryHarmonicMaps.stationary_small_energy_regularity hn N

example {n q : ℕ} (hn : 2 ≤ n)
    (N : HarmonicMaps.CompactSmoothEmbeddedTarget q) :
    ∃ ε α C : ℝ, 0 < ε ∧ 0 < α ∧ α < 1 ∧ 0 ≤ C ∧
      ∀ (Ω : OpenDomain n) (u : Domain n → Ambient q)
        (Du : Domain n → Gradient n q),
        MemW12Loc Ω u Du →
        (∀ᵐ x ∂volume.restrict Ω.val, u x ∈ N.carrierSet) →
        StationaryHarmonicMaps.IsWeaklyHarmonicByTangentVariations
          (StationaryHarmonicMaps.SmoothTarget.toC2 N) Ω u Du →
        StationaryHarmonicMaps.IsDomainStationary Ω Du →
        ∀ (a : Domain n) (R : PositiveRadius),
          closedBall a R.val ⊆ Ω.val →
          normalizedEnergy Du a R ≤ ENNReal.ofReal ε →
          ∃ w : Domain n → Ambient q,
            ContDiffOn ℝ ∞ w (ball a (R.val / 2)) ∧
            IsContinuousRepresentative (ballDomain a (R.val / 2)) u (fun x => w x.val) ∧
            (∀ x ∈ ball a (R.val / 2), w x ∈ N.carrierSet) ∧
            (∀ x ∈ ball a (R.val / 2), ∀ y ∈ ball a (R.val / 2),
              ‖w x - w y‖ ≤ C * R.val ^ (-α) *
                Real.sqrt (normalizedEnergy Du a R).toReal * (dist x y) ^ α) ∧
            ∀ v : ball a (R.val / 2) → Ambient q,
              IsContinuousRepresentative (ballDomain a (R.val / 2)) u v →
              v = (fun x => w x.val) := by
  exact StationaryHarmonicMaps.stationary_small_energy_smooth_regularity hn N
example {n q : ℕ} (hn : 2 ≤ n)
    (N : CompactC2EmbeddedTarget q)
    (G : Ambient q → (Ambient q →L[ℝ] Ambient q)) (L : ℚ)
    (hG : ContDiff ℝ 1 G) (hcG : HasCompactSupport G)
    (hGN : ∀ p : N.Carrier,G p.val=N.normalProjection p)
    (hL : 0≤L) (hDG : ∀ y,‖fderiv ℝ G y‖≤(L:ℝ)) :
      ∀ (Ω : OpenDomain n) (u : Domain n → Ambient q)
        (Du : Domain n → Gradient n q),
        MemW12Loc Ω u Du →
        (∀ᵐ x ∂volume.restrict Ω.val, u x ∈ N.carrierSet) →
        IsWeaklyHarmonicByTangentVariations N Ω u Du →
        IsDomainStationary Ω Du →
        ∀ (a : Domain n) (R : PositiveRadius),
          Metric.closedBall a R.val ⊆ Ω.val →
          normalizedEnergy Du a R ≤ ENNReal.ofReal (Analysis.effectiveStationaryEnergyThreshold n q L:ℝ) →
          ∃ w : Metric.ball a (R.val / 2) → Ambient q,
            IsContinuousRepresentative (ballDomain a (R.val / 2)) u w ∧
            (∀ x, w x ∈ N.carrierSet) ∧
            (∀ x y,
              ‖w x - w y‖ ≤ (Analysis.effectiveStationaryHolderConstant n q L:ℝ) * Real.rpow R.val (-(1/2:ℝ)) *
                Real.sqrt (normalizedEnergy Du a R).toReal *
                Real.rpow (dist (x : Domain n) (y : Domain n)) (1/2:ℝ)) ∧
            ∀ v : Metric.ball a (R.val / 2) → Ambient q,
              IsContinuousRepresentative (ballDomain a (R.val / 2)) u v → v = w := by
  exact StationaryHarmonicMaps.stationary_small_energy_regularity_effective hn N G L hG hcG hGN hL hDG

example {n q : ℕ} (hn : 2≤n)
    (N : CompactSmoothEmbeddedTarget q)
    (G : Ambient q → (Ambient q →L[ℝ] Ambient q)) (L : ℚ)
    (hG : ContDiff ℝ 1 G) (hcG : HasCompactSupport G)
    (hGN : ∀ p : (SmoothTarget.toC2 N).Carrier,
      G p.val=(SmoothTarget.toC2 N).normalProjection p)
    (hL : 0≤L) (hDG : ∀ y,‖fderiv ℝ G y‖≤(L:ℝ)) :
      ∀(Ω : OpenDomain n) (u : Domain n→Ambient q) (Du : Domain n→Gradient n q),
        MemW12Loc Ω u Du →
        (∀ᵐx∂volume.restrict Ω.val,u x∈N.carrierSet) →
        IsWeaklyHarmonicByTangentVariations (SmoothTarget.toC2 N) Ω u Du →
        IsDomainStationary Ω Du →
        ∀(a : Domain n) (R : PositiveRadius),closedBall a R.val⊆Ω.val →
          normalizedEnergy Du a R≤ENNReal.ofReal (Analysis.effectiveStationaryEnergyThreshold n q L:ℝ) →
          ∃w : Domain n→Ambient q,
            ContDiffOn ℝ ∞ w (ball a (R.val/2)) ∧
            IsContinuousRepresentative (ballDomain a (R.val/2)) u (fun x=>w x.val) ∧
            (∀x∈ball a (R.val/2),w x∈N.carrierSet) ∧
            (∀x∈ball a (R.val/2),∀y∈ball a (R.val/2),
              ‖w x-w y‖≤(Analysis.effectiveStationaryHolderConstant n q L:ℝ)*R.val^(-(1/2:ℝ))*Real.sqrt (normalizedEnergy Du a R).toReal*(dist x y)^(1/2:ℝ)) ∧
            ∀v : ball a (R.val/2)→Ambient q,
              IsContinuousRepresentative (ballDomain a (R.val/2)) u v →
              v=(fun x=>w x.val) := by
  exact StationaryHarmonicMaps.stationary_small_energy_smooth_regularity_effective hn N G L hG hcG hGN hL hDG

'''


def main():
    output = lean_output(CONSUMERS)
    if output.strip():
        raise ValueError("Unexpected public-consumer output:\n" + output)
    blocks = re.findall(r"^```lean\s*\n(.*?)^```\s*$",
                        (PROJECT / "README.md").read_text(encoding="utf-8"), re.M | re.S)
    if not blocks:
        raise ValueError("README contains no Lean usage examples")
    for block in blocks:
        lean_output(block)
    print(f"PUBLIC CONSUMER CHECK PASS: complete existential and effective C² and smooth theorems; {len(blocks)} README examples")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, RuntimeError) as error:
        print(f"ERROR: {error}", file=sys.stderr)
        sys.exit(1)
