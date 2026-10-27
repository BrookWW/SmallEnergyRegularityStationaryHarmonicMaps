#!/usr/bin/env python3
"""Consume both complete public theorems through the advertised root import."""

import re
import sys
from verification_common import PROJECT, lean_output


CONSUMERS = r'''
module
public import StationaryHarmonicMaps

open HarmonicMaps MeasureTheory Set Metric
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
    print(f"PUBLIC CONSUMER CHECK PASS: complete C² and smooth theorems; {len(blocks)} README examples")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, RuntimeError) as error:
        print(f"ERROR: {error}", file=sys.stderr)
        sys.exit(1)
