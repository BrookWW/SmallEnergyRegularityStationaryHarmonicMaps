module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Euclidean weak Sobolev interfaces

These are literal weak-derivative and graph-norm definitions for the
small-energy regularity argument. Maps and gradients are
ambient functions, but every analytic condition is restricted to the open
domain. No value outside that domain is prescribed or used.

The explicit-gradient design also occurs in BrookWW/LeanStationaryHarmonicMaps,
commit bde641f98085e5a0443c10779a6fe519190b6adc. This module uses smooth scalar
tests and coordinatewise L2 data rather than importing its C1 witness bundle.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff

namespace HarmonicMaps

abbrev Domain (n : ℕ) := EuclideanSpace ℝ (Fin n)

abbrev Ambient (q : ℕ) := EuclideanSpace ℝ (Fin q)

/-- Coordinate columns of a gradient. The Pi norm is not the HS norm. -/
abbrev Gradient (n q : ℕ) := Fin n → Ambient q

/-- An open Euclidean domain, with no connectedness or boundedness requirement. -/
abbrev OpenDomain (n : ℕ) := {Ω : Set (Domain n) // IsOpen Ω}

/-- The open ball, used as an open domain. -/
def ballDomain {n : ℕ} (a : Domain n) (r : ℝ) : OpenDomain n :=
  ⟨Metric.ball a r, Metric.isOpen_ball⟩

noncomputable section

/-- The ordinary coordinate derivative of a smooth map. Its public carrier
includes smoothness, so `fderiv` is never used on a nondifferentiable input. -/
def coordinateDerivative {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : Domain n → E) (_hf : ContDiff ℝ ∞ f)
    (i : Fin n) (x : Domain n) : E :=
  fderiv ℝ f x (EuclideanSpace.single i 1)

/-- Local L2 membership on all compact subsets of the domain. -/
def LocallyMemL2 {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    (Ω : OpenDomain n) (f : Domain n → E) : Prop :=
  ∀ K : Set (Domain n), IsCompact K → K ⊆ Ω.val →
    MemLp f 2 (volume.restrict K)

/-- A distributional weak gradient, including the local integrability required
to define the distributional pairings. -/
def HasWeakGradient {n q : ℕ} (Ω : OpenDomain n)
    (u : Domain n → Ambient q) (Du : Domain n → Gradient n q) : Prop :=
  LocallyIntegrableOn u Ω.val volume ∧
    (∀ i : Fin n, LocallyIntegrableOn (fun x => Du x i) Ω.val volume) ∧
    ∀ (i : Fin n) (φ : Domain n → ℝ) (hφ : ContDiff ℝ ∞ φ),
      HasCompactSupport φ → tsupport φ ⊆ Ω.val →
      (∫ x in Ω.val, coordinateDerivative φ hφ i x • u x) =
        -(∫ x in Ω.val, φ x • Du x i)

/-- Real, Euclidean-valued W1,2_loc membership with the displayed weak gradient. -/
def MemW12Loc {n q : ℕ} (Ω : OpenDomain n)
    (u : Domain n → Ambient q) (Du : Domain n → Gradient n q) : Prop :=
  HasWeakGradient Ω u Du ∧ LocallyMemL2 Ω u ∧
    ∀ i : Fin n, LocallyMemL2 Ω (fun x => Du x i)

/-- Finite W1,2 membership on the entire domain, not merely local membership. -/
def MemW12 {n q : ℕ} (Ω : OpenDomain n)
    (u : Domain n → Ambient q) (Du : Domain n → Gradient n q) : Prop :=
  HasWeakGradient Ω u Du ∧ MemLp u 2 (volume.restrict Ω.val) ∧
    ∀ i : Fin n, MemLp (fun x => Du x i) 2 (volume.restrict Ω.val)

/-- W1,2_0 is the closure of C-infinity compactly supported maps in the
W1,2 graph norm. Coordinatewise derivative convergence is equivalent to
HS-gradient convergence because there are finitely many coordinates. -/
def HasZeroBoundaryValues {n q : ℕ} (Ω : OpenDomain n)
    (f : Domain n → Ambient q) (Df : Domain n → Gradient n q) : Prop :=
  MemW12 Ω f Df ∧
    ∃ approximation : ℕ → Domain n → Ambient q,
      ∃ hSmooth : ∀ k, ContDiff ℝ ∞ (approximation k),
      (∀ k, HasCompactSupport (approximation k) ∧
        tsupport (approximation k) ⊆ Ω.val) ∧
      Tendsto (fun k => eLpNorm (approximation k - f) 2 (volume.restrict Ω.val))
        atTop (𝓝 0) ∧
      ∀ i : Fin n,
        Tendsto (fun k => eLpNorm
          (fun x => coordinateDerivative (approximation k) (hSmooth k) i x - Df x i)
          2 (volume.restrict Ω.val)) atTop (𝓝 0)

/-- The competitor and original map have a difference in W1,2_0. -/
def HasZeroBoundaryDifference {n q : ℕ} (Ω : OpenDomain n)
    (u : Domain n → Ambient q) (Du : Domain n → Gradient n q)
    (v : Domain n → Ambient q) (Dv : Domain n → Gradient n q) : Prop :=
  HasZeroBoundaryValues Ω (v - u) (fun x i => Dv x i - Du x i)

end
end HarmonicMaps

end
