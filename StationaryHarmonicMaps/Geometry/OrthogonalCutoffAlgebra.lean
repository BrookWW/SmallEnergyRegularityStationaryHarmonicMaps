module

public import StationaryHarmonicMaps.Geometry.OrthogonalFluxAlgebra

/-!
# Exact expanded cutoff error in an orthogonal frame

The pointwise identity retains the derivative of the inverse frame, the
coefficient two in the gradient-cutoff term, the Laplacian term and the
connection-cutoff term. No gauge existence or error estimate is assumed.
-/

public section

open HarmonicMaps

namespace StationaryHarmonicMaps

/-- The four expanded error terms give the actual transformed cutoff forcing. -/
theorem orthogonal_cutoff_forcing_identity {n q : ℕ}
    (P : Ambient q →L[ℝ] Ambient q)
    (D A : Fin n → Ambient q →L[ℝ] Ambient q)
    (v : Fin n → Ambient q) (a : Ambient q) (τ lapτ : ℝ) (dτ : Fin n → ℝ)
    (hP : P * star P = 1)
    (hD : ∀ i, star (D i) * P + star P * D i = 0) :
    let Dv (i : Fin n) := τ • v i + dτ i • a
    let Z (i : Fin n) := star P * D i + star P * A i * P
    let F := τ • (-(∑ i : Fin n, A i (v i))) +
      (2 : ℝ) • (∑ i : Fin n, dτ i • v i) + lapτ • a
    let e := (∑ i : Fin n, dτ i • star (D i) a) +
      (2 : ℝ) • (∑ i : Fin n, dτ i • star P (v i)) +
      lapτ • star P a + ∑ i : Fin n, dτ i • Z i (star P a)
    star P F + ∑ i : Fin n, star (D i) (Dv i) =
      e - ∑ i : Fin n, Z i (star P (Dv i)) := by
  let Z (i : Fin n) := star P * D i + star P * A i * P
  let J := star P (-(∑ i : Fin n, A i (v i))) + ∑ i : Fin n, star (D i) (v i)
  let W := ∑ i : Fin n, Z i (star P (v i))
  have hJ : J = -W := orthogonal_flux_forcing_identity P D A v hP hD
  have hJcut :
      star P (τ • (-(∑ i : Fin n, A i (v i))) +
        (2 : ℝ) • (∑ i : Fin n, dτ i • v i) + lapτ • a) +
        ∑ i : Fin n, star (D i) (τ • v i + dτ i • a) =
      τ • J + (2 : ℝ) • (∑ i : Fin n, dτ i • star P (v i)) +
        lapτ • star P a + ∑ i : Fin n, dτ i • star (D i) a := by
    dsimp only [J]
    simp only [map_add, map_smul, map_sum, Finset.sum_add_distrib, smul_add,
      ← Finset.smul_sum]
    abel
  have hWcut : (∑ i : Fin n, Z i (star P (τ • v i + dτ i • a))) =
      τ • W + ∑ i : Fin n, dτ i • Z i (star P a) := by
    simp only [map_add, map_smul, Finset.sum_add_distrib, ← Finset.smul_sum, W]
  change _ = ((∑ i : Fin n, dτ i • star (D i) a) +
    (2 : ℝ) • (∑ i : Fin n, dτ i • star P (v i)) + lapτ • star P a +
    ∑ i : Fin n, dτ i • Z i (star P a)) -
      ∑ i : Fin n, Z i (star P (τ • v i + dτ i • a))
  rw [hJcut, hWcut, hJ, smul_neg]
  abel

end StationaryHarmonicMaps

end
