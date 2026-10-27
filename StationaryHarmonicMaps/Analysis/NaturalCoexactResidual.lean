module

public import StationaryHarmonicMaps.Analysis.ClosedNormalTensorProjection
public import StationaryHarmonicMaps.Analysis.ClosedNormalHarmonicRemainder
public import StationaryHarmonicMaps.Analysis.HodgeEnergyIdentity

/-!
# The relative Hodge residual of a natural solenoidal one-form

A raw L2 field annihilating every native gradient has an actual closed normal
coexact response. The same residual is naturally solenoidal, coefficient
harmonic and orthogonal to every smooth closed normal tensor divergence.
The response and residual split the original full Hilbert--Schmidt energy.
These conclusions retain the residual; its vanishing is a separate relative
Hodge exactness statement.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped ContDiff Topology

namespace StationaryHarmonicMaps.Analysis

/-- Original natural L2 data produce their native closed normal response and the same natural coefficient-harmonic residual with exact orthogonal energy. -/
theorem exists_natural_closed_normal_harmonic_residual_unitBall {n q : ℕ}
    (F : Domain n → Gradient n q)
    (hF : ∀ j, MemLp (fun x => F x j) 2 (volume.restrict (ball (0 : Domain n) 1)))
    (hNatural : ∀ (ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q),
      MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ →
      (∫ x in ball (0 : Domain n) 1, ∑ j : Fin n, inner ℝ (F x j) (Dψ x j)) = 0) :
    ∃ (b : Fin n → Fin n → Domain n → Ambient q)
      (Db : Fin n → Fin n → Domain n → Gradient n q) (P h : Domain n → Gradient n q),
      (∀ i j, MemW12 (ballDomain (0 : Domain n) 1) (b i j) (Db i j)) ∧
      (∀ j, MemLp (fun x => P x j) 2 (volume.restrict (ball (0 : Domain n) 1))) ∧
      (∀ᵐ x ∂volume.restrict (ball (0 : Domain n) 1), ∀ i j, b i j x = -b j i x) ∧
      (∀ᵐ x ∂volume.restrict (ball (0 : Domain n) 1), ∀ i j k,
        Db i j x k + Db j k x i + Db k i x j = 0) ∧
      (∀ᵐ x ∂volume.restrict (ball (0 : Domain n) 1), ∀ j, (∑ i : Fin n, Db i j x i) = P x j) ∧
      (∀ (j : Fin n) (ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q),
        MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ →
        IntegrableOn (fun x => ∑ i : Fin n, inner ℝ (b i j x) (Dψ x i)) (ball (0 : Domain n) 1) volume ∧
        IntegrableOn (fun x => inner ℝ (P x j) (ψ x)) (ball (0 : Domain n) 1) volume ∧
        (∫ x in ball (0 : Domain n) 1, ∑ i : Fin n, inner ℝ (b i j x) (Dψ x i)) =
          -(∫ x in ball (0 : Domain n) 1, inner ℝ (P x j) (ψ x))) ∧
      (∀ (ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q),
        MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ →
        IntegrableOn (fun x => ∑ j : Fin n, inner ℝ (P x j) (Dψ x j)) (ball (0 : Domain n) 1) volume ∧
        (∫ x in ball (0 : Domain n) 1, ∑ j : Fin n, inner ℝ (P x j) (Dψ x j)) = 0) ∧
      (∀ x j, F x j = P x j + h x j) ∧
      (∀ j, MemLp (fun x => h x j) 2 (volume.restrict (ball (0 : Domain n) 1))) ∧
      (∀ (ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q),
        MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ →
        IntegrableOn (fun x => ∑ j : Fin n, inner ℝ (h x j) (Dψ x j)) (ball (0 : Domain n) 1) volume ∧
        (∫ x in ball (0 : Domain n) 1, ∑ j : Fin n, inner ℝ (h x j) (Dψ x j)) = 0) ∧
      HolderToCK.WeakPoissonOn (ballDomain (0 : Domain n) 1) h (fun _ => 0) ∧
      (∀ (j : Fin n) (ψ : Domain n → Ambient q), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ ball (0 : Domain n) 1 →
        IntegrableOn (fun x => inner ℝ (h x j) (Laplacian.laplacian ψ x)) (ball (0 : Domain n) 1) volume ∧
        (∫ x in ball (0 : Domain n) 1, inner ℝ (h x j) (Laplacian.laplacian ψ x)) = 0) ∧
      ((∫ x in ball (0 : Domain n) 1, hsNormSq (P x)) +
        (∫ x in ball (0 : Domain n) 1, hsNormSq (h x)) =
          ∫ x in ball (0 : Domain n) 1, hsNormSq (F x)) ∧
      ((∫ x in ball (0 : Domain n) 1, ∑ j : Fin n, ∑ i : Fin n, ‖b i j x‖ ^ 2) +
        (∫ x in ball (0 : Domain n) 1, ∑ j : Fin n, ∑ k : Fin n, ∑ i : Fin n, ‖Db i j x k‖ ^ 2) ≤
        (4 * (2 : ℝ) ^ (n + 1) + 2 * (n : ℝ) + 2) *
          (∫ x in ball (0 : Domain n) 1, hsNormSq (F x))) ∧
      ∀ C : Fin n → Fin n → Domain n → Ambient q,
        (∀ i j, ContDiff ℝ ∞ (C i j)) → (∀ i j x, C i j x = -C j i x) →
        (∀ i j k x, fderiv ℝ (C i j) x (EuclideanSpace.single k 1) +
          fderiv ℝ (C j k) x (EuclideanSpace.single i 1) +
          fderiv ℝ (C k i) x (EuclideanSpace.single j 1) = 0) →
        (∀ j (x : Domain n), ‖x‖ = 1 → (∑ i : Fin n, x i • C i j x) = 0) →
        IntegrableOn (fun x => ∑ j : Fin n, inner ℝ (h x j)
          (∑ i : Fin n, fderiv ℝ (C i j) x (EuclideanSpace.single i 1))) (ball (0 : Domain n) 1) volume ∧
        (∫ x in ball (0 : Domain n) 1, ∑ j : Fin n, inner ℝ (h x j)
          (∑ i : Fin n, fderiv ℝ (C i j) x (EuclideanSpace.single i 1))) = 0 := by
  let μ := volume.restrict (ball (0 : Domain n) 1)
  obtain ⟨b, Db, P, hb, hP, hSkew, hClosed, hDivB, hNormal, hPNatural,
    hSelf, _hPEnergy, hBEnergy, hPTests⟩ := exists_closed_normal_tensor_projection_unitBall F hF
  let h := fun (x : Domain n) (j : Fin n) => F x j - P x j
  have hHLp (j : Fin n) : MemLp (fun x => h x j) 2 μ := (hF j).sub (hP j)
  have hHNatural (ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q)
      (hψ : MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ) :
      Integrable (fun x => ∑ j : Fin n, inner ℝ (h x j) (Dψ x j)) μ ∧
      (∫ x, ∑ j : Fin n, inner ℝ (h x j) (Dψ x j) ∂μ) = 0 := by
    have hFI := integrable_finsetSum Finset.univ (fun j _ =>
      HolderToCK.integrable_inner_of_memLp_two (hF j) (hψ.2.2 j))
    obtain ⟨hPI, hPZero⟩ := hPNatural ψ Dψ hψ
    have hPoint (x : Domain n) : (∑ j : Fin n, inner ℝ (h x j) (Dψ x j)) =
        (∑ j : Fin n, inner ℝ (F x j) (Dψ x j)) -
          ∑ j : Fin n, inner ℝ (P x j) (Dψ x j) := by
      simp only [h, inner_sub_left, Finset.sum_sub_distrib]
    refine ⟨(hFI.sub hPI).congr (Eventually.of_forall fun x => (hPoint x).symm), ?_⟩
    rw [integral_congr_ae (Eventually.of_forall hPoint), integral_sub hFI hPI,
      hNatural ψ Dψ hψ, hPZero, sub_self]
  have hHDiv : HolderToCK.WeakPoissonOn (ballDomain (0 : Domain n) 1) h (fun _ => 0) := by
    refine ⟨locallyIntegrableOn_zero, ?_⟩
    intro ψ hψ _hc _hs
    have hW := memW12_ball_of_ambient_c1 (0 : Domain n) 1 ψ (hψ.of_le (by simp))
    obtain ⟨hI, hEq⟩ := hHNatural ψ _ hW
    refine ⟨hI, ?_, ?_⟩
    · simp only [inner_zero_left]
      exact integrable_zero _ _ _
    · simpa only [ballDomain, inner_zero_left, integral_zero, neg_zero] using hEq
  have hHTests (C : Fin n → Fin n → Domain n → Ambient q)
      (hC : ∀ i j, ContDiff ℝ ∞ (C i j)) (hCS : ∀ i j x, C i j x = -C j i x)
      (hCD : ∀ i j k x, fderiv ℝ (C i j) x (EuclideanSpace.single k 1) +
        fderiv ℝ (C j k) x (EuclideanSpace.single i 1) +
        fderiv ℝ (C k i) x (EuclideanSpace.single j 1) = 0)
      (hCN : ∀ j (x : Domain n), ‖x‖ = 1 → (∑ i : Fin n, x i • C i j x) = 0) :
      Integrable (fun x => ∑ j : Fin n, inner ℝ (h x j)
        (∑ i : Fin n, fderiv ℝ (C i j) x (EuclideanSpace.single i 1))) μ ∧
      (∫ x, ∑ j : Fin n, inner ℝ (h x j)
        (∑ i : Fin n, fderiv ℝ (C i j) x (EuclideanSpace.single i 1)) ∂μ) = 0 := by
    obtain ⟨hPI, hFI, hEq⟩ := hPTests C hC hCS hCD hCN
    have hPoint (x : Domain n) : (∑ j : Fin n, inner ℝ (h x j)
        (∑ i : Fin n, fderiv ℝ (C i j) x (EuclideanSpace.single i 1))) =
      (∑ j : Fin n, inner ℝ (F x j) (∑ i : Fin n, fderiv ℝ (C i j) x (EuclideanSpace.single i 1))) -
        ∑ j : Fin n, inner ℝ (P x j) (∑ i : Fin n, fderiv ℝ (C i j) x (EuclideanSpace.single i 1)) := by
      simp only [h, inner_sub_left, Finset.sum_sub_distrib]
    refine ⟨(hFI.sub hPI).congr (Eventually.of_forall fun x => (hPoint x).symm), ?_⟩
    rw [integral_congr_ae (Eventually.of_forall hPoint), integral_sub hFI hPI, ← hEq, sub_self]
  have hHarmonic := coefficient_laplacian_pairing_zero_of_closed_normal_tests h hHLp hHDiv
    (fun C hC hCS hCD hCN => (hHTests C hC hCS hCD hCN).2)
  have hDecomp (x : Domain n) (j : Fin n) : F x j = P x j + h x j := by
    dsimp only [h]
    abel
  have hZero : ∀ j : Fin n, MemLp (fun _ : Domain n => (0 : Ambient q)) 2 μ := fun _ => MemLp.zero'
  have hEq : ∀ᵐ x ∂μ, ∀ j, F x j = (0 : Ambient q) + P x j + h x j :=
    Eventually.of_forall fun x j => by simpa only [zero_add] using hDecomp x j
  have hDself : (∫ x, hsNormSq (fun _ : Fin n => (0 : Ambient q)) ∂μ) =
      ∫ x, ∑ j : Fin n, inner ℝ (F x j) (0 : Ambient q) ∂μ := by
    simp only [hsNormSq, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0),
      inner_zero_right, Finset.sum_const_zero]
  have hOrth : (∫ x, ∑ j : Fin n, inner ℝ (0 : Ambient q) (P x j) ∂μ) = 0 := by
    simp only [inner_zero_left, Finset.sum_const_zero, integral_zero]
  have hEnergy := (hs_residual_energy_identity_of_projection_pairings μ F (fun _ _ => 0) P h
    hF hZero hP hEq hDself hSelf.2 hOrth).2.2.1
  have hEnergy' : (∫ x, hsNormSq (P x) ∂μ) + (∫ x, hsNormSq (h x) ∂μ) =
      ∫ x, hsNormSq (F x) ∂μ := by
    simpa only [hsNormSq, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0),
      Finset.sum_const_zero, integral_zero, zero_add] using hEnergy
  exact ⟨b, Db, P, h, hb, hP, hSkew, hClosed, hDivB, hNormal, hPNatural,
    hDecomp, hHLp, hHNatural, hHDiv, hHarmonic, hEnergy', hBEnergy, hHTests⟩

end StationaryHarmonicMaps.Analysis

end
