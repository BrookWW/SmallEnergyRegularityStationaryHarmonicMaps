module

public import StationaryHarmonicMaps.Analysis.CoexactRangeEulerResolvent
public import StationaryHarmonicMaps.Analysis.SolenoidalHarmonicApproximation

/-!
# Radial Euler resolvents preserve local solenoidal equations

The actual compact radial sampling remains in the original ball. The
true derivative formula therefore preserves the original zero-divergence
condition without a boundary condition on the sampled field.
-/

public section

open HarmonicMaps MeasureTheory Set Filter Metric
open scoped ContDiff Topology

namespace StationaryHarmonicMaps.Analysis

private theorem radial_sample_mem_ball {n : ℕ} (b : ℕ) (r : ℝ)
    (x : Domain n) (hx : x ∈ ball (0 : Domain n) r) (t : Icc (0 : ℝ) 1) :
    (t : ℝ) ^ b • x ∈ ball (0 : Domain n) r := by
  rw [mem_ball, dist_zero_right] at hx ⊢
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg t.property.1 b)]
  exact (mul_le_of_le_one_left (norm_nonneg x) (pow_le_one₀ t.property.1 t.property.2)).trans_lt hx

/-- The actual radial resolvents of a smooth locally solenoidal field remain solenoidal on the same ball. -/
theorem radialEulerResolvent_divergence_zero {n q : ℕ}
    (a b : ℕ) (G : Fin n → Domain n → Ambient q) (hG : ∀ i, ContDiff ℝ ∞ (G i))
    (r : ℝ)
    (hDiv : ∀ x ∈ ball (0 : Domain n) r,
      (∑ i : Fin n, fderiv ℝ (G i) x (EuclideanSpace.single i 1)) = 0)
    (x : Domain n) (hx : x ∈ ball (0 : Domain n) r) :
    (∑ i : Fin n, fderiv ℝ (radialEulerResolvent a b (G i)) x (EuclideanSpace.single i 1)) = 0 := by
  have hInt (i : Fin n) : Integrable (fun t : Icc (0 : ℝ) 1 =>
      (t : ℝ) ^ (a+b) • fderiv ℝ (G i) ((t : ℝ) ^ b • x) (EuclideanSpace.single i 1)) := by
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    exact (continuous_subtype_val.pow (a+b)).smul
      ((((hG i).continuous_fderiv (by simp)).comp
        ((continuous_subtype_val.pow b).smul continuous_const)).clm_apply continuous_const)
  simp_rw [radialEulerResolvent_fderiv_apply a b _ (hG _) x]
  rw [← integral_finsetSum Finset.univ (fun i _ => hInt i)]
  have hPoint (t : Icc (0 : ℝ) 1) : (∑ i : Fin n,
      (t : ℝ) ^ (a+b) • fderiv ℝ (G i) ((t : ℝ) ^ b • x) (EuclideanSpace.single i 1)) = 0 := by
    rw [← Finset.smul_sum, hDiv _ (radial_sample_mem_ball b r x hx t), smul_zero]
  rw [integral_congr_ae (Eventually.of_forall hPoint), integral_zero]


/-- The actual radial resolvent preserves the coefficient Laplacian equation on its original ball. -/
theorem radialEulerResolvent_laplacian_zero {n q : ℕ}
    (a b : ℕ) (f : Domain n → Ambient q) (hf : ContDiff ℝ ∞ f)
    (r : ℝ) (hLap : ∀ x ∈ ball (0 : Domain n) r, Laplacian.laplacian f x = 0)
    (x : Domain n) (hx : x ∈ ball (0 : Domain n) r) :
    Laplacian.laplacian (radialEulerResolvent a b f) x = 0 := by
  let J : Domain n × ℝ → Ambient q := fun p => p.2 ^ a • f (p.2 ^ b • p.1)
  have hJ : ContDiff ℝ ∞ J :=
    (contDiff_snd.pow a).smul (hf.comp ((contDiff_snd.pow b).smul contDiff_fst))
  have H := compactParametricIntegral_laplacian (volume : Measure (Icc (0 : ℝ) 1))
    (fun t : Icc (0 : ℝ) 1 => (t : ℝ)) continuous_subtype_val
    univ isOpen_univ univ isOpen_univ (fun _ _ _ => mem_univ _)
    J hJ.contDiffOn x (mem_univ x)
  change Laplacian.laplacian (radialEulerResolvent a b f) x = _ at H
  rw [H]
  have hPoint (t : Icc (0 : ℝ) 1) : Laplacian.laplacian (fun z : Domain n => J (z, (t : ℝ))) x = 0 := by
    have hComp : ContDiff ℝ ∞ (fun y : Domain n => f ((t : ℝ)^b • y)) :=
      hf.comp (contDiff_id.const_smul ((t : ℝ)^b))
    have hScale := InnerProductSpace.laplacian_smul ((t : ℝ)^a)
      ((hComp.of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))).contDiffAt (x := x))
    change Laplacian.laplacian ((t : ℝ)^a • (fun y : Domain n => f ((t : ℝ)^b • y))) x = 0
    rw [hScale, smooth_vector_laplacian_comp_smul f hf,
      hLap _ (radial_sample_mem_ball b r x hx t), smul_zero, smul_zero]
  rw [integral_congr_ae (Eventually.of_forall hPoint), integral_zero]


/-- The two actual radial inverses used by the closed normal potential preserve the original local harmonic and solenoidal equations and satisfy both Euler identities. -/
theorem radial_hodge_resolvents {n q : ℕ} (hn : 1 ≤ n)
    (G : Fin n → Domain n → Ambient q) (hG : ∀ i, ContDiff ℝ ∞ (G i)) (r : ℝ)
    (hDiv : ∀ x ∈ ball (0 : Domain n) r,
      (∑ i : Fin n, fderiv ℝ (G i) x (EuclideanSpace.single i 1)) = 0)
    (hLap : ∀ i x, x ∈ ball (0 : Domain n) r → Laplacian.laplacian (G i) x = 0) :
    let H := fun i x => (1/2 : ℝ) • radialEulerResolvent (n-1) 2 (G i) x
    let K := fun i => radialEulerResolvent 0 1 (H i)
    (∀ i, ContDiff ℝ ∞ (H i)) ∧ (∀ i, ContDiff ℝ ∞ (K i)) ∧
      (∀ i x, fderiv ℝ (K i) x x + K i x = H i x) ∧
      (∀ i x, G i x = (2 * (n : ℝ)) • H i x + (4 : ℝ) • fderiv ℝ (H i) x x) ∧
      (∀ x ∈ ball (0 : Domain n) r,
        (∑ i : Fin n, fderiv ℝ (H i) x (EuclideanSpace.single i 1)) = 0) ∧
      (∀ x ∈ ball (0 : Domain n) r,
        (∑ i : Fin n, fderiv ℝ (K i) x (EuclideanSpace.single i 1)) = 0) ∧
      (∀ i x, x ∈ ball (0 : Domain n) r → Laplacian.laplacian (H i) x = 0) ∧
      (∀ i x, x ∈ ball (0 : Domain n) r → Laplacian.laplacian (K i) x = 0) := by
  intro H K
  let R := fun i => radialEulerResolvent (n-1) 2 (G i)
  have hR (i : Fin n) : ContDiff ℝ ∞ (R i) := radialEulerResolvent_contDiff _ _ _ (hG i)
  have hH (i : Fin n) : ContDiff ℝ ∞ (H i) := (hR i).const_smul (1/2 : ℝ)
  have hK (i : Fin n) : ContDiff ℝ ∞ (K i) := radialEulerResolvent_contDiff _ _ _ (hH i)
  have hDH (i : Fin n) (x v : Domain n) :
      fderiv ℝ (H i) x v = (1/2 : ℝ) • fderiv ℝ (R i) x v := by
    change fderiv ℝ ((1/2 : ℝ) • R i) x v = _
    rw [fderiv_const_smul ((hR i).differentiable (by simp) x) (1/2 : ℝ)]
    rfl
  have hHD (x : Domain n) (hx : x ∈ ball (0 : Domain n) r) :
      (∑ i : Fin n, fderiv ℝ (H i) x (EuclideanSpace.single i 1)) = 0 := by
    simp_rw [hDH]
    rw [← Finset.smul_sum, radialEulerResolvent_divergence_zero (n-1) 2 G hG r hDiv x hx, smul_zero]
  have hKD := radialEulerResolvent_divergence_zero 0 1 H hH r hHD
  have hHL (i : Fin n) (x : Domain n) (hx : x ∈ ball (0 : Domain n) r) :
      Laplacian.laplacian (H i) x = 0 := by
    change Laplacian.laplacian ((1/2 : ℝ) • R i) x = 0
    rw [InnerProductSpace.laplacian_smul (1/2 : ℝ)
      (((hR i).of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))).contDiffAt),
      radialEulerResolvent_laplacian_zero (n-1) 2 (G i) (hG i) r (hLap i) x hx, smul_zero]
  have hKL := fun i => radialEulerResolvent_laplacian_zero 0 1 (H i) (hH i) r (hHL i)
  refine ⟨hH, hK, ?_, ?_, hHD, hKD, hHL, hKL⟩
  · intro i x
    have HE := radialEulerResolvent_euler_identity 0 1 (H i) (hH i) x
    simpa only [Nat.zero_add, Nat.cast_one, one_smul, add_comm] using HE
  · intro i x
    have HE := radialEulerResolvent_euler_identity (n-1) 2 (G i) (hG i) x
    have hnEq : n-1+1 = n := by omega
    rw [hnEq] at HE
    rw [← HE, hDH]
    change (n : ℝ) • R i x + (2 : ℝ) • fderiv ℝ (R i) x x =
      (2 * (n : ℝ)) • ((1/2 : ℝ) • R i x) + (4 : ℝ) • ((1/2 : ℝ) • fderiv ℝ (R i) x x)
    simp only [smul_smul]
    congr 1 <;> congr 1 <;> ring

end StationaryHarmonicMaps.Analysis

end
