module

public import StationaryHarmonicMaps.Analysis.PhysicalDivergenceTests
public import StationaryHarmonicMaps.Analysis.ScalarVectorWeakEquation
public import StationaryHarmonicMaps.Analysis.HilbertSchmidtEncoding

/-!
# Physical vectors of the original one-form target coordinates

Each target coordinate is a genuine Euclidean vector in the domain
dimension. The full coefficient energy is the sum of all these vector
energies. Original vector weak-divergence tests produce the scalar
physical divergence identities used by the Kelvin extension.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped ContDiff Topology

namespace StationaryHarmonicMaps.Analysis

/-- Actual L2 columns give L2 membership of each original physical target-coordinate vector. -/
theorem physical_coordinate_memLp {X : Type*} [MeasurableSpace X]
    {n q : ℕ} {μ : Measure X} (F : X → Gradient n q)
    (hF : ∀ i, MemLp (fun x => F x i) 2 μ) (j : Fin q) :
    MemLp (fun x => WithLp.toLp 2 (fun i : Fin n => F x i j)) 2 μ := by
  let L : Gradient n q →ₗ[ℝ] Domain n :=
    { toFun := fun A => WithLp.toLp 2 (fun i => A i j)
      map_add' := fun A B => by ext i; rfl
      map_smul' := fun c A => by ext i; rfl }
  exact L.toContinuousLinearMap.lipschitz.comp_memLp (map_zero L) (MemLp.of_eval hF)

/-- Transposing the finite coefficient indices retains the complete HS energy exactly. -/
theorem hsNormSq_eq_sum_physical_norm_sq {n q : ℕ} (F : Gradient n q) :
    hsNormSq F = ∑ j : Fin q, ‖WithLp.toLp 2 (fun i : Fin n => F i j)‖^2 := by
  simp only [hsNormSq,EuclideanSpace.real_norm_sq_eq]
  exact Finset.sum_comm

/-- A genuine linear functional on a physical coordinate vector has the actual basis expansion. -/
theorem physical_coordinate_apply {n q : ℕ} (F : Gradient n q) (j : Fin q)
    (L : Domain n →L[ℝ] ℝ) :
    L (WithLp.toLp 2 (fun i : Fin n => F i j)) =
      ∑ i : Fin n, F i j * L (EuclideanSpace.single i 1) := by
  let z : Domain n := WithLp.toLp 2 (fun i => F i j)
  have hz : (∑ i : Fin n, z i • EuclideanSpace.single i 1)=z := by
    simpa only [EuclideanSpace.basisFun_repr,EuclideanSpace.basisFun_apply] using
      (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr z
  calc
    _ = L (∑ i : Fin n,z i • EuclideanSpace.single i 1) := congrArg L hz.symm
    _ = _ := by simp only [map_sum,map_smul,smul_eq_mul]; rfl

/-- The original vector weak-divergence equation produces each actual scalar physical coordinate equation and its L1 pairing. -/
theorem physical_coordinate_divergence_zero {n q : ℕ} (Ω : OpenDomain n)
    (F : Domain n → Gradient n q)
    (hDiv : HolderToCK.WeakPoissonOn Ω F (fun _ => (0 : Ambient q)))
    (j : Fin q) (η : Domain n → ℝ) (hη : ContDiff ℝ ∞ η)
    (hcη : HasCompactSupport η) (hsη : tsupport η ⊆ Ω.val) :
    IntegrableOn (fun x => fderiv ℝ η x (WithLp.toLp 2 (fun i : Fin n => F x i j)))
      Ω.val volume ∧
    (∫ x in Ω.val, fderiv ℝ η x (WithLp.toLp 2 (fun i : Fin n => F x i j)))=0 := by
  let e : Ambient q := EuclideanSpace.single j 1
  let ψ := fun x => η x • e
  have hψ : ContDiff ℝ ∞ ψ := hη.smul contDiff_const
  have hcψ : HasCompactSupport ψ := hcη.smul_right
  have hsψ : tsupport ψ ⊆ Ω.val :=
    (tsupport_smul_subset_left η (fun _ => e)).trans hsη
  have hDψ (x : Domain n) (i : Fin n) :
      fderiv ℝ ψ x (EuclideanSpace.single i 1) =
        fderiv ℝ η x (EuclideanSpace.single i 1) • e := by
    exact congrArg (fun L : Domain n →L[ℝ] Ambient q => L (EuclideanSpace.single i 1))
      ((hη.differentiable (by simp) x).hasFDerivAt.smul_const e).fderiv
  obtain ⟨hI,_hZero,hEq⟩ := hDiv.2 ψ hψ hcψ hsψ
  have hPoint (x : Domain n) : (∑ i : Fin n, inner ℝ (F x i)
      (fderiv ℝ ψ x (EuclideanSpace.single i 1))) =
        fderiv ℝ η x (WithLp.toLp 2 (fun i : Fin n => F x i j)) := by
    rw [physical_coordinate_apply]
    simp only [hDψ,real_inner_smul_right,e,EuclideanSpace.inner_single_right,
      conj_trivial,one_mul]
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  refine ⟨hI.congr (Eventually.of_forall hPoint),?_⟩
  rw [← integral_congr_ae (Eventually.of_forall hPoint)]
  simpa only [inner_zero_left,integral_zero,neg_zero] using hEq

/-- Actual scalar physical divergence equations reconstruct every global vector weak test. -/
theorem weakPoissonOn_zero_of_physical_coordinates {n q : ℕ}
    (F : Domain n → Gradient n q)
    (hDiv : ∀ (j : Fin q) (η : Domain n → ℝ), ContDiff ℝ ∞ η →
      HasCompactSupport η →
      Integrable (fun x => fderiv ℝ η x (WithLp.toLp 2 (fun i : Fin n => F x i j))) volume ∧
      (∫ x, fderiv ℝ η x (WithLp.toLp 2 (fun i : Fin n => F x i j)))=0) :
    HolderToCK.WeakPoissonOn (⟨univ,isOpen_univ⟩ : OpenDomain n) F (fun _ => (0 : Ambient q)) := by
  refine ⟨locallyIntegrableOn_zero,?_⟩
  intro ψ hψ hcψ _hsψ
  let η := fun (j : Fin q) (x : Domain n) => ψ x j
  have hη (j : Fin q) : ContDiff ℝ ∞ (η j) :=
    (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin q => ℝ) j).contDiff.comp hψ
  have hcη (j : Fin q) : HasCompactSupport (η j) :=
    hcψ.comp_left (g := fun z : Ambient q => z j) rfl
  have hDη (j : Fin q) (x v : Domain n) :
      fderiv ℝ (η j) x v = (fderiv ℝ ψ x v) j := by
    have H := ((PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin q => ℝ) j).hasFDerivAt.comp x
      (hψ.differentiable (by simp) x).hasFDerivAt).fderiv
    exact congrArg (fun L : Domain n →L[ℝ] ℝ => L v) H
  have H (j : Fin q) := hDiv j (η j) (hη j) (hcη j)
  have hPoint (x : Domain n) :
      (∑ i : Fin n, inner ℝ (F x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1))) =
      ∑ j : Fin q, fderiv ℝ (η j) x (WithLp.toLp 2 (fun i : Fin n => F x i j)) := by
    calc
      _ = ∑ i : Fin n, ∑ j : Fin q,
          F x i j * (fderiv ℝ ψ x (EuclideanSpace.single i 1)) j := by
        simp only [PiLp.inner_apply,Real.inner_apply]
      _ = ∑ j : Fin q, ∑ i : Fin n,
          F x i j * (fderiv ℝ ψ x (EuclideanSpace.single i 1)) j := Finset.sum_comm
      _ = _ := by simp_rw [physical_coordinate_apply,hDη]
  have hI : Integrable (fun x => ∑ i : Fin n,
      inner ℝ (F x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1))) volume :=
    (integrable_finsetSum _ (fun j _ => (H j).1)).congr
      (Eventually.of_forall fun x => (hPoint x).symm)
  refine ⟨?_,by simp,?_⟩
  · change Integrable _ (volume.restrict univ)
    rw [Measure.restrict_univ]
    exact hI
  change (∫ x, ∑ i : Fin n,
      inner ℝ (F x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1)) ∂volume.restrict univ) =
      -(∫ x, inner ℝ (0 : Ambient q) (ψ x) ∂volume.restrict univ)
  rw [Measure.restrict_univ,integral_congr_ae (Eventually.of_forall hPoint),
    integral_finsetSum _ (fun j _ => (H j).1)]
  simp only [(H _).2,Finset.sum_const_zero,inner_zero_left,integral_zero,neg_zero]

end StationaryHarmonicMaps.Analysis

end
