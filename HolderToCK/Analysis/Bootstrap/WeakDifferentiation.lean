module

public import HolderToCK.Analysis.ClassicalPoisson
public import HolderToCK.Analysis.ClassicalWeakGradient
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! # One classical derivative of the same weak Poisson equation

C2 symmetry of the solution and the actual smooth test commutes the coordinate
derivatives. Compact integration by parts then supplies the differentiated
forcing, with the same negative sign and native local Sobolev data.
-/

public section

open HarmonicMaps MeasureTheory Set
open scoped ContDiff Topology

namespace HolderToCK

theorem fderiv_direction_swap_of_contDiffAt_two {n q : ℕ}
    (u : Domain n → Ambient q) (x : Domain n) (hu : ContDiffAt ℝ 2 u x)
    (v w : Domain n) :
    fderiv ℝ (fun z => fderiv ℝ u z v) x w =
      fderiv ℝ (fun z => fderiv ℝ u z w) x v := by
  have hDu : DifferentiableAt ℝ (fderiv ℝ u) x :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hsym := hu.isSymmSndFDerivAt (by
    simpa only [minSmoothness_of_isRCLikeNormedField] using (le_rfl : (2 : ℕ∞ω) ≤ 2))
  rw [fderiv_clm_apply hDu (differentiableAt_const _),
    fderiv_clm_apply hDu (differentiableAt_const _)]
  simp only [fderiv_const_apply, ContinuousLinearMap.comp_zero,
    zero_add, ContinuousLinearMap.flip_apply]
  exact hsym w v

theorem contDiff_fderiv_apply {n q : ℕ} {ψ : Domain n → Ambient q}
    (hψ : ContDiff ℝ ∞ ψ) (v : Domain n) :
    ContDiff ℝ ∞ (fun x => fderiv ℝ ψ x v) :=
  contDiffOn_univ.mp ((hψ.contDiffOn.fderiv_of_isOpen isOpen_univ (by simp)).clm_apply
    contDiffOn_const)

theorem WeakPoissonOn.coordinateDerivative {n q : ℕ} (Ω : OpenDomain n)
    {u F : Domain n → Ambient q} (hu : ContDiffOn ℝ 2 u Ω.val)
    (hF : ContDiffOn ℝ 1 F Ω.val)
    (hEq : WeakPoissonOn Ω (fun x j => fderiv ℝ u x (EuclideanSpace.single j 1)) F)
    (i : Fin n) :
    MemW12Loc Ω (fun x => fderiv ℝ u x (EuclideanSpace.single i 1))
      (fun x j => fderiv ℝ (fun z => fderiv ℝ u z (EuclideanSpace.single i 1)) x
        (EuclideanSpace.single j 1)) ∧
    WeakPoissonOn Ω
      (fun x j => fderiv ℝ (fun z => fderiv ℝ u z (EuclideanSpace.single i 1)) x
        (EuclideanSpace.single j 1))
      (fun x => fderiv ℝ F x (EuclideanSpace.single i 1)) := by
  have hcolumn (j : Fin n) : ContDiffOn ℝ 1
      (fun x => fderiv ℝ u x (EuclideanSpace.single j 1)) Ω.val :=
    (hu.fderiv_of_isOpen Ω.property (by norm_num : (1 : ℕ∞ω) + 1 ≤ 2)).clm_apply
      contDiffOn_const
  have hFcolumn : ContinuousOn (fun x => fderiv ℝ F x (EuclideanSpace.single i 1)) Ω.val :=
    (hF.continuousOn_fderiv_of_isOpen Ω.property le_rfl).clm_apply continuousOn_const
  refine ⟨memW12Loc_of_contDiffOn_one Ω (hcolumn i),
    hFcolumn.locallyIntegrableOn Ω.property.measurableSet, ?_⟩
  intro ψ hψ hcψ hsψ
  have htestSmooth (j : Fin n) := contDiff_fderiv_apply hψ (EuclideanSpace.single j 1)
  have htestCompact (j : Fin n) := hcψ.fderiv_apply ℝ (EuclideanSpace.single j 1)
  have htestSupport (j : Fin n) :
      tsupport (fun x => fderiv ℝ ψ x (EuclideanSpace.single j 1)) ⊆ Ω.val :=
    (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single j 1)).trans hsψ
  have hbase := hEq.2 (fun x => fderiv ℝ ψ x (EuclideanSpace.single i 1))
    (htestSmooth i) (htestCompact i) (htestSupport i)
  have hpair (j : Fin n) := compact_test_inner_fderiv_integral Ω (hcolumn j)
    (htestSmooth j) (htestCompact j) (htestSupport j) i
  have hforce := compact_test_inner_fderiv_integral Ω hF hψ hcψ hsψ i
  have hswap (x : Domain n) (hx : x ∈ Ω.val) (j : Fin n) :
      fderiv ℝ (fun z => fderiv ℝ u z (EuclideanSpace.single i 1)) x
        (EuclideanSpace.single j 1) =
      fderiv ℝ (fun z => fderiv ℝ u z (EuclideanSpace.single j 1)) x
        (EuclideanSpace.single i 1) :=
    fderiv_direction_swap_of_contDiffAt_two u x (hu.contDiffAt (Ω.property.mem_nhds hx)) _ _
  have hψtwo : ContDiff ℝ 2 ψ := hψ.of_le
    (le_of_lt (WithTop.coe_lt_coe.mpr (WithTop.coe_lt_top (2 : ℕ))))
  have htestSwap (x : Domain n) (j : Fin n) :
      fderiv ℝ (fun z => fderiv ℝ ψ z (EuclideanSpace.single j 1)) x
        (EuclideanSpace.single i 1) =
      fderiv ℝ (fun z => fderiv ℝ ψ z (EuclideanSpace.single i 1)) x
        (EuclideanSpace.single j 1) :=
    fderiv_direction_swap_of_contDiffAt_two ψ x hψtwo.contDiffAt _ _
  have hleft (j : Fin n) : IntegrableOn (fun x => inner ℝ
      (fderiv ℝ (fun z => fderiv ℝ u z (EuclideanSpace.single i 1)) x
        (EuclideanSpace.single j 1)) (fderiv ℝ ψ x (EuclideanSpace.single j 1))) Ω.val := by
    apply (hpair j).1.congr
    filter_upwards [ae_restrict_mem Ω.property.measurableSet] with x hx
    rw [hswap x hx j]
  refine ⟨integrable_finsetSum Finset.univ (fun j _ => hleft j), hforce.1, ?_⟩
  rw [integral_finsetSum _ (fun j _ => hleft j)]
  have hsign (j : Fin n) :
      (∫ x in Ω.val, inner ℝ
        (fderiv ℝ (fun z => fderiv ℝ u z (EuclideanSpace.single i 1)) x
          (EuclideanSpace.single j 1)) (fderiv ℝ ψ x (EuclideanSpace.single j 1))) =
      -(∫ x in Ω.val, inner ℝ (fderiv ℝ u x (EuclideanSpace.single j 1))
        (fderiv ℝ (fun z => fderiv ℝ ψ z (EuclideanSpace.single i 1)) x
          (EuclideanSpace.single j 1))) := by
    calc
      _ = ∫ x in Ω.val, inner ℝ
          (fderiv ℝ (fun z => fderiv ℝ u z (EuclideanSpace.single j 1)) x
            (EuclideanSpace.single i 1)) (fderiv ℝ ψ x (EuclideanSpace.single j 1)) :=
        setIntegral_congr_fun Ω.property.measurableSet (fun x hx => by rw [hswap x hx j])
      _ = _ := by
        rw [(hpair j).2.2]
        simp_rw [htestSwap]
  simp_rw [hsign]
  rw [Finset.sum_neg_distrib, ← integral_finsetSum]
  · rw [hbase.2.2, neg_neg]
    exact neg_eq_iff_eq_neg.mp hforce.2.2.symm
  · intro j _
    have hI := (hpair j).2.1
    change Integrable (fun x => inner ℝ (fderiv ℝ u x (EuclideanSpace.single j 1))
      (fderiv ℝ (fun z => fderiv ℝ ψ z (EuclideanSpace.single j 1)) x
        (EuclideanSpace.single i 1))) (volume.restrict Ω.val) at hI
    simpa only [htestSwap] using hI

end HolderToCK
end
