module

public import StationaryHarmonicMaps.Analysis.HodgeDirichletProjection
public import StationaryHarmonicMaps.Analysis.SobolevLinearOperations
public import HarmonicMaps.SobolevRestriction

/-!
# Actual unrestricted smooth gradient space on a ball

Every ambient C1 function has its genuine native Sobolev graph on each
finite ball. The full gradients of ambient smooth functions form a true
linear subspace of the complete HS L2 coefficient space. Test functions
have arbitrary boundary values.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped ContDiff Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- Actual ambient C1 maps and their genuine derivative columns are native W1,2 on every finite ball. -/
theorem memW12_ball_of_ambient_c1 {n q : ℕ} (a : Domain n) (r : ℝ)
    (f : Domain n → Ambient q) (hf : ContDiff ℝ 1 f) :
    MemW12 (ballDomain a r) f (fun x i => fderiv ℝ f x (EuclideanSpace.single i 1)) := by
  have hLocal := memW12Loc_of_c1 (ballDomain a (r+1)) hf
  exact hLocal.memW12_ball (Metric.closedBall_subset_ball (by linarith : r < r+1))

/-- The actual full range of unrestricted smooth gradients is a linear HS L2 subspace. -/
theorem exists_smooth_gradient_submodule_ball {n q : ℕ} (a : Domain n) (r : ℝ) :
    let μ := volume.restrict (Metric.ball a r)
    let E : Gradient n q → Ambient (n*q) := fun A => WithLp.toLp 2
      (fun k => A (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)
    ∃ S : Submodule ℝ (Lp (Ambient (n*q)) 2 μ), ∀ Z, Z ∈ S ↔
      ∃ ψ : Domain n → Ambient q, ContDiff ℝ ∞ ψ ∧
        (Z : Domain n → Ambient (n*q)) =ᵐ[μ]
          (fun x => E (fun i => fderiv ℝ ψ x (EuclideanSpace.single i 1))) := by
  let μ := volume.restrict (Metric.ball a r)
  let E : Gradient n q → Ambient (n*q) := fun A => WithLp.toLp 2
    (fun k => A (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)
  let S : Submodule ℝ (Lp (Ambient (n*q)) 2 μ) :=
    { carrier := {Z | ∃ ψ : Domain n → Ambient q, ContDiff ℝ ∞ ψ ∧
        (Z : Domain n → Ambient (n*q)) =ᵐ[μ]
          (fun x => E (fun i => fderiv ℝ ψ x (EuclideanSpace.single i 1)))}
      zero_mem' := by
        refine ⟨0,contDiff_const,?_⟩
        filter_upwards [Lp.coeFn_zero (Ambient (n*q)) 2 μ] with x hx
        rw [hx]
        ext k
        change 0 = (fderiv ℝ (0 : Domain n → Ambient q) x
          (EuclideanSpace.single (finProdFinEquiv.symm k).1 1)) (finProdFinEquiv.symm k).2
        rw [fderiv_zero]
        rfl
      add_mem' := by
        rintro Z W ⟨ψ,hψ,hZ⟩ ⟨φ,hφ,hW⟩
        refine ⟨ψ+φ,hψ.add hφ,?_⟩
        filter_upwards [Lp.coeFn_add Z W,hZ,hW] with x hx hz hw
        rw [hx]
        change Z x + W x = _
        rw [hz,hw]
        ext k
        change (fderiv ℝ ψ x (EuclideanSpace.single (finProdFinEquiv.symm k).1 1))
            (finProdFinEquiv.symm k).2 +
          (fderiv ℝ φ x (EuclideanSpace.single (finProdFinEquiv.symm k).1 1))
            (finProdFinEquiv.symm k).2 =
          (fderiv ℝ (ψ+φ) x (EuclideanSpace.single (finProdFinEquiv.symm k).1 1))
            (finProdFinEquiv.symm k).2
        rw [fderiv_add (hψ.differentiable (by simp) x) (hφ.differentiable (by simp) x)]
        rfl
      smul_mem' := by
        rintro c Z ⟨ψ,hψ,hZ⟩
        refine ⟨c • ψ,contDiff_const.smul hψ,?_⟩
        filter_upwards [Lp.coeFn_smul c Z,hZ] with x hx hz
        rw [hx]
        change c • Z x = _
        rw [hz]
        ext k
        change c * (fderiv ℝ ψ x (EuclideanSpace.single (finProdFinEquiv.symm k).1 1))
          (finProdFinEquiv.symm k).2 =
          (fderiv ℝ (c • ψ) x (EuclideanSpace.single (finProdFinEquiv.symm k).1 1))
            (finProdFinEquiv.symm k).2
        rw [fderiv_const_smul (hψ.differentiable (by simp) x) c]
        rfl }
  exact ⟨S,fun _ => Iff.rfl⟩

end StationaryHarmonicMaps.Analysis

end
