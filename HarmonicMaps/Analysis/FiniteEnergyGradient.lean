module

public import HarmonicMaps.EnergyLemmas
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Gradient columns from finite Hilbert--Schmidt energy

Each measurable column is controlled by the nonnegative HS density. Finite
extended energy therefore supplies its L2 membership without assuming global
L2 membership of the gradient in advance.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped ENNReal BigOperators

namespace HarmonicMaps

/-- A measurable column belongs to L2 when the extended HS integral is finite. -/
theorem memLp_column_of_lintegral_hsNormSq_ne_top
    {α : Type*} [MeasurableSpace α] {n q : ℕ} {μ : Measure α}
    {Du : α → Gradient n q} (i : Fin n)
    (hcolumn : AEStronglyMeasurable (fun x => Du x i) μ)
    (henergy : (∫⁻ x, ENNReal.ofReal (hsNormSq (Du x)) ∂μ) ≠ ⊤) :
    MemLp (fun x => Du x i) 2 μ := by
  have hcolumn_le : ∀ x, ‖Du x i‖ ^ 2 ≤ hsNormSq (Du x) := by
    intro x
    exact Finset.single_le_sum (fun j _ => sq_nonneg ‖Du x j‖) (Finset.mem_univ i)
  have hcolumn_integral :
      (∫⁻ x, ENNReal.ofReal (‖Du x i‖ ^ 2) ∂μ) ≠ ⊤ :=
    ne_top_of_le_ne_top henergy
      (lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hcolumn_le x))
  have hsquare_measurable : AEStronglyMeasurable (fun x => ‖Du x i‖ ^ 2) μ :=
    (hcolumn.norm.aemeasurable.pow_const (2 : ℕ)).aestronglyMeasurable
  have hsquare_integrable : Integrable (fun x => ‖Du x i‖ ^ 2) μ :=
    (lintegral_ofReal_ne_top_iff_integrable hsquare_measurable
      (Eventually.of_forall fun x => sq_nonneg ‖Du x i‖)).mp hcolumn_integral
  exact (memLp_two_iff_integrable_sq_norm hcolumn).mpr hsquare_integrable

/-- Local integrability in a weak gradient gives the measurability needed for
finite energy to supply L2 membership on the whole open domain. -/
theorem HasWeakGradient.memLp_columns_of_dirichletEnergy_ne_top
    {n q : ℕ} {Ω : OpenDomain n} {u : Domain n → Ambient q}
    {Du : Domain n → Gradient n q} (hDu : HasWeakGradient Ω u Du)
    (henergy : dirichletEnergy Du Ω.val ≠ ⊤) :
    ∀ i : Fin n, MemLp (fun x => Du x i) 2 (volume.restrict Ω.val) := by
  intro i
  exact memLp_column_of_lintegral_hsNormSq_ne_top i
    (hDu.2.1 i).aestronglyMeasurable henergy

/-- Unit-ball local Sobolev data and finite total energy give L2 membership
of every original gradient column on the entire unit ball. -/
theorem MemW12Loc.memLp_gradient_columns_unitBall_of_finiteEnergy
    {n q : ℕ} {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hLocal : MemW12Loc (ballDomain (0 : Domain n) 1) u Du)
    (henergy : dirichletEnergy Du (Metric.ball (0 : Domain n) 1) ≠ ⊤) :
    ∀ i : Fin n,
      MemLp (fun x => Du x i) 2
        (volume.restrict (Metric.ball (0 : Domain n) 1)) :=
  hLocal.1.memLp_columns_of_dirichletEnergy_ne_top henergy

end HarmonicMaps
