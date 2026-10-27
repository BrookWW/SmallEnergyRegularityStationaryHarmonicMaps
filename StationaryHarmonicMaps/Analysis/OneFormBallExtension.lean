module

public import StationaryHarmonicMaps.Analysis.SolenoidalBallExtension
public import StationaryHarmonicMaps.Analysis.PhysicalOneFormCoordinates

/-!
# Vector-valued solenoidal extension from any ball

Each original target coordinate is extended by the actual arbitrary-ball
physical Kelvin producer. Finite coefficient transposition preserves the
complete HS square, and the original scalar equations reconstruct every
whole-space vector test.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped ContDiff Topology

namespace StationaryHarmonicMaps.Analysis

/-- Raw vector-valued solenoidal L2 one-forms on any positive-radius ball have a genuine whole-space solenoidal extension with the same coefficient-two full-HS energy bound. -/
theorem exists_solenoidal_oneForm_L2_extension_ball {n q : ℕ} (hn : 2≤n)
    (a : Domain n) (r : ℝ) (hr : 0<r)
    (F : Domain n → Gradient n q)
    (hF : ∀ i, MemLp (fun x => F x i) 2
      (volume.restrict (Metric.ball a r)))
    (hDiv : HolderToCK.WeakPoissonOn (ballDomain a r) F
      (fun _ => (0 : Ambient q))) :
    ∃ G : Domain n → Gradient n q,
      (∀ i, MemLp (fun x => G x i) 2 volume) ∧
      (G =ᵐ[volume.restrict (Metric.ball a r)] F) ∧
      (∫ x, hsNormSq (G x)) ≤
        2*(∫ x in Metric.ball a r, hsNormSq (F x)) ∧
      HolderToCK.WeakPoissonOn (⟨univ,isOpen_univ⟩ : OpenDomain n) G
        (fun _ => (0 : Ambient q)) := by
  classical
  let B := Metric.ball a r
  let Z := fun (j : Fin q) (x : Domain n) => WithLp.toLp 2 (fun i : Fin n => F x i j)
  have hZ (j : Fin q) : MemLp (Z j) 2 (volume.restrict B) :=
    physical_coordinate_memLp F hF j
  have hPhysical (j : Fin q) :
      ∃ z : Domain n → Domain n, MemLp z 2 volume ∧
        (∀ᵐ x ∂volume.restrict B,z x=Z j x) ∧
        (∫ x, ‖z x‖^2) ≤ 2*(∫ x in B,‖Z j x‖^2) ∧
        ∀ (η : Domain n → ℝ), ContDiff ℝ ∞ η → HasCompactSupport η →
          Integrable (fun x => fderiv ℝ η x (z x)) volume ∧
            (∫ x, fderiv ℝ η x (z x))=0 := by
    apply exists_solenoidal_L2_extension_ball hn a r hr (Z j) (hZ j)
    intro η hη hcη hsη
    exact (physical_coordinate_divergence_zero (ballDomain a r)
      F hDiv j η hη hcη hsη).2
  choose z hz hInside hEnergy hTests using hPhysical
  let G := fun (x : Domain n) (i : Fin n) => WithLp.toLp 2 (fun j : Fin q => z j x i)
  have hG (i : Fin n) : MemLp (fun x => G x i) 2 volume := by
    let L : (Fin q → Domain n) →ₗ[ℝ] Ambient q :=
      { toFun := fun A => WithLp.toLp 2 (fun j => A j i)
        map_add' := fun A C => by ext j; rfl
        map_smul' := fun c A => by ext j; rfl }
    exact L.toContinuousLinearMap.lipschitz.comp_memLp (map_zero L) (MemLp.of_eval hz)
  have hInsideAll : ∀ᵐ x ∂volume.restrict B, ∀ j : Fin q,z j x=Z j x :=
    ae_all_iff.mpr hInside
  have hMap : G =ᵐ[volume.restrict B] F := by
    filter_upwards [hInsideAll] with x hx
    funext i
    ext j
    exact congrArg (fun v : Domain n => v i) (hx j)
  have hGPhysical (j : Fin q) (x : Domain n) :
      WithLp.toLp 2 (fun i : Fin n => G x i j)=z j x := by
    ext i
    rfl
  have hGPoint (x : Domain n) : hsNormSq (G x)=∑ j : Fin q,‖z j x‖^2 := by
    simpa only [hGPhysical] using hsNormSq_eq_sum_physical_norm_sq (G x)
  have hFPoint (x : Domain n) : hsNormSq (F x)=∑ j : Fin q,‖Z j x‖^2 :=
    hsNormSq_eq_sum_physical_norm_sq (F x)
  have hEnergyG : (∫ x,hsNormSq (G x)) ≤ 2*(∫ x in B,hsNormSq (F x)) := by
    rw [integral_congr_ae (Eventually.of_forall hGPoint),
      integral_finsetSum _ (fun j _ => (hz j).integrable_norm_pow (by decide : (2 : ℕ)≠0)),
      integral_congr_ae (Eventually.of_forall hFPoint),
      integral_finsetSum _ (fun j _ => (hZ j).integrable_norm_pow (by decide : (2 : ℕ)≠0)),
      Finset.mul_sum]
    exact Finset.sum_le_sum (fun j _ => hEnergy j)
  refine ⟨G,hG,hMap,hEnergyG,?_⟩
  apply weakPoissonOn_zero_of_physical_coordinates G
  intro j η hη hcη
  simpa only [hGPhysical] using hTests j η hη hcη

end StationaryHarmonicMaps.Analysis

end
