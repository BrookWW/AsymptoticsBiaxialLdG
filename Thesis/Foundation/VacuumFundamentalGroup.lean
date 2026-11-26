module

public import Thesis.Foundation.Sphere3Topology
public import Thesis.Foundation.VacuumQuaternionDeck
public import Mathlib.Topology.Homotopy.Lifting

/-! The vacuum quotient and its fundamental group through the quaternion cover. -/

public section

noncomputable section

open Metric Set
open scoped Quaternion

namespace Thesis

/-- The vacuum is the orbit quotient of the sphere of unit quaternions. -/
@[expose] def vacuumQuaternionQuotientHomeomorph (a : BulkCoefficients) :
    Quotient (MulAction.orbitRel (QuaternionGroup 2) Sphere3) ≃ₜ vacuum a := by
  let descend : Quotient (MulAction.orbitRel (QuaternionGroup 2) Sphere3) → vacuum a :=
    Quotient.lift (s := MulAction.orbitRel (QuaternionGroup 2) Sphere3) (vacuumQuaternionProjection a)
      (fun _ _ h => (vacuumQuaternionProjection_eq_iff_orbit a).2 h)
  have hBijective : Function.Bijective descend := by
    constructor
    · intro x y
      refine Quotient.inductionOn₂ x y ?_
      intro v w h
      exact Quotient.sound ((vacuumQuaternionProjection_eq_iff_orbit a).1 h)
    · intro A
      obtain ⟨v, hv⟩ := vacuumQuaternionProjection_surjective a A
      exact ⟨Quotient.mk _ v, hv⟩
  letI : CompactSpace Sphere3 := isCompact_iff_compactSpace.1 (isCompact_sphere _ _)
  exact Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective descend hBijective)
    (continuous_quot_lift _ (continuous_vacuumQuaternionProjection a))

@[simp] theorem vacuumQuaternionQuotientHomeomorph_apply (a : BulkCoefficients) (v : Sphere3) :
    vacuumQuaternionQuotientHomeomorph a (Quotient.mk _ v) = vacuumQuaternionProjection a v :=
  rfl

private def unopInvQuaternionGroup : (QuaternionGroup 2)ᵐᵒᵖ ≃* QuaternionGroup 2 where
  toFun g := g.unop⁻¹
  invFun g := MulOpposite.op g⁻¹
  left_inv g := by simp
  right_inv g := by simp
  map_mul' g h := by simp [mul_inv_rev]

/-- The fundamental group is identified by the right multiplier of a lifted loop. -/
def vacuumFundamentalGroupEquiv (a : BulkCoefficients) (v : Sphere3) :
    FundamentalGroup (vacuum a) (vacuumQuaternionProjection a v) ≃* QuaternionGroup 2 :=
  letI : SimplyConnectedSpace Sphere3 := simplyConnectedSpace_sphere3
  ((vacuumQuaternionProjection_isQuotientCoveringMap a).fundamentalGroupEquiv
      ⟨v, rfl⟩).trans unopInvQuaternionGroup

/-- The endpoint of a lifted loop is its starting quaternion times the group element
represented by the loop. -/
theorem vacuumFundamentalGroupEquiv_monodromy (a : BulkCoefficients) (v : Sphere3)
    (γ : FundamentalGroup (vacuum a) (vacuumQuaternionProjection a v)) :
    Quaternion.linearIsometryEquivTuple.symm
        ((vacuumQuaternionProjection_isCoveringMap a).monodromy γ ⟨v, rfl⟩).val.val =
      Quaternion.linearIsometryEquivTuple.symm v.val *
        quaternionWordReal (vacuumFundamentalGroupEquiv a v γ) := by
  let hp := vacuumQuaternionProjection_isQuotientCoveringMap a
  let e : (vacuumQuaternionProjection a) ⁻¹' {vacuumQuaternionProjection a v} := ⟨v, rfl⟩
  let g := (hp.fundamentalGroupToMulOpposite e γ).unop
  have hend : g • v = (hp.isCoveringMap.monodromy γ e).val :=
    hp.unop_fundamentalGroupToMulOpposite_smul
  change Quaternion.linearIsometryEquivTuple.symm (hp.isCoveringMap.monodromy γ e).val.val =
    Quaternion.linearIsometryEquivTuple.symm v.val * quaternionWordReal g⁻¹
  rw [← hend, quaternionTuple_symm_smul]

/-- Every based vacuum loop has a continuous lift with the stated quaternion endpoint. -/
theorem vacuumLoop_exists_lift (a : BulkCoefficients) (v : Sphere3)
    (γ : Path (vacuumQuaternionProjection a v) (vacuumQuaternionProjection a v)) :
    ∃ Γ : C(unitInterval, Sphere3),
      Γ 0 = v ∧ (∀ t, vacuumQuaternionProjection a (Γ t) = γ t) ∧
      Quaternion.linearIsometryEquivTuple.symm (Γ 1).val =
        Quaternion.linearIsometryEquivTuple.symm v.val *
          quaternionWordReal (vacuumFundamentalGroupEquiv a v
            (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ))) := by
  let hp := vacuumQuaternionProjection_isCoveringMap a
  let Γ := hp.liftPath γ.toContinuousMap v γ.source
  refine ⟨Γ, hp.liftPath_zero .., ?_, ?_⟩
  · intro t
    exact congrFun (hp.liftPath_lifts γ.toContinuousMap v γ.source) t
  · exact vacuumFundamentalGroupEquiv_monodromy a v
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ))

/-- A based vacuum loop lifts to a closed path exactly when its class is trivial. -/
theorem vacuumLoop_exists_closed_lift_iff (a : BulkCoefficients) (v : Sphere3)
    (γ : Path (vacuumQuaternionProjection a v) (vacuumQuaternionProjection a v)) :
    (∃ Γ : Path v v, ∀ t, vacuumQuaternionProjection a (Γ t) = γ t) ↔
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ) = 1 := by
  obtain ⟨Γ, hzero, hproj, hone⟩ := vacuumLoop_exists_lift a v γ
  constructor
  · rintro ⟨Γ', hproj'⟩
    have h₁ : (fun t => Γ' t) = Γ :=
      (vacuumQuaternionProjection_isCoveringMap a).eq_of_comp_eq
        Γ'.continuous Γ.continuous (funext fun t => (hproj' t).trans (hproj t).symm)
        0 (Γ'.source.trans hzero.symm)
    have hΓ : Γ 1 = v := (congrFun h₁ 1).symm.trans Γ'.target
    rw [hΓ] at hone
    apply (vacuumFundamentalGroupEquiv a v).injective
    simp only [map_one]
    apply quaternionWordReal_injective
    have hv : Quaternion.linearIsometryEquivTuple.symm v.val ≠ 0 := by
      intro hz
      have hnorm := quaternionTuple_symm_norm_eq_one v
      rw [hz, norm_zero] at hnorm
      exact zero_ne_one hnorm
    apply mul_left_cancel₀ hv
    simpa only [map_one, mul_one] using hone.symm
  · intro hγ
    have hΓ : Quaternion.linearIsometryEquivTuple.symm (Γ 1).val =
        Quaternion.linearIsometryEquivTuple.symm v.val := by
      simpa only [hγ, (vacuumFundamentalGroupEquiv a v).map_one, quaternionWordReal.map_one,
        mul_one] using hone
    exact ⟨⟨Γ, hzero, Subtype.ext (Quaternion.linearIsometryEquivTuple.symm.injective hΓ)⟩,
      hproj⟩

/-- A continuous vacuum map on a sphere of dimension at least two has the
unique continuous lift with the chosen basepoint value. -/
theorem vacuumSphere_existsUnique_continuous_lift (a : BulkCoefficients) {d : ℕ} (hd : 2 ≤ d)
    (f : C(sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) 1, vacuum a))
    (x : sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) 1) (v : Sphere3)
    (hv : vacuumQuaternionProjection a v = f x) :
    ∃! g : C(sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) 1, Sphere3),
      g x = v ∧ ∀ y, vacuumQuaternionProjection a (g y) = f y := by
  letI := simplyConnectedSpace_unitSphere hd
  letI := locallyPathConnectedSpace_unitSphere d
  simpa only [funext_iff, Function.comp_apply] using
    (vacuumQuaternionProjection_isCoveringMap a).existsUnique_continuousMap_lifts f x v hv

end Thesis
