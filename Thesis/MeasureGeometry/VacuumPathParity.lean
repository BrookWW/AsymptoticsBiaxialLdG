module

public import Thesis.MeasureGeometry.JunctionWord
import Thesis.Foundation.Sphere3Topology
import Mathlib.Topology.Subpath

/-! The light quaternion character on paths, including subdivision and free homotopy. -/

@[expose] public section

noncomputable section

open scoped Topology

namespace Thesis

/-- Fix paths from one chosen vacuum value to every other vacuum value. -/
def pathFromVacuumRoot (a : BulkCoefficients) (v : Sphere3) (A : vacuum a) :
    Path (vacuumQuaternionProjection a v) A := by
  letI : SimplyConnectedSpace Sphere3 := simplyConnectedSpace_sphere3
  let w := (vacuumQuaternionProjection_surjective a A).choose
  have hw : vacuumQuaternionProjection a w = A :=
    (vacuumQuaternionProjection_surjective a A).choose_spec
  exact ((PathConnectedSpace.somePath v w).map (continuous_vacuumQuaternionProjection a)).cast rfl hw.symm

/-- The quaternion word obtained after transporting the endpoints of a vacuum path. -/
def vacuumPathWord (a : BulkCoefficients) (v : Sphere3)
    {A B : vacuum a} (p : Path A B) : QuaternionGroup 2 :=
  vacuumFundamentalGroupEquiv a v (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
    ((pathFromVacuumRoot a v A).trans (p.trans (pathFromVacuumRoot a v B).symm))))

/-- The light character of a path after transporting both endpoints to one fixed vacuum.
It adds under concatenation with the same endpoint transport. -/
def vacuumPathLightParity (a : BulkCoefficients) (v : Sphere3)
    {A B : vacuum a} (p : Path A B) : ZMod 2 :=
  (quaternionLightCharacter (vacuumPathWord a v p)).toAdd

theorem vacuumPathLightParity_homotopic (a : BulkCoefficients) (v : Sphere3)
    {A B : vacuum a} {p q : Path A B} (h : p.Homotopic q) :
    vacuumPathLightParity a v p = vacuumPathLightParity a v q := by
  unfold vacuumPathLightParity vacuumPathWord
  simp only [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.eq.mpr h]

theorem vacuumPathLightParity_refl (a : BulkCoefficients) (v : Sphere3) (A : vacuum a) :
    vacuumPathLightParity a v (Path.refl A) = 0 := by
  unfold vacuumPathLightParity vacuumPathWord
  simp only [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_refl,
    Path.Homotopic.Quotient.mk_symm, Path.Homotopic.Quotient.refl_trans,
    Path.Homotopic.Quotient.trans_symm]
  rw [show FundamentalGroup.fromPath
    (Path.Homotopic.Quotient.refl (vacuumQuaternionProjection a v)) = 1 from rfl, map_one, map_one]
  rfl

theorem vacuumPathLightParity_trans (a : BulkCoefficients) (v : Sphere3)
    {A B C : vacuum a} (p : Path A B) (q : Path B C) :
    vacuumPathLightParity a v (p.trans q) =
      vacuumPathLightParity a v p + vacuumPathLightParity a v q := by
  let c (Y : vacuum a) := Path.Homotopic.Quotient.mk (pathFromVacuumRoot a v Y)
  let P := Path.Homotopic.Quotient.mk p
  let Q := Path.Homotopic.Quotient.mk q
  have h : (c A).trans ((P.trans Q).trans (c C).symm) =
      ((c A).trans (P.trans (c B).symm)).trans ((c B).trans (Q.trans (c C).symm)) := by
    simp only [Path.Homotopic.Quotient.trans_assoc]
    rw [← Path.Homotopic.Quotient.trans_assoc (c B).symm (c B),
      Path.Homotopic.Quotient.symm_trans, Path.Homotopic.Quotient.refl_trans]
  let χ := quaternionLightCharacter.comp (vacuumFundamentalGroupEquiv a v).toMonoidHom
  simp only [vacuumPathLightParity, vacuumPathWord, Path.Homotopic.Quotient.mk_trans,
    Path.Homotopic.Quotient.mk_symm]
  change (χ (FundamentalGroup.fromPath ((c A).trans ((P.trans Q).trans (c C).symm)))).toAdd =
    (χ (FundamentalGroup.fromPath ((c A).trans (P.trans (c B).symm)))).toAdd +
    (χ (FundamentalGroup.fromPath ((c B).trans (Q.trans (c C).symm)))).toAdd
  rw [h]
  change (χ (FundamentalGroup.fromPath ((c B).trans (Q.trans (c C).symm)) *
    FundamentalGroup.fromPath ((c A).trans (P.trans (c B).symm)))).toAdd = _
  rw [map_mul, toAdd_mul, add_comm]

theorem vacuumPathLightParity_symm (a : BulkCoefficients) (v : Sphere3)
    {A B : vacuum a} (p : Path A B) :
    vacuumPathLightParity a v p.symm = vacuumPathLightParity a v p := by
  have h := vacuumPathLightParity_homotopic a v (Path.Homotopic.trans_symm p)
  rw [vacuumPathLightParity_trans, vacuumPathLightParity_refl] at h
  exact (eq_neg_of_add_eq_zero_right h).trans (ZMod.neg_eq_self_mod_two _)

theorem vacuumPathLightParity_cast (a : BulkCoefficients) (v : Sphere3)
    {A B A' B' : vacuum a} (p : Path A B) (hA : A' = A) (hB : B' = B) :
    vacuumPathLightParity a v (p.cast hA hB) = vacuumPathLightParity a v p := by
  subst A' B'
  rw [Path.cast_rfl_rfl]

/-- The endpoint-independent character of the circle is one exactly for the light free classes. -/
theorem vacuumPathLightParity_nativeCircleLoop (a : BulkCoefficients) (v : Sphere3)
    (b : C(NativeCircle, vacuum a)) :
    vacuumPathLightParity a v (nativeCircleLoop b) =
      if nativeVacuumCircleCost a b = kappaStar a then 1 else 0 := by
  have h := nativeVacuumCircleCost_eq_conjugated_oriented_path a b v
    (pathFromVacuumRoot a v (b nativeCircleLoopBase)) false
  change nativeVacuumCircleCost a b = kappaStar a *
    (quaternionSplittingWeight (vacuumPathWord a v (nativeCircleLoop b)) : ℝ) at h
  rw [vacuumPathLightParity, quaternionLightCharacter_eq_indicator, h]
  let g := vacuumPathWord a v (nativeCircleLoop b)
  have hClass : kappaStar a * (quaternionSplittingWeight g : ℝ) = kappaStar a ↔
      IsLightQuaternion g := by
    have hK := kappaStar_pos a
    by_cases hLight : IsLightQuaternion g
    · have hn : g ≠ 1 := by
        intro he
        subst g
        exact (by decide : ¬ IsLightQuaternion (1 : QuaternionGroup 2)) (he ▸ hLight)
      simp only [hLight, quaternionSplittingWeight, if_neg hn, if_true, Nat.cast_one, mul_one]
    · by_cases hId : g = 1
      · have hn : ¬ IsLightQuaternion (1 : QuaternionGroup 2) := by decide
        simp only [quaternionSplittingWeight, hId, if_true, Nat.cast_zero, mul_zero, hK.ne,
          hn]
      · simp only [quaternionSplittingWeight, if_neg hId, hLight, if_false, Nat.cast_ofNat, iff_false]
        linarith only [hK]
  change (if IsLightQuaternion g then (1 : ZMod 2) else 0) =
    if kappaStar a * (quaternionSplittingWeight g : ℝ) = kappaStar a then 1 else 0
  simp only [hClass]

theorem vacuumPathLightParity_nativeCircleLoop_homotopic (a : BulkCoefficients) (v : Sphere3)
    {b c : C(NativeCircle, vacuum a)} (h : b.Homotopic c) :
    vacuumPathLightParity a v (nativeCircleLoop b) =
      vacuumPathLightParity a v (nativeCircleLoop c) := by
  rw [vacuumPathLightParity_nativeCircleLoop, vacuumPathLightParity_nativeCircleLoop,
    nativeVacuumCircleCost_homotopic a h]

/-- A free homotopy of loop paths preserves the light character even when the basepoint moves. -/
theorem vacuumPathLightParity_of_periodic_square (a : BulkCoefficients) (v : Sphere3)
    {A B : vacuum a} (p : Path A A) (q : Path B B)
    (F : C(unitInterval × unitInterval, vacuum a))
    (h₀ : ∀ t, F (0,t) = p t) (h₁ : ∀ t, F (1,t) = q t)
    (hLoop : ∀ s, F (s,0) = F (s,1)) :
    vacuumPathLightParity a v p = vacuumPathLightParity a v q := by
  obtain ⟨b,hb,hp⟩ := exists_nativeCircleLoop_descent p
  obtain ⟨c,hc,hq⟩ := exists_nativeCircleLoop_descent q
  have hpb : vacuumPathLightParity a v (nativeCircleLoop b) = vacuumPathLightParity a v p := by
    rw [← vacuumPathLightParity_cast a v (nativeCircleLoop b) hb hb, hp]
  have hqc : vacuumPathLightParity a v (nativeCircleLoop c) = vacuumPathLightParity a v q := by
    rw [← vacuumPathLightParity_cast a v (nativeCircleLoop c) hc hc, hq]
  have h : b.Homotopic c := nativeCircle_homotopic_of_periodic_square F
    (fun t => (h₀ t).trans ((congrArg (fun z : Path A A => z t) hp).symm))
    (fun t => (h₁ t).trans ((congrArg (fun z : Path B B => z t) hq).symm)) hLoop
  rw [← hpb, ← hqc]
  exact vacuumPathLightParity_nativeCircleLoop_homotopic a v h

theorem vacuumPathLightParity_subpath_add (a : BulkCoefficients) (v : Sphere3)
    {A B : vacuum a} (p : Path A B) (t₀ t₁ t₂ : unitInterval) :
    vacuumPathLightParity a v (p.subpath t₀ t₁) + vacuumPathLightParity a v (p.subpath t₁ t₂) =
      vacuumPathLightParity a v (p.subpath t₀ t₂) := by
  rw [← vacuumPathLightParity_trans]
  exact vacuumPathLightParity_homotopic a v ⟨Path.Homotopy.subpathTransSubpath p _ _ _⟩

end Thesis
