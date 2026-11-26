module

public import Thesis.Foundation.QuaternionFrameMetric
public import Thesis.Variational.VacuumExtension
import Thesis.Interpolation.RegularizedSphereProjection
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! Smooth local inverses of the actual vacuum covering in ambient coordinates. -/

public section

noncomputable section

open Filter Metric Set Topology
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius Quaternion

namespace Thesis

private def tensorQuaternionCover (a : BulkCoefficients) (v : QuaternionCoordinates) : Tensor :=
  (ambientQuaternionCover a v : Tensor)

private theorem contDiff_tensorQuaternionCover (a : BulkCoefficients) :
    ContDiff ℝ ∞ (tensorQuaternionCover a) :=
  symmetricTraceless.subtypeL.contDiff.comp (contDiff_ambientQuaternionCover a)

private def augmentedQuaternionCover (a : BulkCoefficients) (v : QuaternionCoordinates) : Tensor × ℝ :=
  (tensorQuaternionCover a v, ‖v‖ ^ 2)

private theorem contDiff_augmentedQuaternionCover (a : BulkCoefficients) :
    ContDiff ℝ ∞ (augmentedQuaternionCover a) :=
  (contDiff_tensorQuaternionCover a).prodMk (contDiff_norm_sq (𝕜 := ℝ))

private theorem exists_unitQuaternion_curve_of_tangent (p : Sphere3) (z : QuaternionCoordinates)
    (hTan : ⟪p.val, z⟫_ℝ = 0) : ∃ v : ℝ → Sphere3,
    v 0 = p ∧ HasDerivAt (fun t => (v t).val) z 0 := by
  let X : ℝ → QuaternionCoordinates := (fun _ => p.val) + fun t => t • z
  have hX : HasDerivAt X z 0 := by
    have hz : HasDerivAt (fun t : ℝ => t • z) z 0 := by
      simpa only [id_eq, one_smul] using (hasDerivAt_id (0 : ℝ)).smul_const z
    simpa only [zero_add] using (hasDerivAt_const (0 : ℝ) p.val).add hz
  have hp : ‖p.val‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using p.property
  have hX₀ : X 0 = p.val := by simp [X]
  have hp₀ : p.val ≠ 0 := by intro h; rw [h, norm_zero] at hp; exact zero_ne_one hp
  let P := regularizedSphereDirection (0 : QuaternionCoordinates) 0
  have hP0 (x : QuaternionCoordinates) (hx : x ≠ 0) : ‖P x‖ = 1 := by
    change ‖regularizedSphereDirection 0 0 x‖ = 1
    rw [regularizedSphereDirection_zero]
    exact norm_shiftedSphereDirection hx
  let v (t : ℝ) : Sphere3 :=
    if h : X t ≠ 0 then ⟨P (X t), by rw [mem_sphere, dist_zero_right, hP0 _ h]⟩ else p
  have hPp : P p.val = p.val := by
    change regularizedSphereDirection 0 0 p.val = p.val
    rw [regularizedSphereDirection_zero, shiftedSphereDirection, sub_zero, hp, inv_one, one_smul]
  have hv₀ : v 0 = p := by
    have h0 : X 0 ≠ 0 := by rw [hX₀]; exact hp₀
    unfold v
    rw [dif_pos h0]
    apply Subtype.ext
    change P (X 0) = p.val
    rw [hX₀, hPp]
  have hDiff := (contDiffAt_regularizedSphereDirection (δ := 0) (Or.inl hp₀)).differentiableAt
    (by simp)
  have hDP : fderiv ℝ P p.val z = z := by
    change fderiv ℝ (regularizedSphereDirection 0 0) p.val z = z
    rw [fderiv_regularizedSphereDirection_apply (Or.inl hp₀), sub_zero, hTan]
    have hs : regularizedSphereRadius 0 0 p.val = 1 := by simp [regularizedSphereRadius, hp]
    simp only [hs, inv_one, one_smul, zero_div, zero_smul, sub_zero]
  have hD : HasDerivAt (P ∘ X) z 0 := by
    have hComp := (show DifferentiableAt ℝ P (X 0) from hX₀.symm ▸ hDiff).hasFDerivAt.comp_hasDerivAt 0 hX
    rwa [hX₀, hDP] at hComp
  have hNe : ∀ᶠ t in 𝓝 0, X t ≠ 0 := by
    have h0 : X 0 ≠ 0 := by rw [hX₀]; exact hp₀
    exact hX.continuousAt.preimage_mem_nhds (isOpen_ne.mem_nhds h0)
  refine ⟨v, hv₀, hD.congr_of_eventuallyEq ?_⟩
  filter_upwards [hNe] with t ht
  simp only [v, dif_pos ht, Function.comp_apply]

private theorem fderiv_augmentedQuaternionCover_injective (a : BulkCoefficients) (p : Sphere3) :
    Function.Injective (fderiv ℝ (augmentedQuaternionCover a) p.val) := by
  let P := tensorQuaternionCover a
  have hP : ContDiff ℝ ∞ P := contDiff_tensorQuaternionCover a
  have hProd : fderiv ℝ (augmentedQuaternionCover a) p.val =
      (fderiv ℝ P p.val).prod (2 • innerSL ℝ p.val) :=
    (((hP.differentiable (by simp) p.val).hasFDerivAt).prodMk
      (hasStrictFDerivAt_norm_sq p.val).hasFDerivAt).fderiv
  have hZero (z : QuaternionCoordinates)
      (hz : fderiv ℝ (augmentedQuaternionCover a) p.val z = 0) : z = 0 := by
    rw [hProd] at hz
    have hzP : fderiv ℝ P p.val z = 0 := congrArg Prod.fst hz
    have hzN : (2 : ℝ) * ⟪p.val, z⟫_ℝ = 0 := by
      simpa only [ContinuousLinearMap.prod_apply, Prod.snd_zero, smul_apply,
        innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat] using congrArg Prod.snd hz
    have hTan : ⟪p.val, z⟫_ℝ = 0 := (mul_eq_zero.mp hzN).resolve_left (by norm_num)
    obtain ⟨v, hv₀, hv'⟩ := exists_unitQuaternion_curve_of_tangent p z hTan
    let e := Quaternion.linearIsometryEquivTuple.symm
    have hq : HasDerivAt (fun t => e (v t).val) (e z) 0 :=
      e.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt 0 hv'
    have hD : HasDerivAt (fun t => (cover a (v t) : Tensor)) 0 0 := by
      have hD' := ((hP.differentiable (by simp) (v 0).val).hasFDerivAt).comp_hasDerivAt 0 hv'
      have he : (fun t => (cover a (v t) : Tensor)) = P ∘ fun t => (v t).val := by
        funext t
        simp only [cover, tensorQuaternionCover, ambientQuaternionCover, P, Function.comp_apply]
      rw [he]
      rw [hv₀] at hD'
      change HasDerivAt (P ∘ fun t => (v t).val) (fderiv ℝ P p.val z) 0 at hD'
      rwa [hzP] at hD'
    have hM := cover_curve_metric_ge a v hq
    have hA : 0 < 4 * vacuumRadius a ^ 2 := by positivity [vacuumRadius_pos a]
    have hEnergy : 4 * vacuumRadius a ^ 2 * ‖z‖ ^ 2 ≤ 0 := by
      calc
        _ = 4 * vacuumRadius a ^ 2 * ‖e z‖ ^ 2 := by rw [e.norm_map]
        _ ≤ (1 / 2 : ℝ) * ‖deriv (fun t => (cover a (v t) : Tensor)) 0‖ ^ 2 := hM
        _ = 0 := (congrArg (fun w : Tensor => (1 / 2 : ℝ) * ‖w‖ ^ 2) hD.deriv).trans (by norm_num)
    have hs : ‖z‖ ^ 2 ≤ 0 := nonpos_of_mul_nonpos_right hEnergy hA
    exact norm_eq_zero.1 (by nlinarith [norm_nonneg z])
  intro z w h
  apply sub_eq_zero.1
  apply hZero
  rw [map_sub, h, sub_self]

/-- A smooth ambient inverse recovers all nearby lifts in the same sheet. -/
theorem exists_local_smooth_inverse_quaternionCover (a : BulkCoefficients) (p : Sphere3) :
    ∃ (U : Set Sphere3) (I : Tensor → QuaternionCoordinates),
      IsOpen U ∧ p ∈ U ∧ ContDiffAt ℝ ∞ I (cover a p : Tensor) ∧
      ∀ v ∈ U, I (cover a v : Tensor) = v.val := by
  let F := augmentedQuaternionCover a
  let D := fderiv ℝ F p.val
  have hD : Function.Injective D := fderiv_augmentedQuaternionCover_injective a p
  obtain ⟨A, hA⟩ := D.toLinearMap.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hD)
  let L := A.toContinuousLinearMap
  let G := L ∘ F
  have hG : ContDiff ℝ ∞ G := L.contDiff.comp (contDiff_augmentedQuaternionCover a)
  let I := ContinuousLinearEquiv.refl ℝ QuaternionCoordinates
  have hG' : HasFDerivAt G (I : QuaternionCoordinates →L[ℝ] QuaternionCoordinates) p.val := by
    have hDer := L.hasFDerivAt.comp p.val
      (((contDiff_augmentedQuaternionCover a).differentiable (by simp) p.val).hasFDerivAt)
    have hComp : L.comp D = (I : QuaternionCoordinates →L[ℝ] QuaternionCoordinates) := by
      apply ContinuousLinearMap.ext
      intro z
      change A (D z) = z
      exact DFunLike.congr_fun hA z
    change HasFDerivAt G (L.comp D) p.val at hDer
    rwa [hComp] at hDer
  let e := hG.contDiffAt.toOpenPartialHomeomorph G hG' (by simp)
  have hpE : p.val ∈ e.source := hG.contDiffAt.mem_toOpenPartialHomeomorph_source hG' (by simp)
  have hInverse : ContDiffAt ℝ ∞ e.symm (G p.val) := hG.contDiffAt.to_localInverse hG' (by simp)
  let Z (Q : Tensor) := L (Q, 1)
  have hZ : ContDiff ℝ ∞ Z := L.contDiff.comp (contDiff_id.prodMk contDiff_const)
  have hVal (v : Sphere3) : Z (cover a v : Tensor) = G v.val := by
    have hv : ‖v.val‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using v.property
    simp only [Z, G, F, augmentedQuaternionCover, tensorQuaternionCover, cover,
      ambientQuaternionCover, Function.comp_apply, hv, one_pow]
  refine ⟨Subtype.val ⁻¹' e.source, e.symm ∘ Z, e.open_source.preimage continuous_subtype_val, hpE, ?_, ?_⟩
  · rw [← hVal p] at hInverse
    exact hInverse.comp _ hZ.contDiffAt
  · intro v hv
    change e.symm (Z (cover a v : Tensor)) = v.val
    rw [hVal v]
    exact e.left_inv hv

/-- Continuous lifts of smooth vacuum fields inherit smoothness on the same set. -/
theorem contDiffOn_quaternionLift_of_contDiffOn_cover (a : BulkCoefficients)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {U : Set E}
    {v : E → Sphere3} (hv : ContinuousOn v U)
    (hQ : ContDiffOn ℝ ∞ (fun x => (cover a (v x) : Tensor)) U) :
    ContDiffOn ℝ ∞ (fun x => (v x).val) U := by
  intro x hx
  obtain ⟨V, I, hV, hxV, hI, hEq⟩ := exists_local_smooth_inverse_quaternionCover a (v x)
  have hEv : ∀ᶠ y in 𝓝[U] x, v y ∈ V := (hv x hx).eventually (hV.mem_nhds hxV)
  have hC := hI.comp_contDiffWithinAt x (hQ x hx)
  exact hC.congr_of_eventuallyEq (hEv.mono fun y hy => (hEq (v y) hy).symm)
    ((hEq (v x) hxV).symm)

/-- In every source direction the Frobenius derivative controls the same
derivative of the quaternion lift. -/
theorem fderiv_quaternionLift_sq_le (a : BulkCoefficients)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {U : Set E} (hU : IsOpen U)
    {v : E → Sphere3} (hv : ContinuousOn v U)
    (hQ : ContDiffOn ℝ ∞ (fun x => (cover a (v x) : Tensor)) U)
    {x : E} (hx : x ∈ U) (z : E) :
    8 * vacuumRadius a ^ 2 * ‖fderiv ℝ (fun y => (v y).val) x z‖ ^ 2 ≤
      ‖fderiv ℝ (fun y => (cover a (v y) : Tensor)) x z‖ ^ 2 := by
  let F := fun y => (v y).val
  let Q := fun y => (cover a (v y) : Tensor)
  let C : ℝ → E := (fun _ => x) + fun s => s • z
  have hC : HasDerivAt C z 0 := by
    have hz : HasDerivAt (fun t : ℝ => t • z) z 0 := by
      simpa only [id_eq, one_smul] using (hasDerivAt_id (0 : ℝ)).smul_const z
    simpa only [zero_add] using (hasDerivAt_const (0 : ℝ) x).add hz
  have hC₀ : C 0 = x := by simp [C]
  let w := v ∘ C
  let e := Quaternion.linearIsometryEquivTuple.symm
  have hF : HasFDerivAt F (fderiv ℝ F (C 0)) (C 0) := by
    rw [hC₀]
    apply DifferentiableAt.hasFDerivAt
    exact (((contDiffOn_quaternionLift_of_contDiffOn_cover a hv hQ) x hx).contDiffAt
      (hU.mem_nhds hx)).differentiableAt (by simp)
  have hCurve := hF.comp_hasDerivAt 0 hC
  have hQ' : HasFDerivAt Q (fderiv ℝ Q (C 0)) (C 0) := by
    rw [hC₀]
    exact (((hQ x hx).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt
  have hQCurve := hQ'.comp_hasDerivAt 0 hC
  rw [hC₀] at hCurve hQCurve
  have hq : HasDerivAt (fun t => e (w t).val) (e (fderiv ℝ F x z)) 0 :=
    e.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt 0 hCurve
  have hM := cover_curve_metric_ge a w hq
  have hOut : (1 / 2 : ℝ) * ‖deriv (fun t => (cover a (w t) : Tensor)) 0‖ ^ 2 =
      (1 / 2 : ℝ) * ‖fderiv ℝ Q x z‖ ^ 2 :=
    congrArg (fun B : Tensor => (1 / 2 : ℝ) * ‖B‖ ^ 2) hQCurve.deriv
  have hIn : 4 * vacuumRadius a ^ 2 * ‖fderiv ℝ F x z‖ ^ 2 ≤
      (1 / 2 : ℝ) * ‖fderiv ℝ Q x z‖ ^ 2 := by
    rw [← e.norm_map (fderiv ℝ F x z), ← hOut]
    exact hM
  linarith only [hIn]

end Thesis
