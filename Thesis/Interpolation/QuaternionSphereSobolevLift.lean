module

public import Thesis.Foundation.QuaternionCoverSmoothLift
public import Thesis.Foundation.VacuumFundamentalGroup
public import Thesis.Interpolation.SmoothRadialSphereGradient
public import Thesis.Interpolation.QuaternionAmbientCollar
import Mathlib.Analysis.Normed.Module.Normalize

/-! Quantitative smooth lifting of vacuum-valued two-sphere data. -/

@[expose] public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set StratificationTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace Thesis

/-- Direction from the center, with the chosen unit value at the center. -/
def sphereRadialDirection {n : ℕ} (base : UnitBoundarySphere n) (x : Domain n) : UnitBoundarySphere n :=
  if hx : x ≠ 0 then
    ⟨NormedSpace.normalize x, by rw [mem_sphere_zero_iff_norm, NormedSpace.norm_normalize hx]⟩
  else base

theorem sphereRadialDirection_smul {n : ℕ} (base : UnitBoundarySphere n) {r : ℝ} (hr : 0 < r)
    (x : Domain n) : sphereRadialDirection base (r • x) = sphereRadialDirection base x := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [sphereRadialDirection, dif_pos (smul_ne_zero hr.ne' hx), sphereRadialDirection, dif_pos hx]
    exact Subtype.ext (NormedSpace.normalize_smul_of_pos hr x)

@[simp] theorem sphereRadialDirection_unit {n : ℕ} (base θ : UnitBoundarySphere n) :
    sphereRadialDirection base θ.val = θ := by
  have hNorm := mem_sphere_zero_iff_norm.1 θ.property
  have hθ : θ.val ≠ 0 := by intro hz; rw [hz, norm_zero] at hNorm; exact zero_ne_one hNorm
  rw [sphereRadialDirection, dif_pos hθ]
  apply Subtype.ext
  change ‖θ.val‖⁻¹ • θ.val = θ.val
  rw [hNorm, inv_one, one_smul]

theorem continuousOn_sphereRadialDirection {n : ℕ} (base : UnitBoundarySphere n) :
    ContinuousOn (sphereRadialDirection base) ({0}ᶜ : Set (Domain n)) := by
  rw [continuousOn_iff_continuous_restrict]
  apply Continuous.subtype_mk
  change Continuous (fun x : ({0}ᶜ : Set (Domain n)) => (sphereRadialDirection base x.val).val)
  have heq : (fun x : ({0}ᶜ : Set (Domain n)) => (sphereRadialDirection base x.val).val) =
      fun x : ({0}ᶜ : Set (Domain n)) => ‖x.val‖⁻¹ • x.val := by
    funext x
    rw [sphereRadialDirection, dif_pos (show x.val ≠ 0 from x.property)]
    rfl
  rw [heq]
  exact ((continuous_subtype_val.norm).inv₀ (fun x => norm_ne_zero_iff.2 x.property)).smul continuous_subtype_val

def vacuumSphereGradientEnergy {n : ℕ} (hn : 2 ≤ n) {a : BulkCoefficients}
    (Q : UnitBoundarySphere n → vacuum a)
    (hQ : MemSphereW12 hn (fun θ => frobeniusCoordinateEquiv (Q θ).val)) : ℝ :=
  ∫ θ : UnitBoundarySphere n, ∑ i : Fin n,
    ‖(sphereGradient hn (fun θ => frobeniusCoordinateEquiv (Q θ).val) hQ i) θ‖ ^ 2
      ∂unitBoundarySurface n

/-- A smooth two-sphere vacuum field has a quaternion Sobolev lift whose
native tangential energy is controlled by that of the original trace. -/
theorem exists_quaternionSobolevLift_of_smooth_vacuumSphere (a : BulkCoefficients)
    (base : UnitBoundarySphere 3) (Q : C(UnitBoundarySphere 3, vacuum a))
    (hQ : ContDiffOn ℝ ∞ (fun x : Domain 3 => (Q (sphereRadialDirection base x)).val)
      ({0}ᶜ : Set (Domain 3))) :
    ∃ (v : C(UnitBoundarySphere 3, Sphere3))
      (hv : MemSphereW12 (by decide : 2 ≤ 3) (fun θ => (v θ).val))
      (hV : MemSphereW12 (by decide : 2 ≤ 3) (fun θ => frobeniusCoordinateEquiv (Q θ).val)),
      (∀ θ, cover a (v θ) = (Q θ).val) ∧
      8 * vacuumRadius a ^ 2 * quaternionBoundaryEnergy (by decide : 2 ≤ 3) (fun θ => (v θ).val) hv ≤
        vacuumSphereGradientEnergy (by decide : 2 ≤ 3) Q hV := by
  obtain ⟨v₀, hv₀⟩ := vacuumQuaternionProjection_surjective a (Q base)
  obtain ⟨v, ⟨_, hCover⟩, _⟩ := vacuumSphere_existsUnique_continuous_lift a (by decide : 2 ≤ 2) Q base v₀ hv₀
  have hCover' (θ : UnitBoundarySphere 3) : cover a (v θ) = (Q θ).val := by
    rw [← vacuumQuaternionProjection_val, hCover]
  let U := ({0}ᶜ : Set (Domain 3))
  let V (x : Domain 3) := v (sphereRadialDirection base x)
  let A (x : Domain 3) := (Q (sphereRadialDirection base x)).val
  let W (x : Domain 3) := frobeniusCoordinateEquiv (A x)
  let V₄ (x : Domain 3) := (V x).val
  have hVcont : ContinuousOn V U := v.continuous.comp_continuousOn (continuousOn_sphereRadialDirection base)
  have hA : ContDiffOn ℝ ∞ A U := hQ
  have hVTens : (fun x => (cover a (V x) : Tensor)) = fun x => (A x : Tensor) :=
    funext fun x => congrArg (fun z : S0 => (z : Tensor)) (hCover' _)
  have hVQ : ContDiffOn ℝ ∞ (fun x => (cover a (V x) : Tensor)) U := by
    rw [hVTens]
    exact symmetricTraceless.subtypeL.contDiff.comp_contDiffOn hA
  have hV₄ : ContDiffOn ℝ ∞ V₄ U := contDiffOn_quaternionLift_of_contDiffOn_cover a hVcont hVQ
  have hW : ContDiffOn ℝ ∞ W U := frobeniusCoordinateEquiv.toContinuousLinearMap.contDiff.comp_contDiffOn hA
  have hVray (r : ℝ) (hr : 0 < r) (x : Domain 3) : V₄ (r • x) = V₄ x := by
    dsimp only [V₄, V]
    rw [sphereRadialDirection_smul base hr]
  have hWray (r : ℝ) (hr : 0 < r) (x : Domain 3) : W (r • x) = W x := by
    dsimp only [W, A]
    rw [sphereRadialDirection_smul base hr]
  obtain ⟨hv, hvGrad⟩ := exists_memSphereW12_of_smooth_degreeZero (by decide : 2 ≤ 3) hV₄ hVray
  obtain ⟨hWb, hWGrad⟩ := exists_memSphereW12_of_smooth_degreeZero (by decide : 2 ≤ 3) hW hWray
  have heqV : (fun θ : UnitBoundarySphere 3 => V₄ θ.val) = fun θ => (v θ).val := by
    funext θ
    simp only [V₄, V, sphereRadialDirection_unit]
  have heqW : (fun θ : UnitBoundarySphere 3 => W θ.val) = fun θ => frobeniusCoordinateEquiv (Q θ).val := by
    funext θ
    simp only [W, A, sphereRadialDirection_unit]
  revert hvGrad hv hWGrad hWb
  rw [heqV, heqW]
  intro hv hvGrad hWb hWGrad
  refine ⟨v, hv, hWb, hCover', ?_⟩
  have hI {q : ℕ} {z : UnitBoundarySphere 3 → Ambient q} (hz : MemSphereW12 (by decide : 2 ≤ 3) z) :
      Integrable (fun θ => ∑ i : Fin 3, ‖(sphereGradient (by decide : 2 ≤ 3) z hz i) θ‖ ^ 2)
        (unitBoundarySurface 3) := integrable_finsetSum Finset.univ fun i _ =>
      (Lp.memLp (sphereGradient (by decide : 2 ≤ 3) z hz i)).integrable_norm_pow (by norm_num)
  unfold quaternionBoundaryEnergy vacuumSphereGradientEnergy
  rw [← integral_const_mul]
  apply integral_mono_ae ((hI hv).const_mul _) (hI hWb)
  have hAllV := ae_all_iff.2 hvGrad
  have hAllW := ae_all_iff.2 hWGrad
  filter_upwards [hAllV, hAllW] with θ hθv hθw
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [hθv i, hθw i]
  have hxU : θ.val ∈ U := by
    have hNorm : ‖θ.val‖ = 1 := mem_sphere_zero_iff_norm.1 θ.property
    intro h0
    rw [show θ.val = 0 from h0, norm_zero] at hNorm
    exact zero_ne_one hNorm
  have hA' := ((hA _ hxU).contDiffAt (isOpen_compl_singleton.mem_nhds hxU)).differentiableAt (by simp)
  have hLeft := fderiv_quaternionLift_sq_le a isOpen_compl_singleton hVcont hVQ hxU (EuclideanSpace.single i 1)
  rw [hVTens] at hLeft
  have hTens := (symmetricTraceless.subtypeL.hasFDerivAt.comp θ.val hA'.hasFDerivAt).fderiv
  have hFrob := (frobeniusCoordinateEquiv.toContinuousLinearMap.hasFDerivAt.comp θ.val hA'.hasFDerivAt).fderiv
  change fderiv ℝ (fun x => (A x : Tensor)) θ.val = _ at hTens
  change fderiv ℝ W θ.val = _ at hFrob
  rw [hTens] at hLeft
  rw [hFrob, ContinuousLinearMap.comp_apply]
  change 8 * vacuumRadius a ^ 2 * ‖fderiv ℝ V₄ θ.val (EuclideanSpace.single i 1)‖ ^ 2 ≤
    ‖frobeniusCoordinateEquiv (fderiv ℝ A θ.val (EuclideanSpace.single i 1))‖ ^ 2
  rw [LinearIsometryEquiv.norm_map]
  change 8 * vacuumRadius a ^ 2 * ‖fderiv ℝ V₄ θ.val (EuclideanSpace.single i 1)‖ ^ 2 ≤
    ‖(fderiv ℝ A θ.val (EuclideanSpace.single i 1) : Tensor)‖ ^ 2 at hLeft
  exact hLeft

end Thesis
