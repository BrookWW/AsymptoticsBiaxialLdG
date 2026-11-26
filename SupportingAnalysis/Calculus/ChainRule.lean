module

public import Mathlib

/-! Second derivatives of compositions along curves and affine slices. -/

@[expose] public section

open Filter
open scoped ContDiff Topology

set_option autoImplicit false

namespace SupportingAnalysis

section

variable {X E F : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem deriv_deriv_comp_curve_of_contDiffAt {u : E → F} {c : ℝ → E} {t : ℝ}
    (hu : ContDiffAt ℝ 2 u (c t)) (hc : ContDiffAt ℝ 2 c t) :
    deriv (deriv (u ∘ c)) t =
      fderiv ℝ (fderiv ℝ u) (c t) (deriv c t) (deriv c t) +
        fderiv ℝ u (c t) (deriv (deriv c) t) := by
  have huD : DifferentiableAt ℝ (fderiv ℝ u) (c t) :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hcD : DifferentiableAt ℝ (fderiv ℝ c) t :=
    (hc.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hcu : HasDerivAt (fderiv ℝ u ∘ c)
      (fderiv ℝ (fderiv ℝ u) (c t) (deriv c t)) t :=
    huD.hasFDerivAt.comp_hasDerivAt t
      (hc.differentiableAt (by norm_num : (2 : ℕ∞ω) ≠ 0)).hasFDerivAt.hasDerivAt
  have hv : DifferentiableAt ℝ (deriv c) t := by
    let L : (ℝ →L[ℝ] E) →L[ℝ] E := ContinuousLinearMap.apply ℝ E 1
    exact L.differentiableAt.comp t hcD
  have hlocal : deriv (u ∘ c) =ᶠ[𝓝 t]
      (fun s => fderiv ℝ u (c s) (deriv c s)) := by
    have huv := hc.continuousAt.tendsto.eventually (hu.eventually (by simp))
    filter_upwards [hc.eventually (by simp), huv] with s hcs hus
    exact ((hus.differentiableAt (by norm_num : (2 : ℕ∞ω) ≠ 0)).hasFDerivAt.comp_hasDerivAt s
      (hcs.differentiableAt (by norm_num : (2 : ℕ∞ω) ≠ 0)).hasFDerivAt.hasDerivAt).deriv
  exact ((hcu.clm_apply hv.hasDerivAt).congr_of_eventuallyEq hlocal).deriv

theorem fderiv_fderiv_comp_affine_of_contDiffAt (T : X →L[ℝ] E) (q : E) (a x v w : X)
    {u : E → F} (hu : ContDiffAt ℝ 2 u (q + T (x - a))) :
    fderiv ℝ (fderiv ℝ (fun p => u (q + T (p - a)))) x v w =
      fderiv ℝ (fderiv ℝ u) (q + T (x - a)) (T v) (T w) := by
  let g : X → E := fun p => q + T (p - a)
  have hg (p : X) : HasFDerivAt g T p := by
    have hp : HasFDerivAt (fun z : X => z - a) (ContinuousLinearMap.id ℝ X) p :=
      (hasFDerivAt_id p).sub_const a
    simpa only [g, Function.comp_apply, ContinuousLinearMap.comp_id] using
      (T.hasFDerivAt.comp p hp).const_add q
  have huu : DifferentiableAt ℝ (fderiv ℝ u) (g x) :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  let C : (E →L[ℝ] F) →L[ℝ] X →L[ℝ] F := ContinuousLinearMap.compL ℝ X E F |>.flip T
  have hD : HasFDerivAt (fun p => (fderiv ℝ u (g p)).comp T)
      (C.comp ((fderiv ℝ (fderiv ℝ u) (g x)).comp T)) x :=
    C.hasFDerivAt.comp x (huu.hasFDerivAt.comp x (hg x))
  have heq : fderiv ℝ (u ∘ g) =ᶠ[𝓝 x] fun p => (fderiv ℝ u (g p)).comp T := by
    filter_upwards [(hg x).continuousAt.tendsto.eventually (hu.eventually (by simp))]
      with p hp
    exact ((hp.differentiableAt (by norm_num : (2 : ℕ∞ω) ≠ 0)).hasFDerivAt.comp p (hg p)).fderiv
  change (fderiv ℝ (fderiv ℝ (u ∘ g)) x) v w = _
  rw [(hD.congr_of_eventuallyEq heq).fderiv]
  rfl

end

end SupportingAnalysis
