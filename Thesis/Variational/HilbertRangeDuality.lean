module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Module.HahnBanach

/-! A Hilbert-space range estimate from the adjoint pairing. -/

public section

open ContinuousLinearMap
open scoped RealInnerProductSpace

set_option autoImplicit false
noncomputable section

namespace Thesis

theorem exists_norm_le_of_adjoint_pairing
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (i : E →L[ℝ] F) (u : F) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ f : F, |⟪u, f⟫| ≤ C * ‖i.adjoint f‖) :
    ∃ v : E, i v = u ∧ ‖v‖ ≤ C := by
  let A := i.adjoint.toLinearMap
  obtain ⟨r,hr⟩ := A.rangeRestrict.exists_rightInverse_of_surjective A.range_rangeRestrict
  let L : A.range →ₗ[ℝ] ℝ := (innerSL ℝ u).toLinearMap.comp r
  have hr' (z : A.range) : i.adjoint (r z) = (z : E) :=
    congrArg Subtype.val (LinearMap.congr_fun hr z)
  have hL (z : A.range) : ‖L z‖ ≤ C * ‖z‖ := by
    change ‖⟪u, r z⟫‖ ≤ C * ‖z‖
    rw [Real.norm_eq_abs]
    exact (h (r z)).trans_eq (congrArg (fun w : E => C * ‖w‖) (hr' z))
  let L' : A.range →L[ℝ] ℝ := L.mkContinuous C hL
  obtain ⟨G,hG,hNorm⟩ := exists_extension_norm_eq A.range L'
  let v := (InnerProductSpace.toDual ℝ E).symm G
  have hν : ‖v‖ ≤ C := by
    rw [show ‖v‖ = ‖G‖ from (InnerProductSpace.toDual ℝ E).symm.norm_map G, hNorm]
    exact L.mkContinuous_norm_le hC hL
  refine ⟨v,?_,hν⟩
  have hInner (f : F) : ⟪i v,f⟫ = ⟪u,f⟫ := by
    let z : A.range := ⟨i.adjoint f, LinearMap.mem_range_self A f⟩
    have hA : i.adjoint (r z - f) = 0 := by rw [map_sub, hr' z]; exact sub_self _
    have hD := h (r z - f)
    rw [hA, norm_zero, mul_zero, abs_nonpos_iff, inner_sub_right] at hD
    calc
      _ = ⟪v,i.adjoint f⟫ := (i.adjoint_inner_right v f).symm
      _ = G z := InnerProductSpace.toDual_symm_apply
      _ = L' z := hG z
      _ = ⟪u,r z⟫ := rfl
      _ = _ := sub_eq_zero.mp hD
  have hZero : ⟪i v - u,i v - u⟫ = 0 := by
    rw [inner_sub_left, hInner, sub_self]
  exact sub_eq_zero.mp (inner_self_eq_zero.mp hZero)

end Thesis

end
