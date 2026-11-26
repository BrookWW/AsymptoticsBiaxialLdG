module

public import Thesis.Definitions
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.InnerProductSpace.Laplacian

/-! The actual second derivative chain rule and Laplacian trace in a frame. -/

public section

noncomputable section

open Filter Function Set Topology
open scoped ContDiff RealInnerProductSpace

namespace Thesis

/-- The coordinate derivative of a displayed Fréchet column agrees with the
bilinear Hessian when the field is (C^2) near the point. -/
theorem fderiv_fderiv_column_eq_iteratedFDeriv_two
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {x : E} (hf : ContDiffAt ℝ 2 f x) (v w : E) :
    fderiv ℝ (fun y => fderiv ℝ f y w) x v = iteratedFDeriv ℝ 2 f x ![v,w] := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  rw [iteratedFDeriv_two_apply,fderiv_clm_apply hd (differentiableAt_const _)]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,fderiv_const_apply,ContinuousLinearMap.comp_zero,
    zero_add,ContinuousLinearMap.flip_apply]

/-- The actual bilinear Hessian of a composition. -/
theorem iteratedFDeriv_two_comp_apply_of_contDiffAt
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : F → G} {g : E → F} {x : E} (hf : ContDiffAt ℝ 2 f (g x)) (hg : ContDiffAt ℝ 2 g x)
    (v w : E) :
    iteratedFDeriv ℝ 2 (f ∘ g) x ![v,w] =
      iteratedFDeriv ℝ 2 f (g x) ![fderiv ℝ g x v, fderiv ℝ g x w] +
      fderiv ℝ f (g x) (iteratedFDeriv ℝ 2 g x ![v,w]) := by
  let A (y : E) := fderiv ℝ f (g y)
  let B := fderiv ℝ g
  have hgC : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 2 g y := hg.eventually (by norm_num)
  have hfC : ∀ᶠ z in 𝓝 (g x), ContDiffAt ℝ 2 f z := hf.eventually (by norm_num)
  have hfAt : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 2 f (g y) := hg.continuousAt hfC
  have hNear : fderiv ℝ (f ∘ g) =ᶠ[𝓝 x] fun y => (A y).comp (B y) := by
    filter_upwards [hfAt,hgC] with y hy hz
    exact fderiv_comp y (hy.differentiableAt two_ne_zero) (hz.differentiableAt two_ne_zero)
  have hA : HasFDerivAt A ((fderiv ℝ (fderiv ℝ f) (g x)).comp (fderiv ℝ g x)) x :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).hasFDerivAt.comp x
      (hg.differentiableAt two_ne_zero).hasFDerivAt
  have hB : HasFDerivAt B (fderiv ℝ (fderiv ℝ g) x) x :=
    ((hg.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).hasFDerivAt
  have hC := (hA.clm_comp hB).congr_of_eventuallyEq hNear
  simp only [iteratedFDeriv_two_apply,Matrix.cons_val_zero,Matrix.cons_val_one]
  rw [hC.fderiv]
  change fderiv ℝ f (g x) (fderiv ℝ (fderiv ℝ g) x v w) +
    (fderiv ℝ (fderiv ℝ f) (g x) (fderiv ℝ g x v)) (fderiv ℝ g x w) = _
  exact add_comm _ _

/-- The source coordinate Laplacian is the trace of the Hessian in any
orthonormal frame. -/
theorem laplacian_eq_second_derivative_basis_of_contDiffAt
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : Point → F} {x : Point} (hf : ContDiffAt ℝ 2 f x)
    (B : OrthonormalBasis (Fin 3) ℝ Point) :
    laplacian f x = ∑ i : Fin 3, iteratedFDeriv ℝ 2 f x ![B i, B i] := by
  have hStd : laplacian f x = Laplacian.laplacian f x := by
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f (EuclideanSpace.basisFun (Fin 3) ℝ)]
    unfold laplacian
    apply Finset.sum_congr rfl
    intro i _
    rw [EuclideanSpace.basisFun_apply]
    exact fderiv_fderiv_column_eq_iteratedFDeriv_two hf (axis i) (axis i)
  rw [hStd,InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f B]

end Thesis
