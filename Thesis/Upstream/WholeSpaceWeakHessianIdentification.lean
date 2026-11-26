module

public import Thesis.Upstream.WholeSpaceWeakHessianOperator
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-! Identification of the whole-space operator with actual distributional columns. -/

public section

noncomputable section

open Filter Function MeasureTheory Set
open scoped BigOperators ContDiff ENNReal RealInnerProductSpace

namespace Thesis

local instance wholeSpaceHessianFactTwo : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

private theorem compactSmoothScalarDeriv_val (i : Fin 3) (f : CompactSmoothScalar) :
    (compactSmoothScalarDeriv i f).val = coordDeriv i f.val := by
  unfold compactSmoothScalarDeriv
  rfl

private theorem compactSmooth_mixedDeriv_comm (f : CompactSmoothScalar) (i j : Fin 3) :
    compactSmoothScalarDeriv i (compactSmoothScalarDeriv j f) =
      compactSmoothScalarDeriv j (compactSmoothScalarDeriv i f) := by
  apply Subtype.ext
  simp only [compactSmoothScalarDeriv_val]
  funext x
  have hf₂ : ContDiffAt ℝ 2 f.val x := f.property.1.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
  have hd := (hf₂.fderiv_right_succ (n := 1)).differentiableAt one_ne_zero
  have h (k : Fin 3) : fderiv ℝ (coordDeriv k f.val) x =
      (ContinuousLinearMap.apply ℝ ℝ (axis k)).comp (fderiv ℝ (fderiv ℝ f.val) x) :=
    ((ContinuousLinearMap.apply ℝ ℝ (axis k)).hasFDerivAt.comp x hd.hasFDerivAt).fderiv
  change (fderiv ℝ (coordDeriv j f.val) x) (axis i) = (fderiv ℝ (coordDeriv i f.val) x) (axis j)
  rw [h,h]
  exact hf₂.isSymmSndFDerivAt (by rw [minSmoothness_of_isRCLikeNormedField]) (axis i) (axis j)

private theorem compactSmooth_laplace_deriv_comm (f : CompactSmoothScalar) (i : Fin 3) :
    compactSmoothScalarDeriv i (compactSmoothScalarLaplace f) =
      compactSmoothScalarLaplace (compactSmoothScalarDeriv i f) := by
  simp only [compactSmoothScalarLaplace,LinearMap.sum_apply,LinearMap.comp_apply,map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [compactSmooth_mixedDeriv_comm (compactSmoothScalarDeriv j f) i j,compactSmooth_mixedDeriv_comm f i j]

theorem compactSmooth_laplace_hess_comm (f : CompactSmoothScalar) (i j : Fin 3) :
    compactSmoothScalarHess i j (compactSmoothScalarLaplace f) =
      compactSmoothScalarLaplace (compactSmoothScalarHess i j f) := by
  simp only [compactSmoothScalarHess,LinearMap.comp_apply,compactSmooth_laplace_deriv_comm]

private theorem compactSmooth_integral_deriv_parts (f g : CompactSmoothScalar) (i : Fin 3) :
    (∫ x, f.val x*(compactSmoothScalarDeriv i g).val x) =
      -(∫ x, (compactSmoothScalarDeriv i f).val x*g.val x) := by
  rw [compactSmoothScalarDeriv_val,compactSmoothScalarDeriv_val]
  have hF := (compactSmoothScalarDeriv i f).property
  have hG := (compactSmoothScalarDeriv i g).property
  rw [compactSmoothScalarDeriv_val] at hF hG
  apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
  · exact (hF.1.continuous.mul g.property.1.continuous).integrable_of_hasCompactSupport hF.2.mul_right
  · exact (f.property.1.continuous.mul hG.1.continuous).integrable_of_hasCompactSupport f.property.2.mul_right
  · exact (f.property.1.continuous.mul g.property.1.continuous).integrable_of_hasCompactSupport f.property.2.mul_right
  · exact fun x _ => f.property.1.differentiable (by simp) x
  · exact fun x _ => g.property.1.differentiable (by simp) x

theorem compactSmooth_integral_hess_parts (f g : CompactSmoothScalar) (i j : Fin 3) :
    (∫ x, f.val x*(compactSmoothScalarHess i j g).val x) =
      ∫ x, (compactSmoothScalarHess i j f).val x*g.val x := by
  change (∫ x, f.val x*(compactSmoothScalarDeriv j (compactSmoothScalarDeriv i g)).val x) =
    ∫ x, (compactSmoothScalarDeriv j (compactSmoothScalarDeriv i f)).val x*g.val x
  rw [compactSmooth_integral_deriv_parts f (compactSmoothScalarDeriv i g) j,
    compactSmooth_integral_deriv_parts (compactSmoothScalarDeriv j f) g i,neg_neg,
    compactSmooth_mixedDeriv_comm f i j]

private theorem integral_compactSmooth_laplace_mul (f g : CompactSmoothScalar) :
    (∫ x, (compactSmoothScalarLaplace f).val x*g.val x) =
      ∫ x, f.val x*(compactSmoothScalarLaplace g).val x := by
  have hsum (u : CompactSmoothScalar) :
      (compactSmoothScalarLaplace u).val = fun x => ∑ i : Fin 3, (compactSmoothScalarHess i i u).val x := by
    rw [compactSmoothScalarLaplace_val]
    funext x
    simp only [compactSmoothScalarHess_val,laplacian,SupportingAnalysis.scalarHessian,coordDeriv]
    rfl
  have hI (i : Fin 3) : Integrable
      (fun x => (compactSmoothScalarHess i i f).val x*g.val x) volume :=
    ((compactSmoothScalarHess i i f).property.1.continuous.mul g.property.1.continuous
      ).integrable_of_hasCompactSupport (compactSmoothScalarHess i i f).property.2.mul_right
  have hJ (i : Fin 3) : Integrable
      (fun x => f.val x*(compactSmoothScalarHess i i g).val x) volume :=
    (f.property.1.continuous.mul (compactSmoothScalarHess i i g).property.1.continuous
      ).integrable_of_hasCompactSupport f.property.2.mul_right
  simp_rw [hsum,Finset.sum_mul,Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => hI i),integral_finsetSum _ (fun i _ => hJ i)]
  exact Finset.sum_congr rfl (fun i _ => (compactSmooth_integral_hess_parts f g i i).symm)

/-- The actual distributional second weak columns against compact smooth tests. -/
@[expose] def IsWeakScalarHessian (u : Point → ℝ)
    (H : Fin 3 → Fin 3 → Point → ℝ) : Prop :=
  ∀ i j : Fin 3, ∀ φ : CompactSmoothScalar,
    (∫ x, H i j x*φ.val x) = ∫ x, u x*(compactSmoothScalarHess i j φ).val x

theorem IsWeakScalarHessian.of_first_pairings {u : Point → ℝ}
    {D : Fin 3 → Point → ℝ} {H : Fin 3 → Fin 3 → Point → ℝ}
    (hD : ∀ i (φ : CompactSmoothScalar),
      (∫ x, D i x*φ.val x) = -(∫ x, u x*(compactSmoothScalarDeriv i φ).val x))
    (hH : ∀ i j (φ : CompactSmoothScalar),
      (∫ x, H i j x*φ.val x) = -(∫ x, D i x*(compactSmoothScalarDeriv j φ).val x)) :
    IsWeakScalarHessian u H := by
  intro i j φ
  rw [hH i j φ,hD i (compactSmoothScalarDeriv j φ),neg_neg,compactSmooth_mixedDeriv_comm φ i j]
  rfl

/-- Sum of the displayed diagonal second weak derivatives. -/
@[expose] def scalarWeakHessianTrace (H : Fin 3 → Fin 3 → Point → ℝ) : Point → ℝ :=
  fun x => ∑ i : Fin 3, H i i x

private theorem inner_Lp_compactSmoothScalarToLp (f : Lp ℝ 2 (volume : Measure Point))
    (g : CompactSmoothScalar) :
    inner ℝ f (compactSmoothScalarToLp 2 g) = ∫ x, f x*g.val x := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [compactSmoothScalarToLp_ae 2 g] with x hx
  rw [hx]
  exact Real.inner_apply _ _

private theorem inner_compactSmoothScalarToLp_pair (f g : CompactSmoothScalar) :
    inner ℝ (compactSmoothScalarToLp 2 f) (compactSmoothScalarToLp 2 g) =
      ∫ x, f.val x*g.val x := by
  rw [inner_Lp_compactSmoothScalarToLp]
  apply integral_congr_ae
  filter_upwards [compactSmoothScalarToLp_ae 2 f] with x hx
  rw [hx]

private theorem weakHessian_test_identity {u : Point → ℝ}
    {H : Fin 3 → Fin 3 → Point → ℝ} (hH : IsWeakScalarHessian u H)
    (hu : MemLp u 2 (volume : Measure Point))
    (hL : ∀ i j, MemLp (H i j) 2 (volume : Measure Point))
    (i j : Fin 3) (φ : CompactSmoothScalar) :
    (∫ x, H i j x*(compactSmoothScalarLaplace φ).val x) =
      ∫ x, scalarWeakHessianTrace H x*(compactSmoothScalarHess i j φ).val x := by
  rw [hH i j (compactSmoothScalarLaplace φ),compactSmooth_laplace_hess_comm]
  let ψ := compactSmoothScalarHess i j φ
  have hSum : (compactSmoothScalarLaplace ψ).val =
      fun x => ∑ k : Fin 3, (compactSmoothScalarHess k k ψ).val x := by
    rw [compactSmoothScalarLaplace_val]
    funext x
    simp only [laplacian,compactSmoothScalarHess_val,SupportingAnalysis.scalarHessian,coordDeriv]
    rfl
  have hI (k : Fin 3) : Integrable (fun x => H k k x*ψ.val x) volume := by
    have hψ : MemLp ψ.val 2 (volume : Measure Point) :=
      ψ.property.1.continuous.memLp_of_hasCompactSupport ψ.property.2
    exact (hL k k).integrable_mul hψ
  have hJ (k : Fin 3) : Integrable (fun x => u x*(compactSmoothScalarHess k k ψ).val x) volume := by
    have hψ : MemLp (compactSmoothScalarHess k k ψ).val 2 (volume : Measure Point) :=
      (compactSmoothScalarHess k k ψ).property.1.continuous.memLp_of_hasCompactSupport
        (compactSmoothScalarHess k k ψ).property.2
    exact hu.integrable_mul hψ
  change (∫ x, u x*(compactSmoothScalarLaplace ψ).val x) =
    ∫ x, scalarWeakHessianTrace H x*ψ.val x
  simp_rw [hSum,scalarWeakHessianTrace,Finset.mul_sum,Finset.sum_mul]
  rw [integral_finsetSum _ (fun k _ => hJ k),integral_finsetSum _ (fun k _ => hI k)]
  exact Finset.sum_congr rfl (fun k _ => (hH k k ψ).symm)

/-- The extension on (L^2) agrees almost everywhere with any displayed
second weak column of a field with the displayed Laplacian. -/
theorem wholeSpace_laplacianHessianOperator_ae_eq_of_weak {u f : Point → ℝ}
    {H : Fin 3 → Fin 3 → Point → ℝ}
    (hu : MemLp u 2 (volume : Measure Point)) (hf : MemLp f 2 volume)
    (hH : IsWeakScalarHessian u H) (hL : ∀ i j, MemLp (H i j) 2 volume)
    (hF : f =ᵐ[volume] scalarWeakHessianTrace H) (i j : Fin 3)
    (T : Lp ℝ 2 volume →L[ℝ] Lp ℝ 2 volume)
    (hT : ∀ φ : CompactSmoothScalar,
      T (compactSmoothScalarToLp 2 (compactSmoothScalarLaplace φ)) =
        compactSmoothScalarToLp 2 (compactSmoothScalarHess i j φ)) :
    (T (hf.toLp f) : Point → ℝ) =ᵐ[volume] H i j := by
  let L := (compactSmoothScalarToLp (2 : ℝ≥0∞)).comp compactSmoothScalarLaplace
  letI : Fact (1 ≤ ((2 : ℕ) : ℝ≥0∞)) := ⟨by norm_num⟩
  have hDense : DenseRange L := by
    simpa only [Nat.cast_ofNat] using denseRange_compactSmoothScalarLaplace 2 (by decide)
  have hPair (ψ : CompactSmoothScalar) (z : Lp ℝ 2 (volume : Measure Point)) :
      inner ℝ (T z) (L ψ) = inner ℝ z (compactSmoothScalarToLp 2 (compactSmoothScalarHess i j ψ)) := by
    have hClosed : IsClosed {w : Lp ℝ 2 (volume : Measure Point) |
        inner ℝ (T w) (L ψ) = inner ℝ w (compactSmoothScalarToLp 2 (compactSmoothScalarHess i j ψ))} :=
      isClosed_eq (by fun_prop) (by fun_prop)
    refine isClosed_property hDense hClosed (fun φ => ?_) z
    change inner ℝ (T (compactSmoothScalarToLp 2 (compactSmoothScalarLaplace φ)))
      (compactSmoothScalarToLp 2 (compactSmoothScalarLaplace ψ)) =
      inner ℝ (compactSmoothScalarToLp 2 (compactSmoothScalarLaplace φ))
        (compactSmoothScalarToLp 2 (compactSmoothScalarHess i j ψ))
    rw [hT,inner_compactSmoothScalarToLp_pair,inner_compactSmoothScalarToLp_pair]
    rw [← compactSmooth_integral_hess_parts φ (compactSmoothScalarLaplace ψ) i j,
      compactSmooth_laplace_hess_comm,integral_compactSmooth_laplace_mul]
  let h := (hL i j).toLp (H i j)
  have hEq : T (hf.toLp f) = h := by
    apply ext_inner_right ℝ
    intro z
    refine isClosed_property hDense (isClosed_eq (by fun_prop) (by fun_prop)) (fun φ => ?_) z
    rw [hPair]
    change inner ℝ (hf.toLp f) (compactSmoothScalarToLp 2 (compactSmoothScalarHess i j φ)) =
      inner ℝ h (compactSmoothScalarToLp 2 (compactSmoothScalarLaplace φ))
    rw [inner_Lp_compactSmoothScalarToLp,inner_Lp_compactSmoothScalarToLp]
    have he₁ :
        (fun x => hf.toLp f x*(compactSmoothScalarHess i j φ).val x) =ᵐ[volume]
          fun x => scalarWeakHessianTrace H x*(compactSmoothScalarHess i j φ).val x :=
      (hf.coeFn_toLp.trans hF).mono fun x hx => congrArg (fun s => s*(compactSmoothScalarHess i j φ).val x) hx
    have he₂ :
        (fun x => h x*(compactSmoothScalarLaplace φ).val x) =ᵐ[volume]
          fun x => H i j x*(compactSmoothScalarLaplace φ).val x :=
      (hL i j).coeFn_toLp.mono fun x hx => congrArg (fun s => s*(compactSmoothScalarLaplace φ).val x) hx
    rw [integral_congr_ae he₁,integral_congr_ae he₂]
    exact (weakHessian_test_identity hH hu hL i j φ).symm
  rw [hEq]
  exact (hL i j).coeFn_toLp

end Thesis
