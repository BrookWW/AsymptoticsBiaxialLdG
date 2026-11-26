module

public import Thesis.Upstream.WholeSpaceLaplacianTestDensity
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-! Continuous whole-space Hessian operators on the actual scalar forcing spaces. -/

public section

noncomputable section

open Filter Function MeasureTheory Set
open scoped BigOperators ContDiff ENNReal NNReal Topology

namespace Thesis

/-- The vector space of scalar smooth tests of compact support. -/
@[expose] def CompactSmoothScalar : Submodule ℝ (Point → ℝ) where
  carrier := {φ | ContDiff ℝ ∞ φ ∧ HasCompactSupport φ}
  zero_mem' := ⟨contDiff_const,HasCompactSupport.zero⟩
  add_mem' hφ hψ := ⟨hφ.1.add hψ.1,hφ.2.add hψ.2⟩
  smul_mem' c _ hφ := ⟨hφ.1.const_smul c,hφ.2.smul_left⟩

/-- A derivative along a fixed coordinate preserves the compact test space. -/
@[expose] def compactSmoothScalarDeriv (i : Fin 3) : CompactSmoothScalar →ₗ[ℝ] CompactSmoothScalar where
  toFun φ := ⟨coordDeriv i φ.val,
    (ContinuousLinearMap.apply ℝ ℝ (axis i)).contDiff.comp (φ.property.1.fderiv_right (by simp)),
    φ.property.2.fderiv_apply ℝ (axis i)⟩
  map_add' φ ψ := by
    apply Subtype.ext
    funext x
    change fderiv ℝ (φ.val+ψ.val) x (axis i) =
      fderiv ℝ φ.val x (axis i)+fderiv ℝ ψ.val x (axis i)
    rw [fderiv_add (φ.property.1.differentiable (by simp) x)
      (ψ.property.1.differentiable (by simp) x),add_apply]
  map_smul' c φ := by
    apply Subtype.ext
    funext x
    change fderiv ℝ (c • φ.val) x (axis i) = c • fderiv ℝ φ.val x (axis i)
    rw [fderiv_const_smul (φ.property.1.differentiable (by simp) x),smul_apply]

/-- The scalar Laplacian sends compact smooth tests to compact smooth tests. -/
@[expose] def compactSmoothScalarLaplace : CompactSmoothScalar →ₗ[ℝ] CompactSmoothScalar :=
  ∑ j : Fin 3, (compactSmoothScalarDeriv j).comp (compactSmoothScalarDeriv j)

/-- The coordinate Hessian sends compact smooth tests to compact smooth tests. -/
@[expose] def compactSmoothScalarHess (i j : Fin 3) : CompactSmoothScalar →ₗ[ℝ] CompactSmoothScalar :=
  (compactSmoothScalarDeriv j).comp (compactSmoothScalarDeriv i)

theorem compactSmoothScalarLaplace_val (u : CompactSmoothScalar) :
    (compactSmoothScalarLaplace u).val = laplacian u.val := by
  funext x
  simp only [compactSmoothScalarLaplace,LinearMap.sum_apply,LinearMap.comp_apply,
    Submodule.coe_sum,Finset.sum_apply,laplacian]
  rfl

theorem compactSmoothScalarHess_val (i j : Fin 3) (u : CompactSmoothScalar) :
    (compactSmoothScalarHess i j u).val = fun x => SupportingAnalysis.scalarHessian u.val x i j := by
  unfold compactSmoothScalarHess compactSmoothScalarDeriv SupportingAnalysis.scalarHessian
  rfl

private theorem compactSmoothScalar_memLp (p : ℝ≥0∞) (f : CompactSmoothScalar) :
    MemLp f.val p (volume : Measure Point) :=
  f.property.1.continuous.memLp_of_hasCompactSupport f.property.2

/-- The actual pointwise representative of a compact smooth test in (L^p). -/
def compactSmoothScalarToLp (p : ℝ≥0∞) : CompactSmoothScalar →ₗ[ℝ] Lp ℝ p (volume : Measure Point) where
  toFun f := (compactSmoothScalar_memLp p f).toLp f.val
  map_add' f g := by
    have h := MemLp.toLp_add (compactSmoothScalar_memLp p f) (compactSmoothScalar_memLp p g)
    exact h
  map_smul' c f := by
    exact MemLp.toLp_const_smul c (compactSmoothScalar_memLp p f)

theorem compactSmoothScalarToLp_ae (p : ℝ≥0∞) (f : CompactSmoothScalar) :
    ((compactSmoothScalarToLp p f : Lp ℝ p volume) : Point → ℝ) =ᵐ[volume] f.val :=
  (compactSmoothScalar_memLp p f).coeFn_toLp

theorem norm_compactSmoothScalarToLp (p : ℝ≥0∞) (f : CompactSmoothScalar) :
    ‖compactSmoothScalarToLp p f‖ = (eLpNorm f.val p volume).toReal :=
  Lp.norm_toLp f.val (compactSmoothScalar_memLp p f)

theorem denseRange_compactSmoothScalarLaplace (m : ℕ)
    [Fact (1 ≤ (m : ℝ≥0∞))] (hm : 1 < m) :
    DenseRange ((compactSmoothScalarToLp (m : ℝ≥0∞)).comp compactSmoothScalarLaplace) := by
  let p : ℝ≥0∞ := m
  let L := (compactSmoothScalarToLp p).comp compactSmoothScalarLaplace
  have hSmooth : Dense {f : Lp ℝ p (volume : Measure Point) |
      ∃ g : Point → ℝ, f =ᵐ[volume] g ∧ HasCompactSupport g ∧ ContDiff ℝ ∞ g} :=
    Lp.dense_hasCompactSupport_contDiff (ENNReal.natCast_ne_top m)
  have hInto : {f : Lp ℝ p (volume : Measure Point) |
      ∃ g : Point → ℝ, f =ᵐ[volume] g ∧ HasCompactSupport g ∧ ContDiff ℝ ∞ g} ⊆ closure (range L) := by
    rintro f ⟨g,hfg,hgc,hg⟩
    obtain ⟨φ,hφ,hLim⟩ := exists_compactSmooth_laplacian_test_approximation hg hgc
    let x (n : ℕ) : CompactSmoothScalar := ⟨φ n,hφ n⟩
    have hT : Tendsto (fun n => L (x n)) atTop (𝓝 f) := by
      apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).2
      refine (hLim m hm).congr (fun n => ?_)
      apply eLpNorm_congr_ae
      have hA := compactSmoothScalarToLp_ae p (compactSmoothScalarLaplace (x n))
      exact ((hA.trans (EventuallyEq.of_eq (compactSmoothScalarLaplace_val (x n)))).sub hfg).symm
    exact mem_closure_of_tendsto hT (Eventually.of_forall fun n => mem_range_self (x n))
  intro f
  exact closure_minimal hInto isClosed_closure (hSmooth f)

private theorem exists_compactSmooth_hessianLp_control (m : ℕ) (hm : 1 < m) :
    ∃ C : ℝ, 0 < C ∧ ∀ i j : Fin 3, ∀ f : CompactSmoothScalar,
      ‖compactSmoothScalarToLp (m : ℝ≥0∞) (compactSmoothScalarHess i j f)‖ ≤
        C*‖compactSmoothScalarToLp (m : ℝ≥0∞) (compactSmoothScalarLaplace f)‖ := by
  have hm' : 1 < (m : ℝ) := by exact_mod_cast hm
  obtain ⟨C,hC,hBound⟩ := exists_wholeSpace_coordinatePoissonHessianLp (m : ℝ) hm'
  refine ⟨C,hC,fun i j f => ?_⟩
  have h := hBound f.val f.property.1 f.property.2 i j
  rw [ENNReal.ofReal_natCast] at h
  let p : ℝ≥0∞ := m
  have hI := (compactSmoothScalar_memLp p (compactSmoothScalarLaplace f)).eLpNorm_ne_top
  rw [norm_compactSmoothScalarToLp,norm_compactSmoothScalarToLp,compactSmoothScalarLaplace_val,
    compactSmoothScalarHess_val]
  rw [compactSmoothScalarLaplace_val] at hI
  have hz := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hI) h
  simpa only [ENNReal.toReal_mul,ENNReal.toReal_ofReal hC.le] using hz

/-- The coordinate Hessian is a bounded operator of the actual Laplacian
in each integer (L^p) space. The operator is exact on the dense space
of compact smooth Laplace data. -/
theorem exists_wholeSpace_laplacianHessianOperator (m : ℕ)
    [Fact (1 ≤ (m : ℝ≥0∞))] (hm : 1 < m) :
    ∃ C : ℝ, 0 < C ∧ ∀ i j : Fin 3,
      ∃ T : Lp ℝ (m : ℝ≥0∞) (volume : Measure Point) →L[ℝ] Lp ℝ (m : ℝ≥0∞) volume,
        ‖T‖ ≤ C ∧ ∀ f : CompactSmoothScalar,
          T (compactSmoothScalarToLp (m : ℝ≥0∞) (compactSmoothScalarLaplace f)) =
            compactSmoothScalarToLp (m : ℝ≥0∞) (compactSmoothScalarHess i j f) := by
  let p : ℝ≥0∞ := m
  let X := Lp ℝ p (volume : Measure Point)
  let L := (compactSmoothScalarToLp p).comp compactSmoothScalarLaplace
  have hDenseL : DenseRange L := denseRange_compactSmoothScalarLaplace m hm
  obtain ⟨C,hC,hCtrl⟩ := exists_compactSmooth_hessianLp_control m hm
  refine ⟨C,hC,fun i j => ?_⟩
  let H := (compactSmoothScalarToLp p).comp (compactSmoothScalarHess i j)
  have hN (f : CompactSmoothScalar) : ‖H f‖ ≤ C*‖L f‖ := hCtrl i j f
  have hUnique (f g : CompactSmoothScalar) (h : L f = L g) : H f = H g := by
    have h0 := hN (f-g)
    rw [map_sub,map_sub,h,sub_self,norm_zero,mul_zero,norm_le_zero_iff,sub_eq_zero] at h0
    exact h0
  let S := L.range
  let c (x : S) := Classical.choose x.property
  have hc (x : S) : L (c x) = x.val := Classical.choose_spec x.property
  let A : S →ₗ[ℝ] X :=
    { toFun := fun x => H (c x)
      map_add' := fun x y => by
        rw [← H.map_add]
        apply hUnique
        rw [hc,L.map_add,hc,hc]
        rfl
      map_smul' := fun r x => by
        rw [← H.map_smul]
        apply hUnique
        rw [hc,L.map_smul,hc]
        rfl }
  have hA (x : S) : ‖A x‖ ≤ C*‖x‖ := by
    change ‖H (c x)‖ ≤ C*‖x.val‖
    rw [← hc]
    exact hN _
  let A' := A.mkContinuous C hA
  let e : S →L[ℝ] X := S.subtypeL
  have he : DenseRange e := by
    intro x
    have hRange : range e = range L := by
      ext y
      constructor
      · rintro ⟨z,rfl⟩
        exact z.property
      · intro hy
        exact ⟨⟨y,hy⟩,rfl⟩
    rw [hRange]
    exact hDenseL x
  have he' : IsUniformInducing e := isUniformEmbedding_subtype_val.isUniformInducing
  let T := A'.extend e
  have hOn (f : CompactSmoothScalar) : T (L f) = H f := by
    let z : S := ⟨L f,LinearMap.mem_range_self L f⟩
    change T (e z) = H f
    rw [ContinuousLinearMap.extend_eq A' he he' z]
    exact hUnique _ _ (hc z)
  refine ⟨T,?_ ,hOn⟩
  apply ContinuousLinearMap.opNorm_le_bound _ hC.le
  exact isClosed_property he (isClosed_le (by fun_prop) (by fun_prop)) fun x => by
    rw [ContinuousLinearMap.extend_eq A' he he' x]
    exact hA x

end Thesis
