module

public import Thesis.Variational.DirichletPoissonInverse
public import Thesis.Variational.EulerLagrange
import Thesis.Variational.H10StrongApproximation
import Thesis.Variational.WeakZeroTraceGraph

/-! Actual Sobolev fields solving the pure weak Dirichlet equation. -/

public section

noncomputable section

open Filter MeasureTheory Set Topology
open scoped BigOperators ContDiff ENNReal Matrix.Norms.Frobenius RealInnerProductSpace

namespace Thesis

local instance dirichletPoissonWeakContinuousENorm : ContinuousENorm S0 :=
  @SeminormedAddGroup.toContinuousENorm S0 inferInstance

theorem isWeakPoisson_of_H10_pairing {U : Set Point}
    (hU : IsOpen U) [IsFiniteMeasure (volume.restrict U)]
    {u : H10 U} {f : Point → S0} (hf : MemLp f 2 (volume.restrict U))
    (hEq : ∀ v : H10 U,
      (∫ x in U, -(∑ j, frobeniusS0 (h10Gradient u x j) (h10Gradient v x j))) =
        ∫ x in U, frobeniusS0 (f x) (h10Value v x)) :
    IsWeakPoisson U (h10Gradient u) (fun x => (f x : Tensor)) := by
  have hSource := IntegrableOn.locallyIntegrableOn
    (symmetricTraceless.subtypeL.integrable_comp (hf.integrable (by norm_num)))
  refine ⟨hSource,?_⟩
  intro i j φ hφ
  let A : S0 := traceFreeSymmetricPart (Matrix.single i j 1)
  have hEntry (B : S0) : frobeniusS0 B A = (B : Tensor) i j := by
    change frobenius B (traceFreeSymmetricPart (Matrix.single i j 1)) = _
    rw [frobenius_comm,frobenius_traceFreeSymmetricPart,frobenius_eq_sum]
    simp [Matrix.single_apply,ite_and,ite_mul]
  have hScaledEntry (B : S0) (s : ℝ) : frobeniusS0 B (s • A) = s * (B : Tensor) i j := by
    rw [← frobeniusCoordinateEquiv_inner,map_smul,real_inner_smul_right,frobeniusCoordinateEquiv_inner,hEntry]
  let ψ (x : Point) := φ x • A
  have hD (x : Point) (k : Fin 3) : ClassicalGradient ψ x k = coordDeriv k φ x • A :=
    DFunLike.congr_fun (((hφ.1.differentiable (by simp) x).hasFDerivAt.smul_const A).fderiv) (axis k)
  have hZero : HasZeroTrace U ψ (ClassicalGradient ψ) :=
    hasZeroTrace_of_contDiff_hasCompactSupport hU (hφ.1.smul contDiff_const)
      (hφ.2.1.smul_right (f' := fun _ : Point => A))
      ((tsupport_smul_subset_left φ (fun _ : Point => A)).trans hφ.2.2)
  obtain ⟨v,hV,hG⟩ := hZero.exists_H10_with_ae_data hU
  have hLeft :
      (fun x => -(∑ k, frobeniusS0 (h10Gradient u x k) (h10Gradient v x k))) =ᵐ[volume.restrict U]
      fun x => -(∑ k, coordDeriv k φ x * (h10Gradient u x k : Tensor) i j) := by
    filter_upwards [hG] with x hx
    rw [hx]
    congr 1
    exact Finset.sum_congr rfl fun k _ => by rw [hD,hScaledEntry]
  have hRight : (fun x => frobeniusS0 (f x) (h10Value v x)) =ᵐ[volume.restrict U]
      fun x => φ x * (f x : Tensor) i j := by
    filter_upwards [hV] with x hx
    rw [hx]
    exact hScaledEntry (f x) (φ x)
  let L : S0 →L[ℝ] ℝ :=
    ({ toFun := fun B : S0 => (B : Tensor) i j
       map_add' := fun _ _ => rfl
       map_smul' := fun _ _ => rfl } : S0 →ₗ[ℝ] ℝ).toContinuousLinearMap
  have hInt (k : Fin 3) :
      IntegrableOn (fun x => coordDeriv k φ x * (h10Gradient u x k : Tensor) i j) U volume := by
    have hGrad : Integrable (fun x => h10Gradient u x k) (volume.restrict U) :=
      (Lp.memLp (u.val.2 k)).integrable (by norm_num)
    have hLoc : LocallyIntegrableOn (fun x => (h10Gradient u x k : Tensor) i j) U volume :=
      IntegrableOn.locallyIntegrableOn (L.integrable_comp hGrad)
    simpa only [smul_eq_mul] using
      ((hφ.coordDeriv k).integrable_smul hLoc).integrableOn (s := U)
  have hL (k : Fin 3) : (∫ x in U, coordDeriv k φ x * (h10Gradient u x k : Tensor) i j) =
      ∫ x, coordDeriv k φ x * (h10Gradient u x k : Tensor) i j := by
    simpa only [smul_eq_mul] using
      (hφ.coordDeriv k).setIntegral_smul_eq_integral (fun x => (h10Gradient u x k : Tensor) i j)
  have hR : (∫ x in U, φ x * (f x : Tensor) i j) = ∫ x, φ x * (f x : Tensor) i j := by
    simpa only [smul_eq_mul] using hφ.setIntegral_smul_eq_integral (fun x => (f x : Tensor) i j)
  have h := hEq v
  rw [integral_congr_ae hLeft,integral_congr_ae hRight,integral_neg,
    integral_finsetSum _ (fun k _ => hInt k),hR] at h
  simp_rw [hL] at h
  linarith only [h]

/-- The intrinsic zero-trace problem with square-integrable force admits an
actual Sobolev field with its own distributional columns. -/
theorem exists_zeroTrace_weakDirichletPoisson_of_memLp {U : Set Point}
    (hU : IsOpen U) (hB : Bornology.IsBounded U) {f : Point → S0}
    (hf : MemLp f 2 (volume.restrict U)) :
    ∃ v : H10 U, HasZeroTrace U (h10Value v) (h10Gradient v) ∧
      IsWeakPoisson U (h10Gradient v) (fun x => (f x : Tensor)) := by
  letI : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.mpr hB.measure_lt_top.ne
  obtain ⟨v,hv,_⟩ := exists_unique_H10_dirichletPoisson_of_memLp hU.measurableSet hB hf
  exact ⟨v,H10.hasZeroTrace hU v,isWeakPoisson_of_H10_pairing hU hf hv⟩

end Thesis
