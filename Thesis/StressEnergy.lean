module

public import Thesis.Model
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
import Mathlib.Tactic.Ring

/-! Row-wise divergence of the stress tensor for the sextic energy. -/

@[expose] public section

open MeasureTheory Set
open scoped BigOperators ContDiff Matrix Matrix.Norms.Frobenius

namespace Thesis

private theorem frobenius_comm (A B : Tensor) : frobenius A B = frobenius B A := by
  unfold frobenius
  rw [← Matrix.trace_transpose (Aᵀ * B), Matrix.transpose_mul, Matrix.transpose_transpose]

private noncomputable def frobeniusForm : Tensor →L[ℝ] Tensor →L[ℝ] ℝ :=
  (LinearMap.mk₂ ℝ frobenius
    (by intros; simp [frobenius, Matrix.add_mul, Matrix.trace_add])
    (by intros; simp [frobenius, Matrix.trace_smul])
    (by intros; simp [frobenius, Matrix.mul_add, Matrix.trace_add])
    (by intros; simp [frobenius, Matrix.trace_smul])).toContinuousBilinearMap

private noncomputable def frobeniusS0Form : S0 →L[ℝ] S0 →L[ℝ] ℝ :=
  frobeniusForm.bilinearComp symmetricTraceless.subtypeL symmetricTraceless.subtypeL

private theorem frobeniusS0_comm (A B : S0) : frobeniusS0 A B = frobeniusS0 B A :=
  frobenius_comm _ _

private theorem differentiableAt_frobeniusS0 {f g : Point → S0} {x : Point}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    DifferentiableAt ℝ (fun y => frobeniusS0 (f y) (g y)) x := by
  change DifferentiableAt ℝ (fun y => (frobeniusS0Form (f y)) (g y)) x
  fun_prop

private noncomputable def traceL : Tensor →L[ℝ] ℝ :=
  (Matrix.traceLinearMap (Fin 3) ℝ ℝ).toContinuousLinearMap

private theorem traceL_apply (A : Tensor) : traceL A = A.trace := rfl

private theorem bulkPotential_differentiableAt (a : BulkCoefficients) (A : S0) :
    DifferentiableAt ℝ (bulkPotential a) A := by
  unfold bulkPotential
  change DifferentiableAt ℝ (fun B : S0 =>
    a.a2 / 2 * preferredTraceSq a - a.a4 / 4 * preferredTraceSq a ^ 2
      - a.a6 / 6 * preferredTraceSq a ^ 3
      - a.a2 / 2 * traceL ((symmetricTraceless.subtypeL B) ^ 2)
      + a.a4 / 4 * traceL ((symmetricTraceless.subtypeL B) ^ 2) ^ 2
      + a.a6 / 6 * traceL ((symmetricTraceless.subtypeL B) ^ 2) ^ 3
      + a.a6' / 6 * traceL ((symmetricTraceless.subtypeL B) ^ 3) ^ 2) A
  fun_prop

/-- The derivative of the sextic potential on the symmetric traceless subspace. -/
theorem fderiv_bulkPotential (a : BulkCoefficients) (A B : S0) :
    fderiv ℝ (bulkPotential a) A B = frobenius (bulkGradient a A) B := by
  let inclusion := symmetricTraceless.subtypeL
  let t : S0 → ℝ := fun X => traceL (inclusion X * inclusion X)
  let s : S0 → ℝ := fun X => traceL (inclusion X * inclusion X * inclusion X)
  have hA := inclusion.hasFDerivAt (x := A)
  have ht := traceL.hasFDerivAt.comp A (hA.mul' hA)
  have hs := traceL.hasFDerivAt.comp A ((hA.mul' hA).mul' hA)
  change HasFDerivAt t _ A at ht
  change HasFDerivAt s _ A at hs
  have hdt : fderiv ℝ t A B = 2 * ((A : Tensor) * (B : Tensor)).trace := by
    rw [ht.fderiv]
    change ((A : Tensor) * (B : Tensor) + (B : Tensor) * (A : Tensor)).trace = _
    rw [Matrix.trace_add, Matrix.trace_mul_comm (B : Tensor) (A : Tensor)]
    ring
  have hds : fderiv ℝ s A B = 3 * ((A : Tensor) * (A : Tensor) * (B : Tensor)).trace := by
    rw [hs.fderiv]
    change (((A : Tensor) * (A : Tensor)) * (B : Tensor)
      + ((A : Tensor) * (B : Tensor) + (B : Tensor) * (A : Tensor)) * (A : Tensor)).trace = _
    have hCycle₁ := Matrix.trace_mul_cycle (A : Tensor) (B : Tensor) (A : Tensor)
    have hCycle₂ : ((B : Tensor) * A * A).trace = ((A : Tensor) * A * B).trace :=
      (Matrix.trace_mul_cycle (B : Tensor) (A : Tensor) (A : Tensor)).trans hCycle₁
    rw [Matrix.add_mul, Matrix.trace_add, Matrix.trace_add, hCycle₁, hCycle₂]
    ring
  let c := a.a2 / 2 * preferredTraceSq a - a.a4 / 4 * preferredTraceSq a ^ 2
    - a.a6 / 6 * preferredTraceSq a ^ 3
  have h := (((hasFDerivAt_const (𝕜 := ℝ) c A).sub
    (ht.differentiableAt.hasFDerivAt.const_mul (a.a2 / 2))).add
      ((ht.differentiableAt.hasFDerivAt.pow 2).const_mul (a.a4 / 4))).add
        ((ht.differentiableAt.hasFDerivAt.pow 3).const_mul (a.a6 / 6))
  have hp := h.add ((hs.differentiableAt.hasFDerivAt.pow 2).const_mul (a.a6' / 6))
  have hpFun : bulkPotential a =
      ((((fun _ : S0 => c) - (fun y => a.a2 / 2 * t y)) + (fun y => a.a4 / 4 * t y ^ 2))
        + (fun y => a.a6 / 6 * t y ^ 3)) + (fun y => a.a6' / 6 * s y ^ 2) := by
    funext X
    simp [bulkPotential, traceL_apply, c, t, s, inclusion, pow_succ, Matrix.mul_assoc]
  have hp' := hp.congr_of_eventuallyEq (Filter.Eventually.of_forall (congrFun hpFun))
  refine (DFunLike.congr_fun hp'.fderiv B).trans ?_
  simp only [add_apply, sub_apply, smul_apply, smul_eq_mul, nsmul_eq_mul,
    Nat.reduceSub, pow_one, Nat.cast_ofNat]
  change (0 : ℝ) - (a.a2 / 2) * (fderiv ℝ t A) B
    + (a.a4 / 4) * (2 * t A * (fderiv ℝ t A) B)
    + (a.a6 / 6) * (3 * t A ^ 2 * (fderiv ℝ t A) B)
    + (a.a6' / 6) * (2 * s A * (fderiv ℝ s A) B) = _
  rw [hdt, hds]
  change _ = (((bulkForce a A : S0) : Tensor)ᵀ * (B : Tensor)).trace
  rw [(bulkForce a A).transpose_eq]
  change _ = (bulkGradient a A * (B : Tensor)).trace
  simp [bulkGradient, t, s, traceL_apply, inclusion, Matrix.add_mul, Matrix.sub_mul,
    Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul, B.trace_eq_zero,
    smul_eq_mul, pow_two, pow_succ _ 2]
  ring

theorem coordDeriv_frobenius {f g : Point → S0} {x : Point}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (i : Fin 3) :
    coordDeriv i (fun y => frobeniusS0 (f y) (g y)) x =
      frobeniusS0 (coordDeriv i f x) (g x) + frobeniusS0 (f x) (coordDeriv i g x) := by
  have h := frobeniusS0Form.hasFDerivAt_of_bilinear hf.hasFDerivAt hg.hasFDerivAt
  change HasFDerivAt (fun y => frobeniusS0 (f y) (g y)) _ x at h
  change (fderiv ℝ (fun y => frobeniusS0 (f y) (g y)) x) (axis i) = _
  rw [h.fderiv]
  simp only [coordDeriv, add_apply, ContinuousLinearMap.precompL_apply,
    ContinuousLinearMap.precompR_apply]
  exact add_comm _ _

private theorem differentiableAt_coordDeriv {Q : Point → S0} {x : Point}
    (hQ : ContDiffAt ℝ 2 Q x) (i : Fin 3) : DifferentiableAt ℝ (coordDeriv i Q) x := by
  let ev := ContinuousLinearMap.apply ℝ S0 (axis i)
  have hEval := ev.differentiableAt (x := fderiv ℝ Q x)
  exact hEval.comp x ((hQ.fderiv_right_succ (n := 1)).differentiableAt one_ne_zero)

theorem coordDeriv_comm {Q : Point → S0} {x : Point}
    (hQ : ContDiffAt ℝ 2 Q x) (i j : Fin 3) :
    coordDeriv i (coordDeriv j Q) x = coordDeriv j (coordDeriv i Q) x := by
  have hD := (hQ.fderiv_right_succ (n := 1)).differentiableAt one_ne_zero
  have h (k : Fin 3) : fderiv ℝ (coordDeriv k Q) x =
      (ContinuousLinearMap.apply ℝ S0 (axis k)).comp (fderiv ℝ (fderiv ℝ Q) x) := by
    let ev := ContinuousLinearMap.apply ℝ S0 (axis k)
    have hEval := ev.hasFDerivAt (x := fderiv ℝ Q x)
    exact (hEval.comp x hD.hasFDerivAt).fderiv
  change (fderiv ℝ (coordDeriv j Q) x) (axis i) = (fderiv ℝ (coordDeriv i Q) x) (axis j)
  rw [h j, h i]
  exact hQ.isSymmSndFDerivAt (by rw [minSmoothness_of_isRCLikeNormedField]) (axis i) (axis j)

private theorem coordDeriv_energyDensity (a : BulkCoefficients) (ε : ElasticScale)
    {Q : Point → S0} {x : Point} (hQ : ContDiffAt ℝ 2 Q x) (i : Fin 3) :
    coordDeriv i (fun y => energyDensity a ε (Q y) (fun j => coordDeriv j Q y)) x =
      (∑ j, frobeniusS0 (coordDeriv i (coordDeriv j Q) x) (coordDeriv j Q x))
        + (ε : ℝ)⁻¹ ^ 2 * frobenius (bulkGradient a (Q x)) (coordDeriv i Q x : S0) := by
  have hD := differentiableAt_coordDeriv hQ
  let g : Fin 3 → Point → ℝ := fun j y => frobeniusS0 (coordDeriv j Q y) (coordDeriv j Q y)
  have hg (j : Fin 3) : DifferentiableAt ℝ (g j) x := by
    exact differentiableAt_frobeniusS0 (hD j) (hD j)
  have hp := (bulkPotential_differentiableAt a (Q x)).hasFDerivAt.comp x
    (hQ.differentiableAt two_ne_zero).hasFDerivAt
  have hsum := HasFDerivAt.fun_sum (u := Finset.univ) (fun j _ => (hg j).hasFDerivAt)
  have h := (hsum.const_mul (1 / 2 : ℝ)).add (hp.const_mul ((ε : ℝ)⁻¹ ^ 2))
  change HasFDerivAt (fun y => energyDensity a ε (Q y) (fun j => coordDeriv j Q y)) _ x at h
  change (fderiv ℝ (fun y => energyDensity a ε (Q y) (fun j => coordDeriv j Q y)) x) (axis i) = _
  rw [h.fderiv]
  simp only [add_apply, smul_apply, sum_apply, ContinuousLinearMap.comp_apply, smul_eq_mul]
  change (1 / 2 : ℝ) * (∑ j, coordDeriv i (g j) x) + (ε : ℝ)⁻¹ ^ 2 *
    (fderiv ℝ (bulkPotential a) (Q x)) (coordDeriv i Q x) = _
  rw [fderiv_bulkPotential]
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  change (1 / 2 : ℝ) * coordDeriv i (fun y =>
    frobeniusS0 (coordDeriv j Q y) (coordDeriv j Q y)) x = _
  rw [coordDeriv_frobenius (hD j) (hD j),
    frobeniusS0_comm (coordDeriv j Q x) (coordDeriv i (coordDeriv j Q) x)]
  ring

/-- The components of `e_ε I - (∂ᵢ Q : ∂ⱼ Q)ᵢⱼ`. -/
noncomputable def stressTensor (a : BulkCoefficients) (ε : ElasticScale)
    (Q : Point → S0) (x : Point) : Tensor := fun i j =>
  (if i = j then energyDensity a ε (Q x) (fun k => coordDeriv k Q x) else 0)
    - frobeniusS0 (coordDeriv i Q x) (coordDeriv j Q x)

/-- The stress–energy identity for a smooth solution of the sextic Euler–Lagrange equation. -/
theorem stressEnergy_rowDivergence_eq_zero_of_pointwise
    (a : BulkCoefficients) (ε : ElasticScale) {Ω : Set Point} (hΩ : IsOpen Ω)
    {Q : Point → S0} (hQ : ContDiffOn ℝ ∞ Q Ω)
    (hEuler : ∀ x ∈ Ω, (ε : ℝ) ^ 2 • (↑(laplacian Q x) : Tensor) = bulkGradient a (Q x)) :
    ∀ x ∈ Ω, ∀ i : Fin 3, ∑ j, coordDeriv j (fun y => stressTensor a ε Q y i j) x = 0 := by
  intro x hx i
  have hxQ : ContDiffAt ℝ 2 Q x :=
    ((hQ x hx).contDiffAt (hΩ.mem_nhds hx)).of_le (WithTop.coe_le_coe.mpr le_top)
  let e : Point → ℝ := fun y => energyDensity a ε (Q y) (fun k => coordDeriv k Q y)
  have hD := differentiableAt_coordDeriv hxQ
  have he : DifferentiableAt ℝ e x := by
    unfold e energyDensity gradientNormSq
    have hP := bulkPotential_differentiableAt a (Q x)
    have hq := hxQ.differentiableAt two_ne_zero
    have hg (j : Fin 3) := differentiableAt_frobeniusS0 (hD j) (hD j)
    fun_prop
  have hs (j : Fin 3) : coordDeriv j (fun y => stressTensor a ε Q y i j) x =
      (if i = j then coordDeriv j e x else 0) -
        (frobeniusS0 (coordDeriv j (coordDeriv i Q) x) (coordDeriv j Q x) +
          frobeniusS0 (coordDeriv i Q x) (coordDeriv j (coordDeriv j Q) x)) := by
    have hf := differentiableAt_frobeniusS0 (hD i) (hD j)
    have hdiag : DifferentiableAt ℝ (fun y => if i = j then e y else 0) x := by
      by_cases hij : i = j <;> simp [hij, he]
    change coordDeriv j (fun y => (if i = j then e y else 0) -
      frobeniusS0 (coordDeriv i Q y) (coordDeriv j Q y)) x = _
    rw [show coordDeriv j (fun y => (if i = j then e y else 0) -
      frobeniusS0 (coordDeriv i Q y) (coordDeriv j Q y)) x =
        coordDeriv j (fun y => if i = j then e y else 0) x -
          coordDeriv j (fun y => frobeniusS0 (coordDeriv i Q y) (coordDeriv j Q y)) x by
        change (fderiv ℝ (fun y => (if i = j then e y else 0) -
          frobeniusS0 (coordDeriv i Q y) (coordDeriv j Q y)) x) (axis j) = _
        rw [fderiv_fun_sub hdiag hf]
        rfl]
    rw [coordDeriv_frobenius (hD i) (hD j)]
    by_cases hij : i = j <;> simp [hij, coordDeriv]
  simp_rw [hs, coordDeriv_comm hxQ _ i]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq,
    if_pos (Finset.mem_univ i)]
  change coordDeriv i (fun y => energyDensity a ε (Q y) (fun k => coordDeriv k Q y)) x - _ = _
  rw [coordDeriv_energyDensity a ε hxQ]
  have hL : ∑ j : Fin 3,
      frobeniusS0 (coordDeriv i Q x) (coordDeriv j (coordDeriv j Q) x) =
      frobeniusS0 (coordDeriv i Q x) (laplacian Q x) := by
    change ∑ j : Fin 3, frobeniusS0Form (coordDeriv i Q x) (coordDeriv j (coordDeriv j Q) x) = _
    rw [← map_sum]
    rfl
  rw [hL, frobeniusS0_comm (coordDeriv i Q x) (laplacian Q x), ← hEuler x hx]
  change _ + (ε : ℝ)⁻¹ ^ 2 *
    frobeniusForm ((ε : ℝ) ^ 2 • (↑(laplacian Q x) : Tensor)) (↑(coordDeriv i Q x) : Tensor) -
      (_ + frobeniusForm (↑(laplacian Q x) : Tensor) (↑(coordDeriv i Q x) : Tensor)) = 0
  rw [map_smul, smul_apply, smul_eq_mul]
  have hε : (ε : ℝ) ≠ 0 := ne_of_gt ε.property.1
  field_simp
  ring

/-- A smooth test function with compact support in the open set. -/
def IsSmoothTest {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Ω : Set Point) (φ : Point → E) : Prop :=
  ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ Ω

/-- Weak Euler–Lagrange equation tested with a scalar test in each tensor entry. -/
def IsWeakEulerLagrange (a : BulkCoefficients) (ε : ElasticScale) (Ω : Set Point)
    (Q : Point → S0) (D : Point → Fin 3 → S0) : Prop :=
  ∀ (i j : Fin 3) (φ : Point → ℝ), IsSmoothTest Ω φ →
    (ε : ℝ) ^ 2 * (∑ k : Fin 3, ∫ x, coordDeriv k φ x * (D x k : Tensor) i j) +
      (∫ x, φ x * bulkGradient a (Q x) i j) = 0

private noncomputable def entryL (i j : Fin 3) : S0 →L[ℝ] ℝ :=
  ({ toFun := fun A : S0 => (A : Tensor) i j
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl } : S0 →ₗ[ℝ] ℝ).toContinuousLinearMap

private theorem coordDeriv_entry (i j k : Fin 3) {v : Point → S0} {x : Point}
    (hv : DifferentiableAt ℝ v x) :
    coordDeriv k (fun y => (v y : Tensor) i j) x = (coordDeriv k v x : S0).val i j := by
  exact DFunLike.congr_fun (((entryL i j).hasFDerivAt (x := v x)).comp x hv.hasFDerivAt).fderiv
    (axis k)

private theorem contDiffOn_coordDeriv {Ω : Set Point} (hΩ : IsOpen Ω)
    {Q : Point → S0} (hQ : ContDiffOn ℝ ∞ Q Ω) (i : Fin 3) :
    ContDiffOn ℝ ∞ (coordDeriv i Q) Ω :=
  (ContinuousLinearMap.apply ℝ S0 (axis i)).contDiff.comp_contDiffOn
    (hQ.fderiv_of_isOpen hΩ (le_of_eq (by simp)))

private theorem continuous_bulkGradient (a : BulkCoefficients) : Continuous (bulkGradient a) := by
  change Continuous (fun B : S0 =>
    let A := symmetricTraceless.subtypeL B
    let t := traceL (A ^ 2)
    (-a.a2 + a.a4 * t + a.a6 * t ^ 2) • A +
      (a.a6' * traceL (A ^ 3)) • (A ^ 2 - (t / 3) • (1 : Tensor)))
  fun_prop

private theorem integrable_mul_of_support {K : Set Point} {φ v : Point → ℝ}
    (hK : IsCompact K) (hφ : ContinuousOn φ K) (hv : ContinuousOn v K)
    (hzero : ∀ x ∉ K, φ x = 0) : Integrable (fun x => φ x * v x) volume :=
  ((hφ.mul hv).integrableOn_compact hK).integrable_of_forall_notMem_eq_zero
    (fun x hx => by
      change φ x * v x = 0
      rw [hzero x hx, zero_mul])

private theorem test_zero_off_support {φ : Point → ℝ} {x : Point} (hx : x ∉ tsupport φ) :
    φ x = 0 := by
  by_contra hn
  exact hx (subset_tsupport φ hn)

private theorem integral_coordDeriv_test_mul {Ω : Set Point} (hΩ : IsOpen Ω)
    {v : Point → ℝ} (hv : ContDiffOn ℝ ∞ v Ω) {φ : Point → ℝ} (hφ : IsSmoothTest Ω φ)
    (k : Fin 3) : (∫ x, coordDeriv k φ x * v x) = -∫ x, φ x * coordDeriv k v x := by
  obtain ⟨hφsmooth, hφcompact, hφsub⟩ := hφ
  have hφderiv : Continuous (coordDeriv k φ) :=
    (hφsmooth.continuous_fderiv (by simp)).clm_apply continuous_const
  have hvderiv : ContinuousOn (coordDeriv k v) Ω :=
    (hv.continuousOn_fderiv_of_isOpen hΩ (by simp)).clm_apply continuousOn_const
  have hpart := integrable_mul_of_support hφcompact hφderiv.continuousOn
    (hv.continuousOn.mono hφsub) (fun x hx => by simp [coordDeriv, fderiv_of_notMem_tsupport ℝ hx])
  have htest := integrable_mul_of_support hφcompact hφsmooth.continuous.continuousOn
    (hv.continuousOn.mono hφsub) (fun _ => test_zero_off_support)
  have htestDeriv := integrable_mul_of_support hφcompact hφsmooth.continuous.continuousOn
    (hvderiv.mono hφsub) (fun _ => test_zero_off_support)
  have hipb := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure Point)) hpart htestDeriv htest
    (fun x _ => (hφsmooth.differentiable (by simp)) x)
    (fun x hx => (hv.differentiableOn (by simp) x (hφsub hx)).differentiableAt
      (hΩ.mem_nhds (hφsub hx)))
  exact neg_eq_iff_eq_neg.mp hipb.symm

theorem eulerLagrange_pointwise_of_weak (a : BulkCoefficients) (ε : ElasticScale)
    {Ω : Set Point} (hΩ : IsOpen Ω) {Q : Point → S0} (hQ : ContDiffOn ℝ ∞ Q Ω)
    (hWeak : IsWeakEulerLagrange a ε Ω Q (fun x j => coordDeriv j Q x)) :
    ∀ x ∈ Ω, (ε : ℝ) ^ 2 • (laplacian Q x : S0).val = bulkGradient a (Q x) := by
  intro x hx
  ext i j
  let v (k : Fin 3) : Point → ℝ := fun y => (coordDeriv k Q y : S0).val i j
  let ψ : Point → ℝ := fun y => bulkGradient a (Q y) i j
  let L : Point → ℝ := fun y => (laplacian Q y : S0).val i j
  let F : Point → ℝ := fun y => ψ y - (ε : ℝ)^2 * L y
  have hD (k : Fin 3) := contDiffOn_coordDeriv hΩ hQ k
  have hDD (k : Fin 3) := contDiffOn_coordDeriv hΩ (hD k) k
  have hv (k : Fin 3) : ContDiffOn ℝ ∞ (v k) Ω :=
    (entryL i j).contDiff.comp_contDiffOn (hD k)
  have hψ : ContinuousOn ψ Ω := by
    have h := (continuous_bulkGradient a).comp_continuousOn hQ.continuousOn
    exact (continuous_apply j).comp_continuousOn ((continuous_apply i).comp_continuousOn h)
  have hL : L = fun y => ∑ k : Fin 3, (coordDeriv k (coordDeriv k Q) y : S0).val i j := by
    funext y
    change entryL i j (laplacian Q y) = ∑ k : Fin 3, entryL i j (coordDeriv k (coordDeriv k Q) y)
    rw [laplacian, map_sum]
  have hLcont : ContinuousOn L Ω := by
    rw [hL]
    exact continuousOn_finsetSum _ (fun k _ =>
      (entryL i j).continuous.comp_continuousOn (hDD k).continuousOn)
  have hF : ContinuousOn F Ω := hψ.sub (continuousOn_const.mul hLcont)
  have hzero := hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (μ := (volume : Measure Point)) (hF.locallyIntegrableOn hΩ.measurableSet) (by
      intro φ hφsmooth hφcompact hφsub
      have hφ : IsSmoothTest Ω φ := ⟨hφsmooth, hφcompact, hφsub⟩
      have hPair (f : Point → ℝ) (hf : ContinuousOn f Ω) :
          Integrable (fun y => φ y * f y) volume :=
        integrable_mul_of_support hφcompact hφsmooth.continuous.continuousOn
          (hf.mono hφsub) (fun _ => test_zero_off_support)
      have hderiv (k : Fin 3) :
          (∫ y, φ y * coordDeriv k (v k) y) =
          ∫ y, φ y * (coordDeriv k (coordDeriv k Q) y : S0).val i j := by
        apply integral_congr_ae
        filter_upwards with y
        by_cases hy : y ∈ tsupport φ
        · have hyD := (hD k y (hφsub hy)).contDiffAt (hΩ.mem_nhds (hφsub hy))
          rw [show coordDeriv k (v k) y =
            (coordDeriv k (coordDeriv k Q) y : S0).val i j from
              coordDeriv_entry i j k (hyD.differentiableAt (by simp))]
        · rw [test_zero_off_support hy, zero_mul, zero_mul]
      have hsum : (∫ y, φ y * L y) =
          ∑ k : Fin 3, ∫ y, φ y * (coordDeriv k (coordDeriv k Q) y : S0).val i j := by
        simp only [hL, Finset.mul_sum]
        exact integral_finsetSum _ (fun k _ =>
          hPair _ ((entryL i j).continuous.comp_continuousOn (hDD k).continuousOn))
      have h := hWeak i j φ hφ
      change (ε : ℝ)^2 * (∑ k : Fin 3, ∫ y, coordDeriv k φ y * v k y) + (∫ y, φ y * ψ y) = 0 at h
      simp_rw [integral_coordDeriv_test_mul hΩ (hv _) hφ, hderiv] at h
      rw [Finset.sum_neg_distrib, ← hsum, mul_neg, neg_add_eq_sub] at h
      change (∫ y, φ y * F y) = 0
      simp only [F, mul_sub, mul_left_comm (φ _) ((ε : ℝ)^2)]
      rw [integral_sub (hPair _ hψ) ((hPair _ hLcont).const_mul _), integral_const_mul]
      exact h)
  have hae : F =ᵐ[volume.restrict Ω] (0 : Point → ℝ) :=
    (ae_restrict_iff' hΩ.measurableSet).2 hzero
  exact (sub_eq_zero.mp (Measure.eqOn_open_of_ae_eq hae hΩ hF continuousOn_const hx)).symm

/-- Lemma 2.27 for the sextic energy on a bounded domain. -/
theorem stressEnergy_rowDivergence_eq_zero
    (a : BulkCoefficients) (ε : ElasticScale) {Ω : Set Point} (hΩ : IsBoundedDomain Ω)
    {Q : Point → S0} (hQ : ContDiffOn ℝ ∞ Q Ω)
    (hEuler : IsWeakEulerLagrange a ε Ω Q (fun x j => coordDeriv j Q x)) :
    ∀ x ∈ Ω, ∀ i : Fin 3, ∑ j, coordDeriv j (fun y => stressTensor a ε Q y i j) x = 0 := by
  apply stressEnergy_rowDivergence_eq_zero_of_pointwise a ε hΩ.1 hQ
  exact eulerLagrange_pointwise_of_weak a ε hΩ.1 hQ hEuler

/-- The sextic bulk potential is smooth on the tensor space. -/
theorem contDiff_bulkPotential (a : BulkCoefficients) : ContDiff ℝ ∞ (bulkPotential a) := by
  let t := fun A : S0 => traceL ((symmetricTraceless.subtypeL A) ^ 2)
  let s := fun A : S0 => traceL ((symmetricTraceless.subtypeL A) ^ 3)
  have ht : ContDiff ℝ ∞ t := by unfold t; fun_prop
  have hs : ContDiff ℝ ∞ s := by unfold s; fun_prop
  change ContDiff ℝ ∞ (fun A : S0 =>
    a.a2 / 2 * preferredTraceSq a - a.a4 / 4 * preferredTraceSq a ^ 2
    - a.a6 / 6 * preferredTraceSq a ^ 3
    - a.a2 / 2 * t A + a.a4 / 4 * t A ^ 2 + a.a6 / 6 * t A ^ 3
    + a.a6' / 6 * s A ^ 2)
  fun_prop

private theorem contDiffOn_gradient_pair {Ω : Set Point} (hΩ : IsOpen Ω) {Q : Point → S0}
    (hQ : ContDiffOn ℝ ∞ Q Ω) (i j : Fin 3) :
    ContDiffOn ℝ ∞ (fun y => frobeniusS0 (coordDeriv i Q y) (coordDeriv j Q y)) Ω := by
  change ContDiffOn ℝ ∞ (fun y => frobeniusS0Form (coordDeriv i Q y) (coordDeriv j Q y)) Ω
  exact (frobeniusS0Form.contDiff.comp_contDiffOn (contDiffOn_coordDeriv hΩ hQ i)).clm_apply
    (contDiffOn_coordDeriv hΩ hQ j)

/-- The classical energy density is smooth on the smooth map domain. -/
theorem contDiffOn_classicalEnergyDensity (a : BulkCoefficients) (ε : ElasticScale)
    {Ω : Set Point} (hΩ : IsOpen Ω) {Q : Point → S0} (hQ : ContDiffOn ℝ ∞ Q Ω) :
    ContDiffOn ℝ ∞ (fun y => energyDensity a ε (Q y) (fun k => coordDeriv k Q y)) Ω :=
  (contDiffOn_const.mul (ContDiffOn.sum (fun k _ => contDiffOn_gradient_pair hΩ hQ k k))).add
    (contDiffOn_const.mul ((contDiff_bulkPotential a).comp_contDiffOn hQ))

/-- Each scalar stress component is smooth on the smooth solution domain. -/
theorem contDiffOn_stressTensor_entry (a : BulkCoefficients) (ε : ElasticScale)
    {Ω : Set Point} (hΩ : IsOpen Ω) {Q : Point → S0} (hQ : ContDiffOn ℝ ∞ Q Ω)
    (i j : Fin 3) : ContDiffOn ℝ ∞ (fun y => stressTensor a ε Q y i j) Ω := by
  have hp := contDiffOn_gradient_pair hΩ hQ i j
  by_cases hij : i = j
  · simpa only [stressTensor, if_pos hij] using (contDiffOn_classicalEnergyDensity a ε hΩ hQ).sub hp
  · simpa only [stressTensor, if_neg hij, zero_sub] using hp.neg

/-- The exact pointwise stress equation tested against a compactly supported
smooth scalar in one row. -/
theorem integral_stressTensor_row_test_eq_zero (a : BulkCoefficients) (ε : ElasticScale)
    {Ω : Set Point} (hΩ : IsOpen Ω) {Q : Point → S0} (hQ : ContDiffOn ℝ ∞ Q Ω)
    (hEuler : ∀ x ∈ Ω, (ε : ℝ) ^ 2 • (laplacian Q x : S0).val = bulkGradient a (Q x))
    {φ : Point → ℝ} (hφ : IsSmoothTest Ω φ) (i : Fin 3) :
    Integrable (fun x => ∑ j, coordDeriv j φ x * stressTensor a ε Q x i j) volume ∧
    (∫ x, ∑ j, coordDeriv j φ x * stressTensor a ε Q x i j) = 0 := by
  have hT (j : Fin 3) := contDiffOn_stressTensor_entry a ε hΩ hQ i j
  have hφD (j : Fin 3) : Continuous (coordDeriv j φ) :=
    (hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const
  have hTD (j : Fin 3) :
      ContinuousOn (coordDeriv j (fun y => stressTensor a ε Q y i j)) Ω :=
    ((hT j).continuousOn_fderiv_of_isOpen hΩ (by simp)).clm_apply continuousOn_const
  have hInt (j : Fin 3) : Integrable (fun x => coordDeriv j φ x * stressTensor a ε Q x i j) volume :=
    integrable_mul_of_support hφ.2.1 (hφD j).continuousOn ((hT j).continuousOn.mono hφ.2.2)
      (fun x hx => by simp [coordDeriv, fderiv_of_notMem_tsupport ℝ hx])
  have hInt' (j : Fin 3) :
      Integrable (fun x => φ x * coordDeriv j (fun y => stressTensor a ε Q y i j) x) volume :=
    integrable_mul_of_support hφ.2.1 hφ.1.continuous.continuousOn ((hTD j).mono hφ.2.2)
      (fun _ => test_zero_off_support)
  refine ⟨integrable_finsetSum _ (fun j _ => hInt j), ?_⟩
  rw [integral_finsetSum _ (fun j _ => hInt j)]
  simp_rw [integral_coordDeriv_test_mul hΩ (hT _) hφ]
  rw [Finset.sum_neg_distrib, ← integral_finsetSum _ (fun j _ => hInt' j), neg_eq_zero]
  simp_rw [← Finset.mul_sum]
  apply integral_eq_zero_of_ae
  filter_upwards with x
  change φ x * (∑ j, coordDeriv j (fun y => stressTensor a ε Q y i j) x) = 0
  by_cases hx : x ∈ tsupport φ
  · rw [stressEnergy_rowDivergence_eq_zero_of_pointwise a ε hΩ hQ hEuler x (hφ.2.2 hx) i,
      mul_zero]
  · rw [test_zero_off_support hx, zero_mul]

/-- The integrated row identities combine into contraction with a compactly
supported smooth domain vector field. -/
theorem integral_stressTensor_contract_eq_zero (a : BulkCoefficients) (ε : ElasticScale)
    {Ω : Set Point} (hΩ : IsOpen Ω) {Q : Point → S0} (hQ : ContDiffOn ℝ ∞ Q Ω)
    (hEuler : ∀ x ∈ Ω, (ε : ℝ) ^ 2 • (laplacian Q x : S0).val = bulkGradient a (Q x))
    {X : Point → Point} (hX : IsSmoothTest Ω X) :
    (∫ x, ∑ i, ∑ j, ((fderiv ℝ X x) (axis j)) i * stressTensor a ε Q x i j) = 0 := by
  let P (i : Fin 3) : Point →L[ℝ] ℝ := PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) i
  let φ (i : Fin 3) : Point → ℝ := fun x => X x i
  have hφ (i : Fin 3) : IsSmoothTest Ω (φ i) := by
    have hsub : tsupport (φ i) ⊆ tsupport X :=
      closure_mono fun x hx => by
        by_contra hn
        exact hx (by simp [φ, Function.notMem_support.mp hn])
    exact ⟨(P i).contDiff.comp hX.1,
      hX.2.1.of_isClosed_subset (isClosed_tsupport _) hsub, hsub.trans hX.2.2⟩
  have hder (i j : Fin 3) (x : Point) :
      coordDeriv j (φ i) x = (fderiv ℝ X x (axis j)) i :=
    DFunLike.congr_fun (((P i).hasFDerivAt (x := X x)).comp x
      ((hX.1.differentiable (by simp)) x).hasFDerivAt).fderiv (axis j)
  have hrow (i : Fin 3) := integral_stressTensor_row_test_eq_zero a ε hΩ hQ hEuler (hφ i) i
  simp_rw [← hder]
  rw [integral_finsetSum _ (fun i _ => (hrow i).1)]
  simp only [(hrow _).2, Finset.sum_const_zero]

end Thesis

end
