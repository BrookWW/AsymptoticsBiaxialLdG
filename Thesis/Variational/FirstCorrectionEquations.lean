module

public import Thesis.Variational.HarmonicEquation
public import Thesis.Foundation.LinearizedBulk
import Thesis.Variational.BoundaryDefect
import Thesis.Variational.BoundarySubsolution

/-! Differential identities for the actual scaled first correction. -/

public section

open Filter Set Topology
open scoped BigOperators ContDiff Matrix Matrix.Norms.Frobenius

set_option autoImplicit false
noncomputable section

namespace Thesis

theorem coordDeriv_twice_eq_iteratedFDeriv_two
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Point → E} {x : Point} (hf : ContDiffAt ℝ 2 f x) (j : Fin 3) :
    coordDeriv j (coordDeriv j f) x = iteratedFDeriv ℝ 2 f x (fun _ => axis j) := by
  let L := ContinuousLinearMap.apply ℝ E (axis j)
  have hf' := (hf.fderiv_right_succ (n := 1)).differentiableAt one_ne_zero
  have hE := (L.hasFDerivAt (x := fderiv ℝ f x)).comp x hf'.hasFDerivAt
  rw [iteratedFDeriv_two_apply]
  exact DFunLike.congr_fun hE.fderiv (axis j)

theorem ConvergesCjLoc.tendsto_at_of_two {U : Set Point} {u : ℕ → Point → S0} {v : Point → S0}
    (h : ConvergesCjLoc 2 U u v) {x : Point} (hx : x ∈ U) :
    Tendsto (fun n => u n x) atTop (𝓝 (v x)) := by
  have hT := (h.2.2 0 (by decide) {x} isCompact_singleton (singleton_subset_iff.mpr hx)).tendsto_at
    (mem_singleton x)
  let E := ContinuousMultilinearMap.apply ℝ (fun _ : Fin 0 => Point) S0 (fun _ => 0)
  have h' := (E.continuous.tendsto (iteratedFDeriv ℝ 0 v x)).comp hT
  change Tendsto (fun n => iteratedFDeriv ℝ 0 (u n) x (fun _ => 0)) atTop
    (𝓝 (iteratedFDeriv ℝ 0 v x (fun _ => 0))) at h'
  simpa only [iteratedFDeriv_zero_apply] using h'

theorem ConvergesCjLoc.tendsto_laplacian_at {U : Set Point} (hU : IsOpen U)
    {u : ℕ → Point → S0} {v : Point → S0} (h : ConvergesCjLoc 2 U u v) {x : Point} (hx : x ∈ U) :
    Tendsto (fun n => laplacian (u n) x) atTop (𝓝 (laplacian v x)) := by
  have hT := (h.2.2 2 le_rfl {x} isCompact_singleton (singleton_subset_iff.mpr hx)).tendsto_at
    (mem_singleton x)
  unfold laplacian
  apply tendsto_finsetSum
  intro j _
  let E := ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => Point) S0 (fun _ => axis j)
  have h' := (E.continuous.tendsto (iteratedFDeriv ℝ 2 v x)).comp hT
  change Tendsto (fun n => iteratedFDeriv ℝ 2 (u n) x (fun _ => axis j)) atTop
    (𝓝 (iteratedFDeriv ℝ 2 v x (fun _ => axis j))) at h'
  rw [coordDeriv_twice_eq_iteratedFDeriv_two ((h.2.1 x hx).contDiffAt (hU.mem_nhds hx)) j]
  exact h'.congr' (Eventually.of_forall fun n =>
    (coordDeriv_twice_eq_iteratedFDeriv_two ((h.1 n x hx).contDiffAt (hU.mem_nhds hx)) j).symm)

/-- Local two-derivative convergence identifies the actual first
derivative columns at each interior point. -/
theorem ConvergesCjLoc.tendsto_classicalGradient_at_of_two
    {U : Set Point} {u : ℕ → Point → S0} {v : Point → S0}
    (h : ConvergesCjLoc 2 U u v) {x : Point} (hx : x ∈ U) :
    Tendsto (fun n => ClassicalGradient (u n) x) atTop (𝓝 (ClassicalGradient v x)) := by
  apply tendsto_pi_nhds.mpr
  intro j
  have hT := (h.2.2 1 (by decide) {x} isCompact_singleton (singleton_subset_iff.mpr hx)).tendsto_at
    (mem_singleton x)
  let E := ContinuousMultilinearMap.apply ℝ (fun _ : Fin 1 => Point) S0 (fun _ => axis j)
  have h' := (E.continuous.tendsto (iteratedFDeriv ℝ 1 v x)).comp hT
  change Tendsto (fun n => iteratedFDeriv ℝ 1 (u n) x (fun _ => axis j)) atTop
    (𝓝 (iteratedFDeriv ℝ 1 v x (fun _ => axis j))) at h'
  simpa only [iteratedFDeriv_one_apply, ClassicalGradient, coordDeriv] using h'

private theorem tangentProjector_harmonicLaplacian_eq_zero
    {a : BulkCoefficients} {q : Point → S0} {x : Point} (hVac : q x ∈ vacuum a)
    (hHarm : (↑(laplacian q x) : Tensor) = harmonicRhs a q (ClassicalGradient q) x) :
    vacuumTangentProjector a (q x) (laplacian q x) = 0 := by
  let D := ClassicalGradient q
  let v := (-2 * gradientNormSq (D x), -6 * gradientTraceMul D D (q x) x)
  have hL : laplacian q x = vacuumInvariantRightInverse a (q x) v :=
    Subtype.ext (hHarm.trans (harmonicRhs_eq_invariantRightInverse D hVac))
  rw [hL]
  change vacuumInvariantRightInverse a (q x) v -
    vacuumInvariantRightInverse a (q x) (vacuumInvariantDerivative (q x)
      (vacuumInvariantRightInverse a (q x) v)) = 0
  rw [vacuumInvariantRightInverse_isRightInverse hVac, sub_self]

private theorem scaledDifference_value (ε : ElasticScale) (A B : S0) :
    A = B + (ε : ℝ)^2 • ((ε : ℝ)⁻¹^2 • (A - B)) := by
  have hInv : (ε : ℝ)^2 * (ε : ℝ)⁻¹^2 = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ ε.2.1.ne', one_pow]
  rw [smul_smul, hInv, one_smul]
  abel

private theorem laplacian_add_scaledDifference {U : Set Point} (hU : IsOpen U)
    (ε : ElasticScale) {u q : Point → S0} (hu : ContDiffOn ℝ 2 u U) (hq : ContDiffOn ℝ 2 q U)
    {x : Point} (hx : x ∈ U) :
    laplacian u x = laplacian q x +
      (ε : ℝ)^2 • laplacian (fun y => (ε : ℝ)⁻¹^2 • (u y - q y)) x := by
  rw [laplacian_const_smul hU (hu.sub hq) hx,
    laplacian_sub_of_contDiffOn hU hu hq hx]
  exact scaledDifference_value ε (laplacian u x) (laplacian q x)

private theorem tendsto_laplacian_of_scaledDifference {U : Set Point} (hU : IsOpen U)
    {ε : ℕ → ElasticScale} {u : ℕ → Point → S0} {q P : Point → S0}
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (hu : ∀ n, ContDiffOn ℝ 2 (u n) U) (hq : ContDiffOn ℝ 2 q U)
    (hConv : ConvergesCjLoc 2 U (fun n x => (ε n : ℝ)⁻¹^2 • (u n x - q x)) P)
    {x : Point} (hx : x ∈ U) :
    Tendsto (fun n => laplacian (u n) x) atTop (𝓝 (laplacian q x)) := by
  have hs : Tendsto (fun n => (ε n : ℝ)^2) atTop (𝓝 0) := by
    simpa only [zero_pow two_ne_zero] using hε.pow 2
  have h := (tendsto_const_nhds (x := laplacian q x)).add
    (hs.smul (hConv.tendsto_laplacian_at hU hx))
  simpa only [zero_smul, add_zero] using h.congr' (Eventually.of_forall fun n =>
    (laplacian_add_scaledDifference hU (ε n) (hu n) hq hx).symm)

private theorem projected_force_fourth_scale {a : BulkCoefficients} {A : S0} (hA : A ∈ vacuum a)
    (ε : ElasticScale) (B : S0) :
    let T := vacuumTangentProjector a A
    let s := (ε : ℝ)^2
    ((ε : ℝ)^4)⁻¹ • T (bulkForce a (A + s • B)) =
      T (bulkForceQuadraticTerm a A B) + s • T (bulkForcePolynomialRemainder a A B s) := by
  let T := vacuumTangentProjector a A
  apply Subtype.ext
  change ((ε : ℝ)^4)⁻¹ • (↑(T (bulkForce a (A + (ε : ℝ)^2 • B))) : Tensor) =
    (↑(T (bulkForceQuadraticTerm a A B)) : Tensor) +
      (ε : ℝ)^2 • (↑(T (bulkForcePolynomialRemainder a A B ((ε : ℝ)^2))) : Tensor)
  simpa only [tangentPart_eq_vacuumTangentProjector hA] using tangentPart_bulkForce_fourth_scale hA B ε

private theorem tendsto_projected_force_fourth_scale {a : BulkCoefficients} {A : S0}
    (hA : A ∈ vacuum a) {ε : ℕ → ElasticScale} {B : ℕ → S0} {P : S0}
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0)) (hB : Tendsto B atTop (𝓝 P)) :
    let T := vacuumTangentProjector a A
    Tendsto (fun n => ((ε n : ℝ)^4)⁻¹ • T (bulkForce a (A + (ε n : ℝ)^2 • B n)))
      atTop (𝓝 (T (bulkForceQuadraticTerm a A P))) := by
  let T := vacuumTangentProjector a A
  let F (p : ℝ × S0) := T (bulkForceQuadraticTerm a A p.2) +
    p.1 ^ 2 • T (bulkForcePolynomialRemainder a A p.2 (p.1 ^ 2))
  have ht : ContDiff ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) (fun p : ℝ × S0 => p.1) := contDiff_fst
  have hP : ContDiff ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) (fun p : ℝ × S0 => p.2) := contDiff_snd
  have hAB : ContDiff ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) (fun p : ℝ × S0 => (A, p.2)) :=
    contDiff_const.prodMk hP
  have hABt : ContDiff ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) (fun p : ℝ × S0 => (A, p.2, p.1 ^ 2)) :=
    contDiff_const.prodMk (hP.prodMk (ht.pow 2))
  have hQ := T.contDiff.comp ((contDiff_bulkForceQuadraticTerm a).comp hAB)
  have hR := T.contDiff.comp ((contDiff_bulkForcePolynomialRemainder a).comp hABt)
  have hFC : ContDiff ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) F := hQ.add ((ht.pow 2).smul hR)
  have hF0 : F (0, P) = T (bulkForceQuadraticTerm a A P) := by
    simp only [F, zero_pow two_ne_zero, zero_smul, add_zero]
  have hFL := (hFC.continuous.tendsto ((0 : ℝ), P)).comp (hε.prodMk_nhds hB)
  rw [hF0] at hFL
  have hE (n : ℕ) : F ((ε n : ℝ), B n) =
      ((ε n : ℝ)^4)⁻¹ • T (bulkForce a (A + (ε n : ℝ)^2 • B n)) :=
    (projected_force_fourth_scale hA (ε n) (B n)).symm
  exact hFL.congr' (Eventually.of_forall hE)

private theorem projected_scaledDifference_laplacian
    (a : BulkCoefficients) {U : Set Point} (hU : IsOpen U) (ε : ElasticScale)
    {u q : Point → S0} (hu : ContDiffOn ℝ 2 u U) (hq : ContDiffOn ℝ 2 q U)
    {x : Point} (hx : x ∈ U)
    (h0 : vacuumTangentProjector a (q x) (laplacian q x) = 0)
    (hEq : (ε : ℝ)^2 • laplacian u x = bulkForce a (u x)) :
    let T := vacuumTangentProjector a (q x)
    ((ε : ℝ)^4)⁻¹ • T (bulkForce a (u x)) =
      T (laplacian (fun y => (ε : ℝ)⁻¹^2 • (u y - q y)) x) := by
  let T := vacuumTangentProjector a (q x)
  change ((ε : ℝ)^4)⁻¹ • T (bulkForce a (u x)) =
    T (laplacian (fun y => (ε : ℝ)⁻¹^2 • (u y - q y)) x)
  rw [← hEq, laplacian_add_scaledDifference hU ε hu hq hx, map_smul, map_add, map_smul,
    h0, zero_add, smul_smul, smul_smul]
  have hε : ((ε : ℝ)^4)⁻¹ * (ε : ℝ)^2 * (ε : ℝ)^2 = 1 := by
    field_simp [ε.2.1.ne']
  rw [hε, one_smul]

/-- The normal limit and the projected next-order equation for the
scaled difference. The tangent projection is taken after the Laplacian. -/
theorem firstCorrection_linearized_force_and_tangent_laplacian
    (a : BulkCoefficients) {U : Set Point} (hU : IsOpen U)
    (ε : ℕ → ElasticScale) (Q : ℕ → Point → S0) (q P : Point → S0)
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (hQ : ∀ n, ContDiffOn ℝ 2 (Q n) U) (hq : ContDiffOn ℝ 2 q U)
    (hVac : MapsTo q U (vacuum a))
    (hHarm : ∀ x ∈ U, (↑(laplacian q x) : Tensor) = harmonicRhs a q (ClassicalGradient q) x)
    (hEuler : ∀ n, ∀ x ∈ U, (ε n : ℝ) ^ 2 • (↑(laplacian (Q n) x) : Tensor) = bulkGradient a (Q n x))
    (hConv : ConvergesCjLoc 2 U (fun n x => (ε n : ℝ)⁻¹ ^ 2 • (Q n x - q x)) P) :
    ∀ x ∈ U,
      ((fderiv ℝ (bulkForce a) (q x)) (P x) : Tensor) = harmonicRhs a q (ClassicalGradient q) x ∧
      tangentPart a (q x : Tensor) (↑(laplacian P x) : Tensor) =
        tangentPart a (q x : Tensor) (bulkForceQuadraticTerm a (q x) (P x) : Tensor) := by
  intro x hx
  let W (n : ℕ) (y : Point) := (ε n : ℝ)⁻¹ ^ 2 • (Q n y - q y)
  let T := vacuumTangentProjector a (q x)
  have hW : Tendsto (fun n => W n x) atTop (𝓝 (P x)) := hConv.tendsto_at_of_two hx
  have hQc (n : ℕ) : Q n x = q x + (ε n : ℝ)^2 • W n x :=
    scaledDifference_value (ε n) (Q n x) (q x)
  have hF (n : ℕ) : (ε n : ℝ)^2 • laplacian (Q n) x = bulkForce a (Q n x) :=
    Subtype.ext (hEuler n x hx)
  have hF' (n : ℕ) : ((ε n : ℝ)^2)⁻¹ • bulkForce a (q x + (ε n : ℝ)^2 • W n x) =
      laplacian (Q n) x := by
    rw [← hQc n, ← hF n, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ (ε n).2.1.ne'), one_smul]
  have hNormal := linearized_bulkForce_eq_of_scaled_limit (hVac hx) hε hW
    (tendsto_laplacian_of_scaledDifference hU hε hQ hq hConv hx) (Eventually.of_forall hF')
  refine ⟨(congrArg Subtype.val hNormal).trans (hHarm x hx), ?_⟩
  have h0 := tangentProjector_harmonicLaplacian_eq_zero (hVac hx) (hHarm x hx)
  have hW₂ : Tendsto (fun n => laplacian (W n) x) atTop (𝓝 (laplacian P x)) :=
    hConv.tendsto_laplacian_at hU hx
  have hLim := T.continuous.tendsto (laplacian P x) |>.comp hW₂
  have hT := tendsto_projected_force_fourth_scale (hVac hx) hε hW
  have hEq := tendsto_nhds_unique hLim (hT.congr' (Eventually.of_forall fun n => by
    rw [← hQc n]
    exact projected_scaledDifference_laplacian a hU (ε n) (hQ n) hq hx h0 (hF n)))
  simpa only [tangentPart_eq_vacuumTangentProjector (hVac hx)] using congrArg Subtype.val hEq

private theorem tangentPart_trace_pair {a : BulkCoefficients} {A : S0} (hA : A ∈ vacuum a) (B : S0) :
    ((A : Tensor) * tangentPart a (A : Tensor) (B : Tensor)).trace = 0 ∧
    (((A : Tensor)^2) * tangentPart a (A : Tensor) (B : Tensor)).trace = 0 := by
  let T := vacuumTangentProjector a A B
  have h : vacuumInvariantDerivative A T = 0 := by
    change vacuumInvariantDerivative A
      (B - vacuumInvariantRightInverse a A (vacuumInvariantDerivative A B)) = 0
    rw [map_sub, vacuumInvariantRightInverse_isRightInverse hA, sub_self]
  rw [vacuumInvariantDerivative_apply] at h
  simp only [tangentPart_eq_vacuumTangentProjector hA]
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  change 2 * ((A : Tensor) * (T : Tensor)).trace = 0 at h₁
  change 3 * (((A : Tensor)^2) * (T : Tensor)).trace = 0 at h₂
  exact ⟨by linarith only [h₁], by linarith only [h₂]⟩

private theorem trace_tangentPart_harmonicRhs {a : BulkCoefficients} {q : Point → S0}
    {x : Point} (hA : q x ∈ vacuum a) (B : S0) :
    (tangentPart a (q x : Tensor) (B : Tensor) * harmonicRhs a q (ClassicalGradient q) x).trace = 0 := by
  let A : Tensor := q x
  let T := tangentPart a A (B : Tensor)
  obtain ⟨ht, htsq⟩ := tangentPart_trace_pair hA B
  have hT : T.trace = 0 := by
    rw [show T = (↑(vacuumTangentProjector a (q x) B) : Tensor) from
      tangentPart_eq_vacuumTangentProjector hA B]
    exact S0.trace_eq_zero _
  have h₁ : (T * A).trace = 0 := (Matrix.trace_mul_comm T A).trans ht
  have h₂ : (T * A ^ 2).trace = 0 := (Matrix.trace_mul_comm T (A ^ 2)).trans htsq
  change (T * (_ • A - _ • biaxialQuadratic a A)).trace = 0
  simp [biaxialQuadratic, Matrix.mul_sub, Matrix.trace_sub, Matrix.trace_smul, h₁, h₂, hT]

private theorem contDiffOn_normalPart_field (a : BulkCoefficients) {U : Set Point}
    {A B : Point → Tensor} (hA : ContDiffOn ℝ 2 A U) (hB : ContDiffOn ℝ 2 B U) :
    ContDiffOn ℝ 2 (fun y => normalPart a (A y) (B y)) U := by
  have ht := tensorTraceCLM.contDiff.comp_contDiffOn (hA.mul hB)
  have htsq := tensorTraceCLM.contDiff.comp_contDiffOn ((hA.pow 2).mul hB)
  have hSq : ContDiffOn ℝ 2 (fun y => biaxialQuadratic a (A y)) U :=
    (hA.pow 2).sub contDiffOn_const
  exact ((ht.div_const _).smul hA).add ((htsq.div_const _).smul (hSq.const_smul 3))

private theorem trace_laplacian_product_eq_of_zero {U : Set Point} (hU : IsOpen U)
    {A B : Point → Tensor} (hA : ContDiffOn ℝ 2 A U) (hB : ContDiffOn ℝ 2 B U)
    (hZero : ∀ y ∈ U, (A y * B y).trace = 0) {x : Point} (hx : x ∈ U) :
    (laplacian A x * B x).trace =
      -(2 * ∑ j, (coordDeriv j A x * coordDeriv j B x).trace) - (A x * laplacian B x).trace := by
  have hGerm : (fun y => (A y * B y).trace) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hZero y hy
  have hL := laplacian_eq_of_eventuallyEq hGerm
  have hconst : laplacian (fun _ : Point => (0 : ℝ)) x = 0 := by
    have hz (j : Fin 3) : coordDeriv j (fun _ : Point => (0 : ℝ)) = fun _ => 0 := by
      funext y
      simp [coordDeriv]
    simp only [laplacian, hz, Finset.sum_const_zero]
  rw [hconst] at hL
  have hTrace := laplacian_compCLM hU (hA.mul hB) hx tensorTraceCLM
  change laplacian (fun y => (A y * B y).trace) x = (laplacian (fun y => A y * B y) x).trace at hTrace
  rw [hTrace, laplacian_matrix_product hU hA hB hx, Matrix.trace_add, Matrix.trace_add,
    Matrix.trace_smul, Matrix.trace_sum, smul_eq_mul] at hL
  linarith only [hL]

private theorem tangentPart_sub (a : BulkCoefficients) (A B C : Tensor) :
    tangentPart a A (B - C) = tangentPart a A B - tangentPart a A C := by
  unfold tangentPart normalPart
  simp only [Matrix.mul_sub, Matrix.trace_sub, sub_div, sub_smul]
  abel

private theorem laplacian_tangentPart_field_decompose
    (a : BulkCoefficients) {U : Set Point} (hU : IsOpen U) {A B : Point → Tensor}
    (hA : ContDiffOn ℝ 2 A U) (hB : ContDiffOn ℝ 2 B U) {x : Point} (hx : x ∈ U) :
    let T := fun y => tangentPart a (A y) (B y)
    let N := fun y => normalPart a (A y) (B y)
    laplacian T x = normalPart a (A x) (laplacian T x) +
      tangentPart a (A x) (laplacian B x) - tangentPart a (A x) (laplacian N x) := by
  dsimp only
  have h : laplacian (fun y => tangentPart a (A y) (B y)) x =
      laplacian B x - laplacian (fun y => normalPart a (A y) (B y)) x :=
    laplacian_sub_of_contDiffOn hU hB (contDiffOn_normalPart_field a hA hB) hx
  rw [add_sub_assoc]
  rw [show tangentPart a (A x) (laplacian B x) -
      tangentPart a (A x) (laplacian (fun y => normalPart a (A y) (B y)) x) =
      tangentPart a (A x) (laplacian (fun y => tangentPart a (A y) (B y)) x) by
    rw [h, tangentPart_sub]]
  unfold tangentPart
  abel

private theorem normal_laplacian_tangentPart_field
    (a : BulkCoefficients) {U : Set Point} (hU : IsOpen U) {q P : Point → S0}
    (hq : ContDiffOn ℝ 2 q U) (hP : ContDiffOn ℝ 2 P U) (hVac : MapsTo q U (vacuum a))
    {x : Point} (hx : x ∈ U)
    (hHarm : (↑(laplacian q x) : Tensor) = harmonicRhs a q (ClassicalGradient q) x) :
    let r := vacuumRadius a
    let A : Point → Tensor := fun y => q y
    let T : Point → Tensor := fun y => tangentPart a (q y) (P y)
    let Asq : Point → Tensor := fun y => (A y)^2
    let g₁ := ∑ j, (coordDeriv j T x * (coordDeriv j q x : S0)).trace
    let g₂ := ∑ j, (coordDeriv j T x * coordDeriv j Asq x).trace
    normalPart a (A x) (laplacian T x) = (-(g₁ / r^2)) • A x -
      ((2*g₂ + (T x * laplacian Asq x).trace) / (2*r^4)) • (3 : ℝ) • biaxialQuadratic a (A x) := by
  let A : Point → Tensor := fun y => q y
  let B : Point → Tensor := fun y => P y
  let T : Point → Tensor := fun y => tangentPart a (A y) (B y)
  let Asq : Point → Tensor := fun y => (A y)^2
  let r := vacuumRadius a
  let g₁ := ∑ j, (coordDeriv j T x * (coordDeriv j q x : S0)).trace
  let g₂ := ∑ j, (coordDeriv j T x * coordDeriv j Asq x).trace
  change normalPart a (A x) (laplacian T x) = (-(g₁ / r^2)) • A x -
    ((2*g₂ + (T x * laplacian Asq x).trace) / (2*r^4)) • (3 : ℝ) • biaxialQuadratic a (A x)
  have hA : ContDiffOn ℝ 2 A U := symmetricTraceless.subtypeL.contDiff.comp_contDiffOn hq
  have hB : ContDiffOn ℝ 2 B U := symmetricTraceless.subtypeL.contDiff.comp_contDiffOn hP
  have hT : ContDiffOn ℝ 2 T U := hB.sub (contDiffOn_normalPart_field a hA hB)
  have hL : laplacian A x = (↑(laplacian q x) : Tensor) :=
    laplacian_compCLM hU hq hx symmetricTraceless.subtypeL
  have hD (j : Fin 3) : coordDeriv j A x = (coordDeriv j q x : S0).val :=
    coordDeriv_compCLM symmetricTraceless.subtypeL
      (((hq x hx).contDiffAt (hU.mem_nhds hx)).differentiableAt two_ne_zero) j
  have hZ (y : Point) (hy : y ∈ U) :
      (T y * A y).trace = 0 ∧ (T y * Asq y).trace = 0 := by
    rw [Matrix.trace_mul_comm (T y) (A y), Matrix.trace_mul_comm (T y) (Asq y)]
    exact tangentPart_trace_pair (hVac hy) (P y)
  have hTL : (T x * laplacian A x).trace = 0 := by
    rw [hL, hHarm]
    exact trace_tangentPart_harmonicRhs (hVac hx) (P x)
  have h₁ := trace_laplacian_product_eq_of_zero hU hT hA (fun y hy => (hZ y hy).1) hx
  have h₂ := trace_laplacian_product_eq_of_zero hU hT (show ContDiffOn ℝ 2 Asq U from hA.pow 2)
    (fun y hy => (hZ y hy).2) hx
  rw [hTL, sub_zero] at h₁
  simp only [hD] at h₁
  have h₁' : (A x * laplacian T x).trace = -(2 * g₁) :=
    (Matrix.trace_mul_comm (A x) (laplacian T x)).trans h₁
  have h₂' : (Asq x * laplacian T x).trace = -(2 * g₂) - (T x * laplacian Asq x).trace :=
    (Matrix.trace_mul_comm (Asq x) (laplacian T x)).trans h₂
  have hd₁ : -(2 * g₁) / (2 * r^2) = -(g₁ / r^2) := by ring
  have hd₂ : (-(2 * g₂) - (T x * laplacian Asq x).trace) / (2 * r^4) =
      -((2 * g₂ + (T x * laplacian Asq x).trace) / (2 * r^4)) := by ring
  unfold normalPart
  change ((A x * laplacian T x).trace / (2 * r^2)) • A x +
    ((Asq x * laplacian T x).trace / (2 * r^4)) • (3 : ℝ) • biaxialQuadratic a (A x) = _
  rw [h₁', h₂', hd₁, hd₂, sub_eq_add_neg]
  simp only [neg_smul]

private theorem tangentPart_quadratic_explicit {a : BulkCoefficients} {A : S0} (hA : A ∈ vacuum a)
    (B : S0) :
    let X : Tensor := A
    let Y : Tensor := B
    let r := vacuumRadius a
    let t₁ := (X * Y).trace
    let t₂ := (X^2 * Y).trace
    tangentPart a X (bulkForceQuadraticTerm a A B : Tensor) =
      ((2*a.a4 + 8*a.a6*r^2)*t₁) • tangentPart a X Y +
      (3*a.a6'*t₂) • (X*Y + Y*X - (2/3*t₁) • (1 : Tensor)) -
      (3*a.a6'/r^2*t₂) • (t₂ • X + t₁ • biaxialQuadratic a X) := by
  let X : Tensor := A
  let Y : Tensor := B
  let r := vacuumRadius a
  let t₁ := (X * Y).trace
  let t₂ := (X^2 * Y).trace
  change tangentPart a X (bulkForceQuadraticTerm a A B : Tensor) =
    ((2*a.a4 + 8*a.a6*r^2)*t₁) • tangentPart a X Y +
      (3*a.a6'*t₂) • (X*Y + Y*X - (2/3*t₁) • (1 : Tensor)) -
      (3*a.a6'/r^2*t₂) • (t₂ • X + t₁ • biaxialQuadratic a X)
  have hRad : 2 * bulkRadialCoefficient a = 2*a.a4 + 8*a.a6*r^2 := by
    unfold bulkRadialCoefficient
    dsimp only [r]
    ring
  have hJordan : (3*a.a6'*t₂) • tangentPart a X (traceFreeJordan A B : Tensor) =
      (3*a.a6'*t₂) • (X*Y + Y*X - (2/3*t₁) • (1 : Tensor)) -
        (3*a.a6'/r^2*t₂) • (t₂ • X + t₁ • biaxialQuadratic a X) := by
    have hN := normalPart_traceFreeJordan hA B
    change normalPart a X (traceFreeJordan A B : Tensor) =
      (t₂/r^2) • X + (t₁/r^2) • biaxialQuadratic a X at hN
    rw [tangentPart, hN, traceFreeJordan_coe, smul_sub, smul_add, smul_add]
    have hs (z : ℝ) : (3*a.a6'*t₂) * (z/r^2) = (3*a.a6'/r^2*t₂) * z := by ring
    simp only [smul_smul, hs]
    rfl
  rw [tangentPart_bulkForceQuadraticTerm hA B, hRad, hJordan]
  exact (add_sub_assoc _ _ _).symm

/-- The explicit tangential equation obtained by differentiating the two
trace constraints on the tangent component of the correction. -/
theorem laplacian_tangentPart_eq_tangentCorrectionRhs
    (a : BulkCoefficients) {U : Set Point} (hU : IsOpen U) {q P : Point → S0}
    (hq : ContDiffOn ℝ 2 q U) (hP : ContDiffOn ℝ 2 P U) (hVac : MapsTo q U (vacuum a))
    {x : Point} (hx : x ∈ U)
    (hHarm : (↑(laplacian q x) : Tensor) = harmonicRhs a q (ClassicalGradient q) x)
    (hEq : tangentPart a (q x : Tensor) (↑(laplacian P x) : Tensor) =
      tangentPart a (q x : Tensor) (bulkForceQuadraticTerm a (q x) (P x) : Tensor)) :
    laplacian (fun y => tangentPart a (q y) (P y)) x = tangentCorrectionRhs a q P x := by
  let A : Point → Tensor := fun y => q y
  let B : Point → Tensor := fun y => P y
  let N : Point → Tensor := fun y => normalPart a (A y) (B y)
  let T : Point → Tensor := fun y => tangentPart a (A y) (B y)
  have hA : ContDiffOn ℝ 2 A U := symmetricTraceless.subtypeL.contDiff.comp_contDiffOn hq
  have hB : ContDiffOn ℝ 2 B U := symmetricTraceless.subtypeL.contDiff.comp_contDiffOn hP
  have hL : laplacian B x = (↑(laplacian P x) : Tensor) :=
    laplacian_compCLM hU hP hx symmetricTraceless.subtypeL
  have h := laplacian_tangentPart_field_decompose a hU hA hB hx
  change laplacian T x = normalPart a (A x) (laplacian T x) +
    tangentPart a (A x) (laplacian B x) - tangentPart a (A x) (laplacian N x) at h
  change laplacian T x = _
  rw [h, hL, hEq, normal_laplacian_tangentPart_field a hU hq hP hVac hx hHarm,
    tangentPart_quadratic_explicit (hVac hx) (P x)]
  dsimp only [tangentCorrectionRhs, A, B, N, T]
  abel

/-- Local two-derivative convergence of the scaled difference yields both
trace coefficients and the normal and tangential first-correction equations. -/
theorem firstCorrection_equations_of_convergesC2Loc
    (a : BulkCoefficients) {U : Set Point} (hU : IsOpen U)
    (ε : ℕ → ElasticScale) (Q : ℕ → Point → S0) (q P : Point → S0)
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (hQ : ∀ n, ContDiffOn ℝ 2 (Q n) U) (hq : ContDiffOn ℝ 2 q U)
    (hVac : MapsTo q U (vacuum a))
    (hHarm : ∀ x ∈ U, (↑(laplacian q x) : Tensor) = harmonicRhs a q (ClassicalGradient q) x)
    (hEuler : ∀ n, ∀ x ∈ U, (ε n : ℝ)^2 • (↑(laplacian (Q n) x) : Tensor) = bulkGradient a (Q n x))
    (hConv : ConvergesCjLoc 2 U (fun n x => (ε n : ℝ)⁻¹^2 • (Q n x - q x)) P) :
    ∀ x ∈ U,
      let r := vacuumRadius a
      let A : Tensor := q x
      let B : Tensor := P x
      (A*B).trace = -(gradientNormSq (ClassicalGradient q x) / (4*r^2*(a.a4 + 4*a.a6*r^2))) ∧
      (A^2*B).trace = -(gradientTraceMul (ClassicalGradient q) (ClassicalGradient q) A x / (a.a6'*r^4)) ∧
      normalPart a A B = ((A*B).trace / (2*r^2)) • A +
        ((A^2*B).trace / (2*r^4)) • (3 : ℝ) • biaxialQuadratic a A ∧
      laplacian (fun y => tangentPart a (q y) (P y)) x = tangentCorrectionRhs a q P x := by
  intro x hx
  have hP : ContDiffOn ℝ 2 P U := hConv.2.1
  obtain ⟨hNormal, hTangential⟩ :=
    firstCorrection_linearized_force_and_tangent_laplacian a hU ε Q q P hε hQ hq hVac hHarm hEuler hConv x hx
  obtain ⟨h₁, h₂⟩ := firstCorrection_trace_coefficients (ClassicalGradient q) (hVac hx) hNormal
  exact ⟨h₁, h₂, rfl, laplacian_tangentPart_eq_tangentCorrectionRhs a hU hq hP hVac hx (hHarm x hx) hTangential⟩

end Thesis

end
