module

public import Thesis.Foundation.VacuumTarget
public import Thesis.Foundation.WeakGradient

/-! Trace identities for the classical vacuum map equation. -/

public section

open Filter MeasureTheory Set
open scoped BigOperators ContDiff Matrix Matrix.Norms.Frobenius

namespace Thesis

private noncomputable def traceCLM : Tensor →L[ℝ] ℝ :=
  (Matrix.traceLinearMap (Fin 3) ℝ ℝ).toContinuousLinearMap

private theorem coordDeriv_trace {f : Point → Tensor} {x : Point}
    (hf : DifferentiableAt ℝ f x) (j : Fin 3) :
    coordDeriv j (fun y => (f y).trace) x = (coordDeriv j f x).trace := by
  have hd := (traceCLM.hasFDerivAt (x := f x)).comp x hf.hasFDerivAt
  exact DFunLike.congr_fun hd.fderiv (axis j)

private theorem coordDeriv_matrix_mul {f g : Point → Tensor} {x : Point}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (j : Fin 3) :
    coordDeriv j (fun y => f y * g y) x = f x * coordDeriv j g x + coordDeriv j f x * g x := by
  exact DFunLike.congr_fun (hf.hasFDerivAt.mul' hg.hasFDerivAt).fderiv (axis j)

private theorem coordDeriv_coeS0 {u : Point → S0} {x : Point}
    (hu : DifferentiableAt ℝ u x) (j : Fin 3) :
    coordDeriv j (fun y => (u y : Tensor)) x = (coordDeriv j u x : S0).val := by
  have hd := (symmetricTraceless.subtypeL.hasFDerivAt (x := u x)).comp x hu.hasFDerivAt
  exact DFunLike.congr_fun hd.fderiv (axis j)

private theorem differentiableAt_coordDeriv_s0 {u : Point → S0} {x : Point}
    (hu : ContDiffAt ℝ 2 u x) (j : Fin 3) : DifferentiableAt ℝ (coordDeriv j u) x := by
  let ev := ContinuousLinearMap.apply ℝ S0 (axis j)
  have h := ev.differentiableAt (x := fderiv ℝ u x)
  exact h.comp x ((hu.fderiv_right_succ (n := 1)).differentiableAt one_ne_zero)

private theorem coordDeriv_eq_zero_of_eventually_zero {u : Point → ℝ} {x : Point}
    (h : u =ᶠ[nhds x] 0) (j : Fin 3) : coordDeriv j u x = 0 := by
  change u =ᶠ[nhds x] (fun _ : Point => (0 : ℝ)) at h
  unfold coordDeriv
  rw [h.fderiv_eq, fderiv_const_apply, zero_apply]

/-- First derivatives of both constant trace invariants vanish along a
smooth vacuum-valued field. -/
theorem vacuum_field_trace_first {a : BulkCoefficients} {Ω : Set Point}
    (hΩ : IsOpen Ω) {u : Point → S0} (hu : ContDiffOn ℝ 1 u Ω)
    (hN : MapsTo u Ω (vacuum a)) {x : Point} (hx : x ∈ Ω) (j : Fin 3) :
    ((u x : Tensor) * (coordDeriv j u x : S0).val).trace = 0 ∧
      (((u x : Tensor) ^ 2) * (coordDeriv j u x : S0).val).trace = 0 := by
  have hux := ((hu x hx).contDiffAt (hΩ.mem_nhds hx)).differentiableAt one_ne_zero
  let f := vacuumInvariants ∘ u
  have hf : f =ᶠ[nhds x] (fun _ => (2 * vacuumRadius a ^ 2, (0 : ℝ))) := by
    filter_upwards [hΩ.mem_nhds hx] with y hy
    exact Prod.ext (vacuum_traces (hN hy)).1 (vacuum_traces (hN hy)).2
  have hd := ((hasStrictFDerivAt_vacuumInvariants (u x)).hasFDerivAt.comp x hux.hasFDerivAt).fderiv
  change fderiv ℝ f x = _ at hd
  have hd0 : fderiv ℝ f x = 0 := hf.fderiv_eq.trans
    (congrFun (fderiv_const (𝕜 := ℝ) (E := Point) (2 * vacuumRadius a ^ 2, (0 : ℝ))) x)
  have hdx := DFunLike.congr_fun (hd.symm.trans hd0) (axis j)
  change vacuumInvariantDerivative (u x) (coordDeriv j u x) = 0 at hdx
  rw [vacuumInvariantDerivative_apply] at hdx
  constructor
  · have h := congrArg Prod.fst hdx
    change 2 * ((u x : Tensor) * (coordDeriv j u x : S0).val).trace = 0 at h
    linarith only [h]
  · have h := congrArg Prod.snd hdx
    change 3 * (((u x : Tensor) ^ 2) * (coordDeriv j u x : S0).val).trace = 0 at h
    linarith only [h]

/-- Twice differentiating the trace constraints gives the two normal pairings
of the Laplacian. -/
theorem vacuum_field_trace_laplacian {a : BulkCoefficients} {Ω : Set Point}
    (hΩ : IsOpen Ω) {u : Point → S0} (hu : ContDiffOn ℝ 2 u Ω)
    (hN : MapsTo u Ω (vacuum a)) {x : Point} (hx : x ∈ Ω) :
    ((u x : Tensor) * (laplacian u x : S0).val).trace = -gradientNormSq (ClassicalGradient u x) ∧
      (((u x : Tensor) ^ 2) * (laplacian u x : S0).val).trace =
        -2 * gradientTraceMul (ClassicalGradient u) (ClassicalGradient u) (u x : Tensor) x := by
  have hux := (hu x hx).contDiffAt (hΩ.mem_nhds hx)
  have hu1 : ContDiffOn ℝ 1 u Ω := hu.of_le (by norm_num)
  let A : Point → Tensor := fun y => u y
  have hA : DifferentiableAt ℝ A x :=
    (symmetricTraceless.subtypeL.differentiableAt).comp x (hux.differentiableAt two_ne_zero)
  have hpoint (j : Fin 3) :
      ((u x : Tensor) * (coordDeriv j (coordDeriv j u) x : S0).val).trace =
        -frobeniusS0 (coordDeriv j u x) (coordDeriv j u x) ∧
      (((u x : Tensor) ^ 2) * (coordDeriv j (coordDeriv j u) x : S0).val).trace =
        -2 * (((coordDeriv j u x : S0).val * (coordDeriv j u x : S0).val) * (u x : Tensor)).trace := by
    let B : Point → Tensor := fun y => (coordDeriv j u y : S0).val
    have hD := differentiableAt_coordDeriv_s0 hux j
    have hB : DifferentiableAt ℝ B x := (symmetricTraceless.subtypeL.differentiableAt).comp x hD
    have hz1 : (fun y => (A y * B y).trace) =ᶠ[nhds x] 0 := by
      filter_upwards [hΩ.mem_nhds hx] with y hy
      exact (vacuum_field_trace_first hΩ hu1 hN hy j).1
    have hz2 : (fun y => (A y ^ 2 * B y).trace) =ᶠ[nhds x] 0 := by
      filter_upwards [hΩ.mem_nhds hx] with y hy
      exact (vacuum_field_trace_first hΩ hu1 hN hy j).2
    have hA' : coordDeriv j A x = B x := coordDeriv_coeS0 (hux.differentiableAt two_ne_zero) j
    have hB' : coordDeriv j B x = (coordDeriv j (coordDeriv j u) x : S0).val := coordDeriv_coeS0 hD j
    have h1 := coordDeriv_eq_zero_of_eventually_zero hz1 j
    rw [coordDeriv_trace (show DifferentiableAt ℝ (fun y => A y * B y) x from hA.mul hB),
      coordDeriv_matrix_mul hA hB, hA', hB', Matrix.trace_add] at h1
    have h2 := coordDeriv_eq_zero_of_eventually_zero hz2 j
    have hAA : DifferentiableAt ℝ (fun y => A y * A y) x := hA.mul hA
    simp only [pow_two] at h2 ⊢
    rw [coordDeriv_trace (show DifferentiableAt ℝ (fun y => (A y * A y) * B y) x from hAA.mul hB),
      coordDeriv_matrix_mul hAA hB,
      coordDeriv_matrix_mul hA hA, hA', hB', Matrix.trace_add, Matrix.add_mul, Matrix.trace_add] at h2
    have cyc1 : (A x * B x * B x).trace = (B x * B x * A x).trace :=
      (Matrix.trace_mul_cycle (B x) (B x) (A x)).symm
    have cyc2 : (B x * A x * B x).trace = (B x * B x * A x).trace :=
      Matrix.trace_mul_cycle (B x) (A x) (B x)
    rw [cyc1, cyc2] at h2
    constructor
    · change (A x * _).trace = _
      rw [frobeniusS0, frobenius, (coordDeriv j u x).transpose_eq]
      linarith only [h1]
    · change (A x * A x * _).trace = -2 * (B x * B x * A x).trace
      linarith only [h2]
  have hsum :
      ((laplacian u x : S0) : Tensor) = ∑ j, (coordDeriv j (coordDeriv j u) x : S0).val := by
    change symmetricTraceless.subtype (∑ j, coordDeriv j (coordDeriv j u) x) = _
    exact map_sum symmetricTraceless.subtype _ _
  constructor
  · rw [hsum, Matrix.mul_sum, Matrix.trace_sum, gradientNormSq, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ => (hpoint j).1
  · rw [hsum, Matrix.mul_sum, Matrix.trace_sum, gradientTraceMul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => (hpoint j).2

/-- The two invariant derivatives determine a normal vector at a vacuum point. -/
theorem eq_vacuumInvariantRightInverse_of_normal {a : BulkCoefficients} {A L : S0}
    (hA : A ∈ vacuum a)
    (hNormal : ∀ B ∈ (vacuumInvariantDerivative A).ker, frobeniusS0 B L = 0) :
    L = vacuumInvariantRightInverse a A (vacuumInvariantDerivative A L) := by
  let p := vacuumInvariantDerivative A L
  let R := vacuumInvariantRightInverse a A p
  let K := L - R
  have hK : K ∈ (vacuumInvariantDerivative A).ker := by
    change vacuumInvariantDerivative A (L - R) = 0
    rw [map_sub, vacuumInvariantRightInverse_isRightInverse hA p, sub_self]
  obtain ⟨h₁, h₂⟩ := (mem_vacuumInvariantKernel_iff A K).1 hK
  have h₁' : inner ℝ (frobeniusCoordinateEquiv K) (frobeniusCoordinateEquiv A) = 0 := by
    rw [real_inner_comm, frobeniusCoordinateEquiv_inner, h₁]
  have h₂' : inner ℝ (frobeniusCoordinateEquiv K) (frobeniusCoordinateEquiv (traceFreeSquare A)) = 0 := by
    rw [real_inner_comm, frobeniusCoordinateEquiv_inner, h₂]
  have hR : inner ℝ (frobeniusCoordinateEquiv K) (frobeniusCoordinateEquiv R) = 0 := by
    change inner ℝ (frobeniusCoordinateEquiv K)
      (frobeniusCoordinateEquiv (vacuumInvariantRightInverse a A p)) = 0
    rw [vacuumInvariantRightInverse_apply, map_add, map_smul, map_smul,
      inner_add_right, real_inner_smul_right, real_inner_smul_right, h₁', h₂']
    simp
  have hL : inner ℝ (frobeniusCoordinateEquiv K) (frobeniusCoordinateEquiv L) = 0 :=
    (frobeniusCoordinateEquiv_inner K L).trans (hNormal K hK)
  have hKK : inner ℝ (frobeniusCoordinateEquiv K) (frobeniusCoordinateEquiv K) = 0 := calc
    _ = inner ℝ (frobeniusCoordinateEquiv K)
        (frobeniusCoordinateEquiv L - frobeniusCoordinateEquiv R) :=
      congrArg (inner ℝ (frobeniusCoordinateEquiv K)) (map_sub frobeniusCoordinateEquiv L R)
    _ = inner ℝ (frobeniusCoordinateEquiv K) (frobeniusCoordinateEquiv L) -
        inner ℝ (frobeniusCoordinateEquiv K) (frobeniusCoordinateEquiv R) := inner_sub_right ..
    _ = 0 := by linarith only [hL, hR]
  have hKzero : K = 0 := frobeniusCoordinateEquiv.injective (by simpa using hKK)
  exact sub_eq_zero.mp hKzero

/-- For a smooth vacuum-valued field, the normal Laplacian is the displayed
quadratic right-hand side with the prescribed material radius. -/
theorem laplacian_eq_harmonicRhs_of_normal {a : BulkCoefficients} {Ω : Set Point}
    (hΩ : IsOpen Ω) {u : Point → S0} (hu : ContDiffOn ℝ 2 u Ω)
    (hN : MapsTo u Ω (vacuum a)) {x : Point} (hx : x ∈ Ω)
    (hNormal : ∀ B ∈ (vacuumInvariantDerivative (u x)).ker,
      frobeniusS0 B (laplacian u x) = 0) :
    (laplacian u x : S0).val = harmonicRhs a u (ClassicalGradient u) x := by
  obtain ⟨h₁, h₂⟩ := vacuum_field_trace_laplacian hΩ hu hN hx
  have heq := congrArg Subtype.val (eq_vacuumInvariantRightInverse_of_normal (hN hx) hNormal)
  rw [vacuumInvariantRightInverse_apply, vacuumInvariantDerivative_apply, h₁, h₂] at heq
  change (laplacian u x : S0).val = _ at heq
  rw [heq]
  change _ • (u x : Tensor) + _ • (traceFreeSquare (u x) : Tensor) = _
  rw [traceFreeSquare_coe_eq_biaxialQuadratic (hN hx), harmonicRhs, sub_eq_add_neg, ← neg_smul]
  have hr := (vacuumRadius_pos a).ne'
  congr 1
  · congr 1
    dsimp only
    field_simp [hr]
    ring
  · congr 1
    dsimp only
    field_simp [hr]

end Thesis

end
