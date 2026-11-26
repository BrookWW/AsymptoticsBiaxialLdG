module

public import Thesis.Variational.BoundaryPohozaev
import Thesis.MeasureGeometry.StressAlgebra
import Mathlib.Analysis.InnerProductSpace.Dual

/-! The boundary normal energy of a classical penalized solution. -/

public section

open Filter MeasureTheory Set Topology
open scoped BigOperators ContDiff ENNReal Matrix Matrix.Norms.Frobenius

set_option autoImplicit false
noncomputable section

namespace Thesis

/-- Contraction of a stress field with the Jacobian of the test field. -/
@[expose] def stressFieldContraction (T : Point → Tensor) (X : Point → Point) (x : Point) : ℝ :=
  ∑ j, ∑ i, coordDeriv j (fun y => X y i) x * T x i j

/-- Outward stress flux tested by an ambient vector field. -/
@[expose] def stressFieldFlux (T : Point → Tensor) (X ν : Point → Point) (x : Point) : ℝ :=
  ∑ j, (∑ i, X x i * T x i j) * ν x j

private theorem contDiffOn_point_coordinate {U : Set Point} {X : Point → Point}
    (hX : ContDiffOn ℝ 1 X U) (i : Fin 3) : ContDiffOn ℝ 1 (fun x => X x i) U := by
  let P : Point →L[ℝ] ℝ := EuclideanSpace.proj i
  exact P.contDiff.comp_contDiffOn hX

private theorem stressField_divergence_eq_contraction
    {U : Set Point} (hU : IsOpen U) (T : Point → Tensor) (X : Point → Point)
    (hX : ContDiffOn ℝ 1 X (closure U))
    (hT : ∀ i j : Fin 3, ContDiffOn ℝ 1 (fun x => T x i j) (closure U))
    (hDiv : ∀ x ∈ U, ∀ i, ∑ j, coordDeriv j (fun y => T y i j) x = 0)
    {x : Point} (hx : x ∈ U) :
    (∑ j, coordDeriv j (fun y => ∑ i, X y i * T y i j) x) = stressFieldContraction T X x := by
  let Xi (i : Fin 3) (y : Point) := X y i
  have hN : closure U ∈ 𝓝 x := mem_of_superset (hU.mem_nhds hx) subset_closure
  have hXd (i : Fin 3) : DifferentiableAt ℝ (Xi i) x :=
    ((contDiffOn_point_coordinate hX i).contDiffAt hN).differentiableAt one_ne_zero
  have hTd (i j : Fin 3) : DifferentiableAt ℝ (fun y => T y i j) x :=
    ((hT i j).contDiffAt hN).differentiableAt one_ne_zero
  have hSum (j : Fin 3) : coordDeriv j (fun y => ∑ i, X y i * T y i j) x =
      ∑ i, (coordDeriv j (Xi i) x * T x i j + X x i * coordDeriv j (fun y => T y i j) x) := by
    let P (i : Fin 3) : Point → ℝ := Xi i * (fun y => T y i j)
    have hP (i : Fin 3) : DifferentiableAt ℝ (P i) x := (hXd i).mul (hTd i j)
    change fderiv ℝ (fun y => ∑ i, P i y) x (axis j) = _
    rw [fderiv_fun_sum fun i _ => hP i, sum_apply]
    apply Finset.sum_congr rfl
    intro i _
    change fderiv ℝ (fun y => Xi i y * T y i j) x (axis j) = _
    rw [fderiv_fun_mul (hXd i) (hTd i j)]
    change _ + T x i j * coordDeriv j (Xi i) x = _
    rw [add_comm, mul_comm (T x i j)]
    rfl
  simp_rw [hSum, Finset.sum_add_distrib]
  rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
    (f := fun j i : Fin 3 => X x i * coordDeriv j (fun y => T y i j) x)]
  simp only [← Finset.mul_sum, hDiv x hx, mul_zero, Finset.sum_const_zero, add_zero,
    stressFieldContraction, Xi]

/-- Integrated stress contraction and boundary flux for an arbitrary
continuously differentiable ambient test field. -/
theorem integral_stressFieldContraction_eq_stressFieldFlux
    (hGG : External.LipschitzGaussGreen) {U : Set Point} {ν X : Point → Point}
    (hGeo : PiecewiseRegularBoundary U ν) (T : Point → Tensor)
    (hX : ContDiffOn ℝ 1 X (closure U))
    (hT : ∀ i j : Fin 3, ContDiffOn ℝ 1 (fun x => T x i j) (closure U))
    (hDiv : ∀ x ∈ U, ∀ i, ∑ j, coordDeriv j (fun y => T y i j) x = 0) :
    let σ : Measure Point := Measure.euclideanHausdorffMeasure 2
    IntegrableOn (stressFieldContraction T X) U volume ∧
      IntegrableOn (stressFieldFlux T X ν) (frontier U) σ ∧
      (∫ x in U, stressFieldContraction T X x) = ∫ x in frontier U, stressFieldFlux T X ν x ∂σ := by
  let F (j : Fin 3) (x : Point) : ℝ := ∑ i, X x i * T x i j
  have hF (j : Fin 3) : ContDiffOn ℝ 1 (F j) (closure U) :=
    ContDiffOn.sum fun i _ => (contDiffOn_point_coordinate hX i).mul (hT i j)
  have hB (j : Fin 3) := hGG U ν hGeo (F j) (hF j) j
  have hIV : IntegrableOn (fun x => ∑ j, coordDeriv j (F j) x) U volume :=
    integrable_finsetSum Finset.univ fun j _ => (hB j).1
  have hIB : IntegrableOn (stressFieldFlux T X ν) (frontier U) (Measure.euclideanHausdorffMeasure 2) :=
    integrable_finsetSum Finset.univ fun j _ => (hB j).2.1
  have hEq : EqOn (fun x => ∑ j, coordDeriv j (F j) x) (stressFieldContraction T X) U :=
    fun _ hx => stressField_divergence_eq_contraction hGeo.isOpen T X hX hT hDiv hx
  refine ⟨hIV.congr ((ae_restrict_mem hGeo.isOpen.measurableSet).mono hEq), hIB, ?_⟩
  calc
    _ = ∫ x in U, ∑ j, coordDeriv j (F j) x :=
      (setIntegral_congr_fun hGeo.isOpen.measurableSet hEq).symm
    _ = ∑ j, ∫ x in U, coordDeriv j (F j) x := integral_finsetSum Finset.univ fun j _ => (hB j).1
    _ = ∑ j, ∫ x in frontier U, F j x * ν x j ∂(Measure.euclideanHausdorffMeasure 2) :=
      Finset.sum_congr rfl fun j _ => (hB j).2.2
    _ = _ := (integral_finsetSum Finset.univ fun j _ => (hB j).2.1).symm

theorem gradientFromColumns_closureGradient (U : Set Point) (Q : Point → S0) (x v : Point) :
    gradientFromColumns (closureGradient U Q x) v = (fderivWithin ℝ Q (closure U) x) v := by
  have hv : (∑ j : Fin 3, v j • axis j) = v := by
    simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply, axis] using
      (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr v
  simp_rw [gradientFromColumns_apply, closureGradient, ← map_smul, ← map_sum, hv]

/-- Along a curve lying locally in the closure, the derivative of the trace
is the interior derivative applied to the curve velocity. -/
theorem hasDerivAt_comp_boundaryCurve {U : Set Point} {Q : Point → S0}
    (hQ : ContDiffOn ℝ 1 Q (closure U))
    {x : Point} (hx : x ∈ frontier U) {γ : ℝ → Point} {v : Point}
    (hPoint : γ 0 = x) (hdγ : HasDerivAt γ v 0) (hCurve : ∀ᶠ t in 𝓝 0, γ t ∈ frontier U) :
    HasDerivAt (Q ∘ γ) (gradientFromColumns (closureGradient U Q x) v) 0 := by
  have hCx : γ 0 ∈ closure U := hPoint.symm ▸ frontier_subset_closure hx
  have hD := (hQ.differentiableOn one_ne_zero (γ 0) hCx).hasFDerivWithinAt
  have hMaps : MapsTo γ (γ ⁻¹' closure U) (closure U) := fun _ ht => ht
  have hNear : γ ⁻¹' closure U ∈ 𝓝 (0 : ℝ) := hCurve.mono fun _ ht => frontier_subset_closure ht
  have hComp := (hD.comp 0 hdγ.hasFDerivAt.hasFDerivWithinAt hMaps).hasFDerivAt hNear
  rw [gradientFromColumns_closureGradient, ← hPoint]
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
    one_smul] using! hComp.hasDerivAt

/-- Two continuously differentiable extensions of the same wall datum have
the same tangential columns. Tangent curves give the wall geometry at `x`. -/
theorem tangentialGradientColumns_eq_of_boundary_trace
    {U : Set Point} {Q b : Point → S0}
    (hQ : ContDiffOn ℝ 1 Q (closure U)) (hb : ContDiffOn ℝ 1 b (closure U))
    (hTrace : EqOn Q b (frontier U)) {x n : Point} (hx : x ∈ frontier U) (hn : ‖n‖ = 1)
    (hCurves : ∀ v : Point, inner ℝ v n = 0 → ∃ γ : ℝ → Point,
      γ 0 = x ∧ HasDerivAt γ v 0 ∧ ∀ᶠ t in 𝓝 0, γ t ∈ frontier U) :
    tangentialGradientColumns (closureGradient U Q x) n =
      tangentialGradientColumns (closureGradient U b x) n := by
  funext i
  let v := axis i - n i • n
  have hNi : inner ℝ (axis i) n = n i := by
    simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, axis, PiLp.single_apply,
      dotProduct, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hTang : inner ℝ v n = 0 := by
    change inner ℝ (axis i - n i • n) n = 0
    rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hn, hNi, one_pow, mul_one, sub_self]
  obtain ⟨γ, hPoint, hDeriv, hNear⟩ := hCurves v hTang
  have hDerivativeQ := hasDerivAt_comp_boundaryCurve hQ hx hPoint hDeriv hNear
  have hDerivativeB := hasDerivAt_comp_boundaryCurve hb hx hPoint hDeriv hNear
  have hTraceCurve : (Q ∘ γ) =ᶠ[𝓝 0] b ∘ γ := hNear.mono fun _ ht => hTrace ht
  have hEq := hDerivativeQ.unique (hDerivativeB.congr_of_eventuallyEq hTraceCurve)
  change gradientFromColumns (closureGradient U Q x) (axis i - n i • n) =
    gradientFromColumns (closureGradient U b x) (axis i - n i • n) at hEq
  simpa only [map_sub, map_smul, gradientFromColumns_axis, tangentialGradientColumns] using hEq

theorem continuousOn_closureGradient_column {U : Set Point} {Q : Point → S0}
    (hUnique : UniqueDiffOn ℝ (closure U)) (hQ : ContDiffOn ℝ 1 Q (closure U)) (i : Fin 3) :
    ContinuousOn (fun x => closureGradient U Q x i) (closure U) :=
  (ContinuousLinearMap.apply ℝ S0 (axis i)).continuous.comp_continuousOn
    (hQ.continuousOn_fderivWithin hUnique le_rfl)

theorem continuousOn_gradientFromColumns {U : Set Point} {D : Point → Gradient}
    (hD : ∀ i : Fin 3, ContinuousOn (fun x => D x i) U)
    {X : Point → Point} (hX : ContDiffOn ℝ 1 X U) :
    ContinuousOn (fun x => gradientFromColumns (D x) (X x)) U := by
  simp_rw [gradientFromColumns_apply]
  exact continuousOn_finsetSum Finset.univ fun i _ =>
    (contDiffOn_point_coordinate hX i).continuousOn.smul (hD i)

theorem continuousOn_gradientNormSq {U : Set Point} {D : Point → Gradient}
    (hD : ∀ i : Fin 3, ContinuousOn (fun x => D x i) U) :
    ContinuousOn (fun x => gradientNormSq (D x)) U := by
  simp_rw [gradientNormSq_eq_sum_norm_sq]
  exact continuousOn_finsetSum Finset.univ fun i _ => (hD i).norm.pow 2

private theorem integrableOn_boundary_of_continuousOn_closure
    {U : Set Point} {ν : Point → Point} (hGeo : PiecewiseRegularBoundary U ν)
    {f : Point → ℝ} (hf : ContinuousOn f (closure U)) :
    IntegrableOn f (frontier U) (Measure.euclideanHausdorffMeasure 2 : Measure Point) := by
  let σ : Measure Point := Measure.euclideanHausdorffMeasure 2
  letI : IsFiniteMeasure (σ.restrict (frontier U)) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact hGeo.area_lt_top⟩
  have hI := (hf.integrableOn_compact (μ := σ.restrict (frontier U)) hGeo.isBounded.isCompact_closure).mono_set
    (frontier_subset_closure : frontier U ⊆ closure U)
  simpa only [IntegrableOn, Measure.restrict_restrict isClosed_frontier.measurableSet, inter_self] using hI

/-- The whole-wall flux against an extension of the unit normal. -/
theorem stressFieldFlux_elasticStress_at_normal
    (a : BulkCoefficients) (ε : ElasticScale) (Q : Point → S0) (D : Point → Gradient)
    (X ν : Point → Point) {x : Point} (hX : X x = ν x) (hν : ‖ν x‖ = 1) (hVac : Q x ∈ vacuum a) :
    stressFieldFlux (fun y => elasticStress a ε (Q y) (D y)) X ν x =
      (1 / 2 : ℝ) * gradientNormSq (tangentialGradientColumns (D x) (ν x)) -
        (1 / 2 : ℝ) * ‖gradientFromColumns (D x) (ν x)‖ ^ 2 := by
  have hx : x - (x - X x) = X x := by abel
  have hFlux : centeredStressFlux (fun y => elasticStress a ε (Q y) (D y)) (x - X x) ν x =
      stressFieldFlux (fun y => elasticStress a ε (Q y) (D y)) X ν x := by
    simp only [centeredStressFlux, hx, stressFieldFlux]
  have h := centeredStressFlux_elasticStress a ε Q D (x - X x) ν x
  rw [hFlux, hx, hX, real_inner_self_eq_norm_sq, hν, one_pow, one_mul, ← norm_sq_eq_frobeniusS0,
    energyDensity, (bulkPotential_eq_zero_iff a (Q x)).2 hVac, mul_zero, add_zero,
    gradientNormSq_eq_normal_add_tangential (D x) (ν x) hν] at h
  linarith only [h]

/-- The normal-trace identity for the entire wall. The tangential energy is
that of the prescribed datum `b`, measured using its interior extension. -/
theorem boundary_normal_energy_identity
    (hGG : External.LipschitzGaussGreen) (a : BulkCoefficients) (ε : ElasticScale)
    {U : Set Point} {ν X : Point → Point} (hGeo : PiecewiseRegularBoundary U ν)
    (hUnique : UniqueDiffOn ℝ (closure U)) (hX : ContDiffOn ℝ 1 X (closure U))
    (hXwall : EqOn X ν (frontier U)) {b : Point → S0} (hb : ContDiffOn ℝ 1 b (closure U))
    (hVac : ∀ x ∈ frontier U, b x ∈ vacuum a)
    (hCurves : ∀ᵐ x ∂((Measure.euclideanHausdorffMeasure 2 : Measure Point).restrict (frontier U)),
      ∀ v : Point, inner ℝ v (ν x) = 0 → ∃ γ : ℝ → Point,
        γ 0 = x ∧ HasDerivAt γ v 0 ∧ ∀ᶠ t in 𝓝 0, γ t ∈ frontier U)
    {Q : Point → S0} (hQ : ContDiffOn ℝ ∞ Q U) (hC : ContDiffOn ℝ 2 Q (closure U))
    (hTrace : EqOn Q b (frontier U))
    (hEuler : ∀ x ∈ U, (ε : ℝ) ^ 2 • (↑(laplacian Q x) : Tensor) = bulkGradient a (Q x)) :
    let σ : Measure Point := Measure.euclideanHausdorffMeasure 2
    let D := closureGradient U Q
    let F := closureGradient U b
    let N (x : Point) := ‖gradientFromColumns (D x) (ν x)‖ ^ 2
    let B (x : Point) := gradientNormSq (tangentialGradientColumns (F x) (ν x))
    let T (x : Point) := elasticStress a ε (Q x) (D x)
    IntegrableOn N (frontier U) σ ∧ IntegrableOn B (frontier U) σ ∧
      IntegrableOn (stressFieldContraction T X) U volume ∧
      (1 / 2 : ℝ) * (∫ x in frontier U, N x ∂σ) =
        (1 / 2 : ℝ) * (∫ x in frontier U, B x ∂σ) - (∫ x in U, stressFieldContraction T X x) := by
  let σ : Measure Point := Measure.euclideanHausdorffMeasure 2
  let D := closureGradient U Q
  let F := closureGradient U b
  let T (x : Point) := elasticStress a ε (Q x) (D x)
  let N' (x : Point) := ‖gradientFromColumns (D x) (X x)‖ ^ 2
  let B' (x : Point) := gradientNormSq (tangentialGradientColumns (F x) (X x))
  let N (x : Point) := ‖gradientFromColumns (D x) (ν x)‖ ^ 2
  let B (x : Point) := gradientNormSq (tangentialGradientColumns (F x) (ν x))
  have hD (i : Fin 3) : ContinuousOn (fun x => D x i) (closure U) :=
    continuousOn_closureGradient_column hUnique (hC.of_le (by norm_num)) i
  have hF (i : Fin 3) : ContinuousOn (fun x => F x i) (closure U) := continuousOn_closureGradient_column hUnique hb i
  have hNc : ContinuousOn N' (closure U) := (continuousOn_gradientFromColumns hD hX).norm.pow 2
  have hBc : ContinuousOn B' (closure U) := by
    apply continuousOn_gradientNormSq
    intro i
    exact (hF i).sub ((contDiffOn_point_coordinate hX i).continuousOn.smul (continuousOn_gradientFromColumns hF hX))
  have hIwN := integrableOn_boundary_of_continuousOn_closure hGeo hNc
  have hIwB := integrableOn_boundary_of_continuousOn_closure hGeo hBc
  have hN : IntegrableOn N (frontier U) σ := hIwN.congr
    ((ae_restrict_mem isClosed_frontier.measurableSet).mono fun x hx => by simp only [N', N, hXwall hx])
  have hB : IntegrableOn B (frontier U) σ := hIwB.congr
    ((ae_restrict_mem isClosed_frontier.measurableSet).mono fun x hx => by simp only [B', B, hXwall hx])
  have hT (i j : Fin 3) : ContDiffOn ℝ 1 (fun x => T x i j) (closure U) :=
    contDiffOn_closureElasticStress_entry a ε hUnique hC i j
  have hDiv : ∀ x ∈ U, ∀ i : Fin 3, ∑ j, coordDeriv j (fun y => T y i j) x = 0 := by
    intro x hx i
    have hEq (j : Fin 3) : (fun y => T y i j) =ᶠ[𝓝 x] (fun y => stressTensor a ε Q y i j) := by
      filter_upwards [hGeo.isOpen.mem_nhds hx] with y hy
      unfold T D
      rw [closureGradient_eq_classicalGradient hGeo.isOpen hC hy, elasticStress_classicalGradient]
    have hc (j : Fin 3) : coordDeriv j (fun y => T y i j) x = coordDeriv j (fun y => stressTensor a ε Q y i j) x :=
      congrArg (fun L : Point →L[ℝ] ℝ => L (axis j)) (hEq j).fderiv_eq
    simp_rw [hc]
    exact stressEnergy_rowDivergence_eq_zero_of_pointwise a ε hGeo.isOpen hQ hEuler x hx i
  obtain ⟨hInt, _, hFlux⟩ := integral_stressFieldContraction_eq_stressFieldFlux hGG hGeo T hX hT hDiv
  have hWall : stressFieldFlux T X ν =ᵐ[σ.restrict (frontier U)] fun x => (1 / 2 : ℝ) * B x - (1 / 2 : ℝ) * N x := by
    filter_upwards [hGeo.normal_ae, hCurves] with x hn hc
    have hx : x ∈ frontier U := hn.1
    have hVacQ : Q x ∈ vacuum a := (hTrace hx).symm ▸ hVac x hx
    have hbEq := tangentialGradientColumns_eq_of_boundary_trace (hC.of_le (by norm_num)) hb hTrace hx hn.2.1 hc
    change tangentialGradientColumns (D x) (ν x) = tangentialGradientColumns (F x) (ν x) at hbEq
    have hNFlux := stressFieldFlux_elasticStress_at_normal a ε Q D X ν (hXwall hx) hn.2.1 hVacQ
    change stressFieldFlux T X ν x = _ at hNFlux
    simpa only [hbEq, N, B] using hNFlux
  refine ⟨hN, hB, hInt, ?_⟩
  have hWallInt := integral_congr_ae hWall
  rw [hWallInt, integral_sub (hB.const_mul _) (hN.const_mul _), integral_const_mul, integral_const_mul] at hFlux
  change (1 / 2 : ℝ) * (∫ x in frontier U, N x ∂σ) =
    (1 / 2 : ℝ) * (∫ x in frontier U, B x ∂σ) - (∫ x in U, stressFieldContraction T X x)
  linarith only [hFlux]

/-- The stress contraction in the normal-energy identity is the energy
times divergence minus the derivative pairing of the gradient columns. -/
theorem stressFieldContraction_elasticStress (a : BulkCoefficients) (ε : ElasticScale)
    (Q : Point → S0) (D : Point → Gradient) (X : Point → Point) (x : Point) :
    stressFieldContraction (fun y => elasticStress a ε (Q y) (D y)) X x =
      energyDensity a ε (Q x) (D x) * (∑ j, coordDeriv j (fun y => X y j) x) -
        ∑ j, ∑ i, coordDeriv j (fun y => X y i) x * frobeniusS0 (D x i) (D x j) := by
  simp only [stressFieldContraction, elasticStress_entry, mul_sub, Finset.sum_sub_distrib, mul_ite,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, ← Finset.sum_mul]
  rw [mul_comm (energyDensity a ε (Q x) (D x))]

private theorem coordDeriv_point_entry {X : Point → Point} {x : Point}
    (hX : DifferentiableAt ℝ X x) (i j : Fin 3) :
    coordDeriv j (fun y => X y i) x = (fderiv ℝ X x (axis j)) i := by
  let L : Point →L[ℝ] ℝ := EuclideanSpace.proj i
  have hd := (L.hasFDerivAt (x := X x)).comp x hX.hasFDerivAt
  exact DFunLike.congr_fun hd.fderiv (axis j)

/-- Uniform pointwise control of volume stress work by the total energy
and the operator norm of the test field derivative. -/
theorem abs_stressFieldContraction_elasticStress_le (a : BulkCoefficients) (ε : ElasticScale)
    (Q : Point → S0) (D : Point → Gradient) {X : Point → Point} {x : Point}
    (hX : DifferentiableAt ℝ X x) :
    |stressFieldContraction (fun y => elasticStress a ε (Q y) (D y)) X x| ≤
      18 * ‖fderiv ℝ X x‖ * energyDensity a ε (Q x) (D x) := by
  let T := elasticStress a ε (Q x) (D x)
  let e := energyDensity a ε (Q x) (D x)
  have hT : ‖T‖ ≤ 2 * e := (elasticStress_bounds a ε (Q x) (D x)).2.2.1
  have hEntry (i j : Fin 3) : ‖(fderiv ℝ X x (axis j)) i‖ ≤ ‖fderiv ℝ X x‖ := by
    have hN := (fderiv ℝ X x).le_opNorm (axis j)
    have hu : ‖axis j‖ = 1 := by simp [axis]
    rw [hu, mul_one] at hN
    exact (PiLp.norm_apply_le (fderiv ℝ X x (axis j)) i).trans hN
  rw [← Real.norm_eq_abs, stressFieldContraction]
  simp_rw [coordDeriv_point_entry hX]
  calc
    _ ≤ ∑ j : Fin 3, ‖∑ i : Fin 3, (fderiv ℝ X x (axis j)) i * T i j‖ := norm_sum_le _ _
    _ ≤ ∑ _ : Fin 3, ∑ _ : Fin 3, ‖fderiv ℝ X x‖ * (2 * e) := by
      apply Finset.sum_le_sum
      intro j _
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      rw [norm_mul]
      exact mul_le_mul (hEntry i j)
        ((Real.norm_eq_abs _).le.trans ((abs_tensor_entry_le_frobenius_norm T i j).trans hT))
        (norm_nonneg _) (norm_nonneg _)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      norm_num
      ring

/-- A fixed `C¹` extension on a bounded closed domain has uniform value
and derivative bounds; the choice is independent of the solution. -/
theorem exists_field_and_fderiv_bound_on_closedDomain
    {U : Set Point} (hU : IsOpen U) (hBounded : Bornology.IsBounded U)
    (hUnique : UniqueDiffOn ℝ (closure U)) {X : Point → Point} (hX : ContDiffOn ℝ 1 X (closure U)) :
    ∃ L : ℝ, 0 ≤ L ∧ (∀ x ∈ closure U, ‖X x‖ ≤ L) ∧ (∀ x ∈ U, ‖fderiv ℝ X x‖ ≤ L) := by
  have hK := hBounded.isCompact_closure
  obtain ⟨L₁, h₁⟩ := hK.exists_bound_of_continuousOn hX.continuousOn
  obtain ⟨L₂, h₂⟩ := hK.exists_bound_of_continuousOn (hX.continuousOn_fderivWithin hUnique le_rfl)
  let L := max (max L₁ L₂) 0
  refine ⟨L, le_max_right _ _, ?_, ?_⟩
  · intro x hx
    exact (h₁ x hx).trans ((le_max_left _ _).trans (le_max_left _ _))
  · intro x hx
    have hN : closure U ∈ 𝓝 x := mem_of_superset (hU.mem_nhds hx) subset_closure
    have hd := (hX.contDiffAt hN).differentiableAt one_ne_zero
    rw [← fderivWithin_eq_fderiv (uniqueDiffWithinAt_of_mem_nhds hN) hd]
    exact (h₂ x (subset_closure hx)).trans ((le_max_right _ _).trans (le_max_left _ _))

/-- Uniform normal trace bound for the energy-bounded family with a fixed
vacuum wall datum and a fixed extension of the wall normal. -/
theorem exists_uniform_boundary_normal_energy_bound
    (hGG : External.LipschitzGaussGreen) (a : BulkCoefficients)
    {U : Set Point} {ν X : Point → Point} (hGeo : PiecewiseRegularBoundary U ν)
    (hUnique : UniqueDiffOn ℝ (closure U)) (hX : ContDiffOn ℝ 1 X (closure U))
    (hXwall : EqOn X ν (frontier U)) {b : Point → S0} (hb : ContDiffOn ℝ 1 b (closure U))
    (hVac : ∀ x ∈ frontier U, b x ∈ vacuum a)
    (hCurves : ∀ᵐ x ∂((Measure.euclideanHausdorffMeasure 2 : Measure Point).restrict (frontier U)),
      ∀ v : Point, inner ℝ v (ν x) = 0 → ∃ γ : ℝ → Point,
        γ 0 = x ∧ HasDerivAt γ v 0 ∧ ∀ᶠ t in 𝓝 0, γ t ∈ frontier U)
    {C₀ : ℝ} (hC₀ : 0 ≤ C₀) :
    ∃ L : ℝ, 0 ≤ L ∧ (∀ x ∈ closure U, ‖X x‖ ≤ L) ∧ (∀ x ∈ U, ‖fderiv ℝ X x‖ ≤ L) ∧
      ∀ (ε : ElasticScale) (Q : Point → S0),
        ContDiffOn ℝ ∞ Q U → ContDiffOn ℝ 2 Q (closure U) → EqOn Q b (frontier U) →
        (∀ x ∈ U, (ε : ℝ) ^ 2 • (↑(laplacian Q x) : Tensor) = bulkGradient a (Q x)) →
        energy a ε U Q (closureGradient U Q) ≤ ENNReal.ofReal C₀ →
        let σ : Measure Point := Measure.euclideanHausdorffMeasure 2
        let N (x : Point) := ‖gradientFromColumns (closureGradient U Q x) (ν x)‖ ^ 2
        let B (x : Point) := gradientNormSq (tangentialGradientColumns (closureGradient U b x) (ν x))
        IntegrableOn N (frontier U) σ ∧
          (∫ x in frontier U, N x ∂σ) ≤ (∫ x in frontier U, B x ∂σ) + 36 * L * C₀ ∧
          ∀ c : Point, ∀ r : ℝ, (∫ x in frontier U ∩ Metric.ball c r, N x ∂σ) ≤
            (∫ x in frontier U, B x ∂σ) + 36 * L * C₀ := by
  obtain ⟨L, hL, hValue, hDer⟩ := exists_field_and_fderiv_bound_on_closedDomain hGeo.isOpen
    hGeo.isBounded hUnique hX
  refine ⟨L, hL, hValue, hDer, ?_⟩
  intro ε Q hQ hC hTrace hEuler hE
  let σ : Measure Point := Measure.euclideanHausdorffMeasure 2
  let D := closureGradient U Q
  let N (x : Point) := ‖gradientFromColumns (D x) (ν x)‖ ^ 2
  let B (x : Point) := gradientNormSq (tangentialGradientColumns (closureGradient U b x) (ν x))
  let e (x : Point) := energyDensity a ε (Q x) (D x)
  let T (x : Point) := elasticStress a ε (Q x) (D x)
  obtain ⟨hN, _, hInt, hId⟩ := boundary_normal_energy_identity hGG a ε hGeo hUnique hX hXwall hb
    hVac hCurves hQ hC hTrace hEuler
  have hD (i : Fin 3) : ContinuousOn (fun x => D x i) (closure U) :=
    continuousOn_closureGradient_column hUnique (hC.of_le (by norm_num)) i
  have hEC : ContinuousOn e (closure U) := by
    simp only [e, energyDensity]
    exact (continuousOn_const.mul (continuousOn_gradientNormSq hD)).add (continuousOn_const.mul
      ((contDiff_bulkPotential a).continuous.comp_continuousOn hC.continuousOn))
  have he : IntegrableOn e U volume :=
    (hEC.integrableOn_compact (μ := volume) hGeo.isBounded.isCompact_closure).mono_set subset_closure
  have hPos (x : Point) : 0 ≤ e x := by
    have h := (elasticStress_bounds a ε (Q x) (D x)).2.2.1
    change ‖T x‖ ≤ 2 * e x at h
    linarith only [h, norm_nonneg (T x)]
  have hEN : (∫ x in U, e x) ≤ C₀ := by
    have hRepr := ofReal_integral_eq_lintegral_ofReal he (Eventually.of_forall hPos)
    apply (ENNReal.ofReal_le_ofReal_iff hC₀).1
    rw [hRepr]
    exact hE
  have hContr : (-18 * L) * (∫ x in U, e x) ≤ ∫ x in U, stressFieldContraction T X x := by
    rw [← integral_const_mul]
    apply integral_mono_ae (he.const_mul _) hInt
    filter_upwards [ae_restrict_mem hGeo.isOpen.measurableSet] with x hx
    have hXd := (hX.contDiffAt (mem_of_superset (hGeo.isOpen.mem_nhds hx) subset_closure)).differentiableAt one_ne_zero
    have hBd : |stressFieldContraction T X x| ≤ 18 * ‖fderiv ℝ X x‖ * e x :=
      abs_stressFieldContraction_elasticStress_le a ε Q D hXd
    have hLx := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hDer x hx) (by norm_num : (0 : ℝ) ≤ 18)) (hPos x)
    linarith only [hBd, hLx, neg_abs_le (stressFieldContraction T X x)]
  have hF := mul_le_mul_of_nonneg_left hEN (mul_nonneg (by norm_num : (0 : ℝ) ≤ 18) hL)
  have hGlobal : (∫ x in frontier U, N x ∂σ) ≤ (∫ x in frontier U, B x ∂σ) + 36 * L * C₀ := by
    change (1 / 2 : ℝ) * (∫ x in frontier U, N x ∂σ) =
      (1 / 2 : ℝ) * (∫ x in frontier U, B x ∂σ) - (∫ x in U, stressFieldContraction T X x) at hId
    linarith only [hId, hContr, hF]
  refine ⟨hN, hGlobal, fun c r => ?_⟩
  exact (setIntegral_mono_set hN (Eventually.of_forall fun _ => sq_nonneg _) (Eventually.of_forall
    fun _ hx => hx.1)).trans hGlobal

/-- The signed local wall chart has a fixed unit direction in which
its defining function has derivative minus one. -/
theorem exists_local_smooth_defining_function_and_unit_direction
    {U : Set Point} (hU : IsSmoothDomain U) {a : Point} (ha : a ∈ frontier U) :
    ∃ (r : ℝ) (φ : Point → ℝ) (n : Point → Point) (t : Point → ℝ) (w : Point),
      0 < r ∧ ContDiff ℝ ∞ φ ∧ ContDiff ℝ ∞ n ∧
      U ∩ Metric.ball a r = {y | φ y < 0} ∩ Metric.ball a r ∧
      ‖w‖ = 1 ∧ (∀ y, fderiv ℝ φ y w = -1) ∧
      (∀ y, 1 ≤ t y) ∧ (∀ y, fderiv ℝ φ y = t y • innerSL ℝ (n y)) ∧
      ∀ y ∈ frontier U ∩ Metric.ball a r, HasRegularOutwardNormalAt U y (n y) := by
  obtain ⟨r, A, g, hr, hg, _, hChart⟩ := hU.2 a ha
  let E : Point ≃L[ℝ] Plane × EuclideanSpace ℝ (Fin 1) :=
    EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 2) (m := 1)
  let P : Point →L[ℝ] Plane := (ContinuousLinearMap.fst ℝ Plane (EuclideanSpace ℝ (Fin 1))).comp
    E.toContinuousLinearMap
  let H : Point →L[ℝ] ℝ := EuclideanSpace.proj (2 : Fin 3)
  have hP (z : Point) : P z = WithLp.toLp 2 ![z 0, z 1] := by
    ext i
    fin_cases i <;> rfl
  let Y (y : Point) := A (y - a)
  let φ (y : Point) := g (P (Y y)) - H (Y y)
  have hYS : ContDiff ℝ ∞ Y := A.toContinuousLinearEquiv.toContinuousLinearMap.contDiff.comp
    (contDiff_id.sub contDiff_const)
  have hφ : ContDiff ℝ ∞ φ := (hg.comp (P.contDiff.comp hYS)).sub (H.contDiff.comp hYS)
  have hDef : U ∩ Metric.ball a r = {y | φ y < 0} ∩ Metric.ball a r := by
    change U ∩ Metric.ball a r = {y | g (P (Y y)) - (Y y) 2 < 0} ∩ Metric.ball a r
    simpa only [hP, Y, sub_neg] using hChart
  let w := A.symm (axis 2)
  have hPY : P (axis 2) = 0 := by
    rw [hP]
    ext i
    fin_cases i <;> rfl
  have hHY : H (axis 2) = 1 := by rfl
  have hLine (y : Point) (t : ℝ) : φ (y + t • w) = φ y - t := by
    have hTrans : Y (y + t • w) = Y y + t • axis 2 := by
      simp only [Y, w, map_sub, map_add, map_smul, A.apply_symm_apply]
      abel
    simp only [φ, hTrans, map_add, map_smul, hPY, smul_zero, add_zero, hHY, smul_eq_mul, mul_one]
    ring
  have hVertical (y : Point) : (fderiv ℝ φ y) w = -1 := by
    have hy : HasDerivAt (fun t : ℝ => y + t • w) w 0 :=
      by simpa only [id_eq, one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add y
    have hdφ : HasFDerivAt φ (fderiv ℝ φ y) (y + (0 : ℝ) • w) := by
      simpa only [zero_smul, add_zero] using (hφ.differentiable (by simp) y).hasFDerivAt
    have hf : HasDerivAt (fun t : ℝ => φ (y + t • w)) ((fderiv ℝ φ y) w) 0 := by
      exact hdφ.comp_hasDerivAt 0 hy
    have hl : HasDerivAt (fun t : ℝ => φ y - t) (-1) 0 := by
      simpa only [Pi.sub_def, id_eq, zero_sub] using!
        (hasDerivAt_const 0 (φ y)).sub (hasDerivAt_id 0)
    exact hf.unique (hl.congr_of_eventuallyEq (Eventually.of_forall (hLine y)))
  let J : Point ≃ₗᵢ[ℝ] (Point →L[ℝ] ℝ) := InnerProductSpace.toDual ℝ Point
  let V (y : Point) := J.symm (fderiv ℝ φ y)
  have hVS : ContDiff ℝ ∞ V := J.symm.toContinuousLinearEquiv.toContinuousLinearMap.contDiff.comp
    (hφ.fderiv_right (by simp))
  have hV (y : Point) : V y ≠ 0 := by
    intro hz
    have hJ : J (V y) = fderiv ℝ φ y := J.apply_symm_apply _
    rw [hz, map_zero] at hJ
    have h := hVertical y
    rw [← hJ, zero_apply] at h
    norm_num at h
  let n (y : Point) := ‖V y‖⁻¹ • V y
  have hnS : ContDiff ℝ ∞ n := ((hVS.norm ℝ hV).inv (fun y => norm_ne_zero_iff.mpr (hV y))).smul hVS
  have hn (y : Point) : ‖n y‖ = 1 := by
    dsimp only [n]
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hV y))]
  have hw : ‖w‖ = 1 := by
    change ‖A.symm (axis 2)‖ = 1
    rw [A.symm.norm_map]
    simp [axis]
  have hFactor (y : Point) : 1 ≤ ‖V y‖ := by
    have hBound := (fderiv ℝ φ y).le_opNorm w
    have hJV : J (V y) = fderiv ℝ φ y := J.apply_symm_apply _
    rwa [hVertical, norm_neg, norm_one, hw, mul_one, ← hJV, J.norm_map] at hBound
  have hD (y : Point) : fderiv ℝ φ y = ‖V y‖ • innerSL ℝ (n y) := by
    ext z
    have hInner : inner ℝ (V y) z = (fderiv ℝ φ y) z := InnerProductSpace.toDual_symm_apply
    simp only [smul_apply, smul_eq_mul, innerSL_apply_apply, n, real_inner_smul_left,
      ← mul_assoc, mul_inv_cancel₀ (norm_ne_zero_iff.mpr (hV y)), one_mul, hInner]
  refine ⟨r, φ, n, fun y => ‖V y‖, w, hr, hφ, hnS, hDef, hw, hVertical, hFactor, hD, ?_⟩
  intro y hy
  have hφZero : φ y = 0 := by
    rcases lt_trichotomy (φ y) 0 with hneg | heq | hpos
    · have hmem : y ∈ U ∩ Metric.ball a r := hDef.symm ▸ ⟨hneg, hy.2⟩
      exact (hy.1.2 (hU.1.1.interior_eq.symm ▸ hmem.1)).elim
    · exact heq
    · let O := φ ⁻¹' Ioi (0 : ℝ) ∩ Metric.ball a r
      have hO : IsOpen O := (isOpen_Ioi.preimage hφ.continuous).inter Metric.isOpen_ball
      have hDis : O ∩ U = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro z hz
        have hzL : z ∈ U ∩ Metric.ball a r := ⟨hz.2, hz.1.2⟩
        have hzR : φ z < 0 := (show z ∈ {x | φ x < 0} ∩ Metric.ball a r from hDef ▸ hzL).1
        exact (lt_asymm hzR hz.1.1).elim
      have hM : y ∈ closure (O ∩ U) := hO.inter_closure ⟨⟨hpos, hy.2⟩, hy.1.1⟩
      rw [hDis, closure_empty] at hM
      exact hM.elim
  obtain ⟨s, hs, hSub⟩ := Metric.mem_nhds_iff.mp (Metric.isOpen_ball.mem_nhds hy.2)
  refine ⟨hy.1, hn y, s, φ, ‖V y‖, hs, (hφ.of_le (by simp)).contDiffOn, hφZero,
    norm_pos_iff.mpr (hV y), ?_, ?_⟩
  · rw [← hD y]
    exact (hφ.differentiable (by simp) y).hasFDerivAt
  · ext z
    constructor
    · intro hz
      exact ⟨(show z ∈ {x | φ x < 0} ∩ Metric.ball a r from hDef ▸ ⟨hz.1, hSub hz.2⟩).1, hz.2⟩
    · intro hz
      exact ⟨(show z ∈ U ∩ Metric.ball a r from hDef.symm ▸ ⟨hz.1, hSub hz.2⟩).1, hz.2⟩

/-- A smooth epigraph chart gives a signed smooth defining function and its
normalized outward gradient. The derivative factor is at least one. -/
theorem exists_local_smooth_defining_function_and_normal_field
    {U : Set Point} (hU : IsSmoothDomain U) {a : Point} (ha : a ∈ frontier U) :
    ∃ (r : ℝ) (φ : Point → ℝ) (n : Point → Point) (t : Point → ℝ),
      0 < r ∧ ContDiff ℝ ∞ φ ∧ ContDiff ℝ ∞ n ∧
      U ∩ Metric.ball a r = {y | φ y < 0} ∩ Metric.ball a r ∧
      (∀ y, 1 ≤ t y) ∧ (∀ y, fderiv ℝ φ y = t y • innerSL ℝ (n y)) ∧
      ∀ y ∈ frontier U ∩ Metric.ball a r, HasRegularOutwardNormalAt U y (n y) := by
  obtain ⟨r, φ, n, t, _, hr, hφ, hn, hDef, _, _, hFactor, hD, hWall⟩ :=
    exists_local_smooth_defining_function_and_unit_direction hU ha
  exact ⟨r, φ, n, t, hr, hφ, hn, hDef, hFactor, hD, hWall⟩

/-- A smooth epigraph chart gives an ambient smooth unit vector field whose
restriction to the wall in the chart is its regular outward normal. -/
theorem exists_local_smooth_outward_normal_field {U : Set Point} (hU : IsSmoothDomain U)
    {a : Point} (ha : a ∈ frontier U) :
    ∃ (r : ℝ) (n : Point → Point), 0 < r ∧ ContDiff ℝ ∞ n ∧
      ∀ y ∈ frontier U ∩ Metric.ball a r, HasRegularOutwardNormalAt U y (n y) := by
  obtain ⟨r, _, n, _, hr, _, hn, _, _, _, hWall⟩ :=
    exists_local_smooth_defining_function_and_normal_field hU ha
  exact ⟨r, n, hr, hn, hWall⟩

end Thesis

end
