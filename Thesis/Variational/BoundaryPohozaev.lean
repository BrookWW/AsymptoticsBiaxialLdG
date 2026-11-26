module

public import Thesis.Variational.Pohozaev
public import Thesis.MeasureGeometry.StressBounds
public import Mathlib.Geometry.Euclidean.Volume.Measure
import StratificationTheory.Foundation.SphereSurfaceIntegral

/-! Boundary stress flux for an intersection with a Euclidean ball. -/

public section

open Filter MeasureTheory Set Topology
open scoped BigOperators ContDiff ENNReal NNReal Matrix Matrix.Norms.Frobenius

set_option autoImplicit false
noncomputable section

namespace Thesis

/-- Local epigraph charts defining a Lipschitz boundary. -/
@[expose] def HasLocallyLipschitzBoundary (V : Set Point) : Prop :=
  ∀ x ∈ frontier V,
    ∃ (r : ℝ) (A : Point ≃ₗᵢ[ℝ] Point) (g : Plane → ℝ) (L : ℝ≥0),
      0 < r ∧ LipschitzOnWith L g (Metric.ball 0 r) ∧ g 0 = 0 ∧
      V ∩ Metric.ball x r =
        {y | let z := A (y - x); g (WithLp.toLp 2 ![z 0, z 1]) < z 2} ∩ Metric.ball x r

/-- The outward unit normal at a point with a local regular defining function. -/
@[expose] def HasRegularOutwardNormalAt (V : Set Point) (x ν : Point) : Prop :=
  x ∈ frontier V ∧ ‖ν‖ = 1 ∧
    ∃ (r : ℝ) (φ : Point → ℝ) (t : ℝ),
      0 < r ∧ ContDiffOn ℝ 1 φ (Metric.ball x r) ∧ φ x = 0 ∧ 0 < t ∧
        HasFDerivAt φ (t • innerSL ℝ ν) x ∧
        V ∩ Metric.ball x r = {y | φ y < 0} ∩ Metric.ball x r

/-- A bounded Lipschitz domain whose boundary is regular up to a surface-null set. -/
structure PiecewiseRegularBoundary (V : Set Point) (ν : Point → Point) : Prop where
  isOpen : IsOpen V
  isBounded : Bornology.IsBounded V
  lipschitz : HasLocallyLipschitzBoundary V
  area_lt_top : Measure.euclideanHausdorffMeasure 2 (frontier V) < ⊤
  normal_measurable :
    AEMeasurable ν ((Measure.euclideanHausdorffMeasure 2).restrict (frontier V))
  normal_ae : ∀ᵐ x ∂((Measure.euclideanHausdorffMeasure 2).restrict (frontier V)),
    HasRegularOutwardNormalAt V x (ν x)

/-- Gauss–Green applied to one coordinate of a continuously differentiable field.
The volume and flux integrals use Lebesgue and Euclidean surface measure. -/
@[expose] def External.LipschitzGaussGreen : Prop :=
  ∀ (V : Set Point) (ν : Point → Point), PiecewiseRegularBoundary V ν →
    ∀ (f : Point → ℝ), ContDiffOn ℝ 1 f (closure V) → ∀ j : Fin 3,
      IntegrableOn (coordDeriv j f) V volume ∧
        IntegrableOn (fun x => f x * ν x j) (frontier V) (Measure.euclideanHausdorffMeasure 2) ∧
        (∫ x in V, coordDeriv j f x) =
          ∫ x in frontier V, f x * ν x j ∂(Measure.euclideanHausdorffMeasure 2)

/-- Outward stress flux tested by the centered position vector. -/
@[expose] def centeredStressFlux (T : Point → Tensor) (c : Point)
    (ν : Point → Point) (x : Point) : ℝ :=
  ∑ j, (∑ i, (x - c) i * T x i j) * ν x j

private theorem coordDeriv_centeredCoord (c x : Point) (i j : Fin 3) :
    coordDeriv j (fun y : Point => (y - c) i) x = if j = i then 1 else 0 := by
  let L : Point →L[ℝ] ℝ := EuclideanSpace.proj i
  have h : HasFDerivAt (fun y : Point => (y - c) i) L x :=
    (L.hasFDerivAt (x := x)).sub_const (L c)
  rw [coordDeriv, h.fderiv]
  change (EuclideanSpace.single j (1 : ℝ) : Point) i = _
  simp only [PiLp.single_apply, eq_comm]

private theorem centeredStress_divergence_trace {V : Set Point} (hV : IsOpen V)
    (T : Point → Tensor) (hT : ∀ i j : Fin 3,
      ContDiffOn ℝ 1 (fun x => T x i j) (closure V))
    (hDiv : ∀ x ∈ V, ∀ i, ∑ j, coordDeriv j (fun y => T y i j) x = 0)
    (c x : Point) (hx : x ∈ V) :
    (∑ j, coordDeriv j (fun y : Point => ∑ i, (y - c) i * T y i j) x) = (T x).trace := by
  let X (i : Fin 3) : Point → ℝ := fun y => (y - c) i
  have hX (i : Fin 3) : DifferentiableAt ℝ (X i) x := by
    change DifferentiableAt ℝ (fun y : Point => (EuclideanSpace.proj i) (y - c)) x
    fun_prop
  have hT' (i j : Fin 3) : DifferentiableAt ℝ (fun y => T y i j) x :=
    (((hT i j) x (subset_closure hx)).contDiffAt
      (mem_of_superset (hV.mem_nhds hx) subset_closure)).differentiableAt one_ne_zero
  have hSum (j : Fin 3) :
      coordDeriv j (fun y : Point => ∑ i, (y - c) i * T y i j) x =
        ∑ i, ((if j = i then 1 else 0) * T x i j +
          (x - c) i * coordDeriv j (fun y => T y i j) x) := by
    let Y (i : Fin 3) : Point → ℝ := X i * (fun y => T y i j)
    have hY (i : Fin 3) : DifferentiableAt ℝ (Y i) x := (hX i).mul (hT' i j)
    change fderiv ℝ (fun y => ∑ i, Y i y) x (axis j) = _
    rw [fderiv_fun_sum fun i _ => hY i, sum_apply]
    apply Finset.sum_congr rfl
    intro i _
    change fderiv ℝ (fun y => X i y * T y i j) x (axis j) = _
    rw [fderiv_fun_mul (hX i) (hT' i j)]
    change _ + T x i j * coordDeriv j (X i) x = _
    rw [coordDeriv_centeredCoord, add_comm, mul_comm (T x i j)]
    rfl
  simp_rw [hSum, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]
  rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
    (f := fun j i : Fin 3 => (x - c) i * coordDeriv j (fun y => T y i j) x)]
  simp only [← Finset.mul_sum, hDiv x hx, mul_zero, Finset.sum_const_zero, add_zero,
    Matrix.trace, Matrix.diag_apply]

/-- A row-divergence-free stress has centered outward flux equal to its
integrated trace. The input is the geometric Gauss–Green theorem. -/
theorem integral_trace_eq_centeredStressFlux
    (hGG : External.LipschitzGaussGreen) {V : Set Point} {ν : Point → Point}
    (hGeo : PiecewiseRegularBoundary V ν) (T : Point → Tensor)
    (hT : ∀ i j : Fin 3, ContDiffOn ℝ 1 (fun x => T x i j) (closure V))
    (hDiv : ∀ x ∈ V, ∀ i, ∑ j, coordDeriv j (fun y => T y i j) x = 0)
    (c : Point) :
    IntegrableOn (centeredStressFlux T c ν) (frontier V) (Measure.euclideanHausdorffMeasure 2) ∧
      (∫ x in V, (T x).trace) =
        ∫ x in frontier V, centeredStressFlux T c ν x ∂(Measure.euclideanHausdorffMeasure 2) := by
  let F (j : Fin 3) (x : Point) : ℝ := ∑ i, (x - c) i * T x i j
  have hF (j : Fin 3) : ContDiffOn ℝ 1 (F j) (closure V) := by
    apply ContDiffOn.sum
    intro i _
    refine (ContDiff.contDiffOn ?_).mul (hT i j)
    change ContDiff ℝ 1 (fun x : Point => (EuclideanSpace.proj i) (x - c))
    fun_prop
  have hGB (j : Fin 3) := hGG V ν hGeo (F j) (hF j) j
  have hI := integrable_finsetSum Finset.univ
    (fun j _ => (hGB j).2.1)
  refine ⟨hI, ?_⟩
  calc
    _ = ∫ x in V, ∑ j, coordDeriv j (F j) x :=
      setIntegral_congr_fun hGeo.isOpen.measurableSet fun x hx =>
        (centeredStress_divergence_trace hGeo.isOpen T hT hDiv c x hx).symm
    _ = ∑ j, ∫ x in V, coordDeriv j (F j) x :=
      integral_finsetSum Finset.univ fun j _ => (hGB j).1
    _ = ∑ j, ∫ x in frontier V, F j x * ν x j ∂(Measure.euclideanHausdorffMeasure 2) :=
      Finset.sum_congr rfl fun j _ => (hGB j).2.2
    _ = _ := (integral_finsetSum Finset.univ fun j _ => (hGB j).2.1).symm

private theorem sphere_physical_patches_subset_frontier {U : Set Point} (hU : IsOpen U) (x : Point)
    {r : ℝ} (hr : 0 < r) :
    U ∩ Metric.sphere x r ⊆ frontier (U ∩ Metric.ball x r) ∧
      frontier U ∩ Metric.ball x r ⊆ frontier (U ∩ Metric.ball x r) := by
  rw [frontier, (hU.inter Metric.isOpen_ball).interior_eq]
  constructor
  · intro y hy
    have hS : y ∈ frontier (Metric.ball x r) := by
      rw [frontier_ball x hr.ne']
      exact hy.2
    have hC : y ∈ closure (U ∩ Metric.ball x r) := hU.inter_closure ⟨hy.1, hS.1⟩
    refine ⟨hC, fun h => hS.2 ?_⟩
    rw [Metric.isOpen_ball.interior_eq]
    exact h.2
  · intro y hy
    have hC : y ∈ closure (U ∩ Metric.ball x r) := Metric.isOpen_ball.closure_inter ⟨hy.1.1, hy.2⟩
    refine ⟨hC, fun h => hy.1.2 ?_⟩
    rw [hU.interior_eq]
    exact h.1

theorem frontier_slice_subset {U : Set Point} (hU : IsOpen U) (x : Point)
    {r : ℝ} (hr : 0 < r) :
    frontier (U ∩ Metric.ball x r) ⊆
      (U ∩ Metric.sphere x r) ∪ (frontier U ∩ Metric.ball x r) ∪ (frontier U ∩ Metric.sphere x r) := by
  intro y hy
  have hCl := closure_inter_subset_inter_closure U (Metric.ball x r) hy.1
  have hNot : y ∉ U ∩ Metric.ball x r := by
    intro h
    exact hy.2 ((hU.inter Metric.isOpen_ball).interior_eq.symm ▸ h)
  by_cases hUy : y ∈ U
  · apply Or.inl
    apply Or.inl
    refine ⟨hUy, ?_⟩
    rw [← frontier_ball x hr.ne', frontier, Metric.isOpen_ball.interior_eq]
    exact ⟨hCl.2, fun h => hNot ⟨hUy, h⟩⟩
  · have hFr : y ∈ frontier U := by
      rw [frontier, hU.interior_eq]
      exact ⟨hCl.1, hUy⟩
    by_cases hyB : y ∈ Metric.ball x r
    · exact Or.inl (Or.inr ⟨hFr, hyB⟩)
    · refine Or.inr ⟨hFr, ?_⟩
      rw [← frontier_ball x hr.ne', frontier, Metric.isOpen_ball.interior_eq]
      exact ⟨hCl.2, hyB⟩

private theorem restrict_frontier_eq_patches {U : Set Point} (hU : IsOpen U) (x : Point)
    {r : ℝ} (hr : 0 < r) {μ : Measure Point} (hSeam : μ (frontier U ∩ Metric.sphere x r) = 0) :
    μ.restrict (frontier (U ∩ Metric.ball x r)) =
      μ.restrict ((U ∩ Metric.sphere x r) ∪ (frontier U ∩ Metric.ball x r)) := by
  have hNot : ∀ᵐ y ∂μ, y ∉ frontier U ∩ Metric.sphere x r := by
    rw [ae_iff]
    have hSet : {y | ¬ y ∉ frontier U ∩ Metric.sphere x r} = frontier U ∩ Metric.sphere x r :=
      Set.ext fun _ => not_not
    rwa [hSet]
  obtain ⟨hS, hT⟩ := sphere_physical_patches_subset_frontier hU x hr
  apply Measure.restrict_congr_set
  filter_upwards [hNot] with y hy
  apply propext
  change y ∈ frontier (U ∩ Metric.ball x r) ↔ y ∈ (U ∩ Metric.sphere x r) ∪ (frontier U ∩ Metric.ball x r)
  exact ⟨fun h => (frontier_slice_subset hU x hr h).resolve_right hy, fun h => h.elim (fun h' => hS h') (fun h' => hT h')⟩

/-- Centered stress flux for the two actual boundary patches of an intersection
with a ball. The regular normals are the radial unit vector and the original
outward normal, respectively. The seam has zero Euclidean surface measure. -/
theorem integral_trace_eq_centeredStressFlux_patches
    (hGG : External.LipschitzGaussGreen) {U : Set Point} (hU : IsOpen U)
    (c : Point) {r : ℝ} (hr : 0 < r) {ν ν' : Point → Point}
    (hGeo : PiecewiseRegularBoundary (U ∩ Metric.ball c r) ν')
    (hSeam : Measure.euclideanHausdorffMeasure 2 (frontier U ∩ Metric.sphere c r) = 0)
    (hRad : EqOn ν' (fun x => r⁻¹ • (x - c)) (U ∩ Metric.sphere c r))
    (hPhys : EqOn ν' ν (frontier U ∩ Metric.ball c r))
    (T : Point → Tensor)
    (hT : ∀ i j : Fin 3, ContDiffOn ℝ 1 (fun x => T x i j) (closure (U ∩ Metric.ball c r)))
    (hDiv : ∀ x ∈ U ∩ Metric.ball c r, ∀ i, ∑ j, coordDeriv j (fun y => T y i j) x = 0) :
    let σ : Measure Point := Measure.euclideanHausdorffMeasure 2
    let S := U ∩ Metric.sphere c r
    let W := frontier U ∩ Metric.ball c r
    let f := centeredStressFlux T c (fun x => r⁻¹ • (x - c))
    let g := centeredStressFlux T c ν
    IntegrableOn f S σ ∧ IntegrableOn g W σ ∧
      (∫ x in U ∩ Metric.ball c r, (T x).trace) = (∫ x in S, f x ∂σ) + (∫ x in W, g x ∂σ) := by
  let σ : Measure Point := Measure.euclideanHausdorffMeasure 2
  let S := U ∩ Metric.sphere c r
  let W := frontier U ∩ Metric.ball c r
  let F := centeredStressFlux T c ν'
  let f := centeredStressFlux T c (fun x => r⁻¹ • (x - c))
  let g := centeredStressFlux T c ν
  have hSm : MeasurableSet S := hU.measurableSet.inter Metric.isClosed_sphere.measurableSet
  have hWm : MeasurableSet W := isClosed_frontier.measurableSet.inter Metric.isOpen_ball.measurableSet
  have hDis : Disjoint S W := by
    rw [Set.disjoint_left]
    intro y hy hy'
    have hyn : y ∉ interior U := hy'.1.2
    exact hyn (hU.interior_eq.symm ▸ hy.1)
  have hEqS : EqOn F f S := fun y hy => by simp only [F, f, centeredStressFlux, hRad hy]
  have hEqW : EqOn F g W := fun y hy => by simp only [F, g, centeredStressFlux, hPhys hy]
  obtain ⟨hI, hE⟩ := integral_trace_eq_centeredStressFlux hGG hGeo T hT hDiv c
  obtain ⟨hS, hW⟩ := sphere_physical_patches_subset_frontier hU c hr
  have hIS : IntegrableOn F S σ := hI.mono_set hS
  have hIW : IntegrableOn F W σ := hI.mono_set hW
  refine ⟨hIS.congr ((ae_restrict_mem hSm).mono hEqS),
    hIW.congr ((ae_restrict_mem hWm).mono hEqW), ?_⟩
  change (∫ x in U ∩ Metric.ball c r, (T x).trace) = (∫ x in S, f x ∂σ) + (∫ x in W, g x ∂σ)
  calc
    _ = ∫ x in frontier (U ∩ Metric.ball c r), F x ∂σ := hE
    _ = ∫ x in S ∪ W, F x ∂σ := by rw [restrict_frontier_eq_patches hU c hr hSeam]
    _ = (∫ x in S, F x ∂σ) + (∫ x in W, F x ∂σ) := setIntegral_union hDis hWm hIS hIW
    _ = _ := congrArg₂ (· + ·) (setIntegral_congr_fun hSm hEqS) (setIntegral_congr_fun hWm hEqW)

/-- Cartesian derivative columns taken from inside the closed domain. -/
@[expose] def closureGradient (U : Set Point) (Q : Point → S0) (x : Point) : Gradient :=
  fun j => (fderivWithin ℝ Q (closure U) x) (axis j)

theorem closureGradient_eq_classicalGradient {U : Set Point} (hU : IsOpen U)
    {Q : Point → S0} (hQ : ContDiffOn ℝ 2 Q (closure U)) {x : Point} (hx : x ∈ U) :
    closureGradient U Q x = ClassicalGradient Q x := by
  have hN : closure U ∈ 𝓝 x := Filter.mem_of_superset (hU.mem_nhds hx) subset_closure
  have hD := ((hQ x (subset_closure hx)).contDiffAt hN).differentiableAt (by norm_num)
  funext i
  exact congrArg (fun L : Point →L[ℝ] S0 => L (axis i))
    (fderivWithin_eq_fderiv (uniqueDiffWithinAt_of_mem_nhds hN) hD)

/-- The differential determined by Cartesian derivative columns. -/
@[expose] def gradientFromColumns (D : Gradient) : Point →L[ℝ] S0 :=
  ∑ i, (EuclideanSpace.proj i).smulRight (D i)

theorem gradientFromColumns_apply (D : Gradient) (v : Point) :
    gradientFromColumns D v = ∑ i, v i • D i := by
  simp only [gradientFromColumns, sum_apply, ContinuousLinearMap.smulRight_apply]
  rfl

theorem gradientFromColumns_axis (D : Gradient) (j : Fin 3) :
    gradientFromColumns D (axis j) = D j := by
  rw [gradientFromColumns_apply]
  simp only [axis, PiLp.single_apply, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq', if_pos (Finset.mem_univ j)]

theorem elasticStress_entry (a : BulkCoefficients) (ε : ElasticScale) (v : S0)
    (D : Gradient) (i j : Fin 3) :
    elasticStress a ε v D i j =
      (if i = j then energyDensity a ε v D else 0) - frobeniusS0 (D i) (D j) := by
  let Q (x : Point) := v + gradientFromColumns D x
  have hQ : Q 0 = v := by simp only [Q, map_zero, add_zero]
  have hD : ClassicalGradient Q 0 = D := by
    funext k
    have hd : HasFDerivAt Q (gradientFromColumns D) 0 :=
      (gradientFromColumns D).hasFDerivAt.const_add v
    exact (congrArg (fun L : Point →L[ℝ] S0 => L (axis k)) hd.fderiv).trans
      (gradientFromColumns_axis D k)
  have hs := elasticStress_classicalGradient a ε Q 0
  rw [hQ, hD] at hs
  rw [hs, stressTensor, hQ]
  change (if i = j then energyDensity a ε v (ClassicalGradient Q 0) else 0) -
    frobeniusS0 (ClassicalGradient Q 0 i) (ClassicalGradient Q 0 j) = _
  rw [hD]

theorem contDiffOn_closureElasticStress_entry
    (a : BulkCoefficients) (ε : ElasticScale) {U : Set Point} {Q : Point → S0}
    (hU : UniqueDiffOn ℝ (closure U)) (hQ : ContDiffOn ℝ 2 Q (closure U)) (i j : Fin 3) :
    ContDiffOn ℝ 1 (fun x => elasticStress a ε (Q x) (closureGradient U Q x) i j) (closure U) := by
  let C := closure U
  have hD (k : Fin 3) : ContDiffOn ℝ 1 (fun x => closureGradient U Q x k) C :=
    (ContinuousLinearMap.apply ℝ S0 (axis k)).contDiff.comp_contDiffOn
      (hQ.fderivWithin hU (by norm_num))
  have hF (k : Fin 3) : ContDiffOn ℝ 1
      (fun x => frobeniusCoordinateEquiv (closureGradient U Q x k)) C :=
    frobeniusCoordinateEquiv.toContinuousLinearEquiv.toContinuousLinearMap.contDiff.comp_contDiffOn (hD k)
  have hGram (k l : Fin 3) : ContDiffOn ℝ 1
      (fun x => frobeniusS0 (closureGradient U Q x k) (closureGradient U Q x l)) C := by
    simp_rw [← frobeniusCoordinateEquiv_inner]
    exact ContDiffOn.inner ℝ (hF k) (hF l)
  have hE : ContDiffOn ℝ 1 (fun x => energyDensity a ε (Q x) (closureGradient U Q x)) C := by
    simp only [energyDensity, gradientNormSq]
    have hP : ContDiff ℝ 1 (bulkPotential a) := (contDiff_bulkPotential a).of_le (by simp)
    exact (contDiffOn_const.mul (ContDiffOn.sum fun k _ => hGram k k)).add
      (contDiffOn_const.mul (hP.comp_contDiffOn (hQ.of_le (by norm_num))))
  simp_rw [elasticStress_entry]
  by_cases h : i = j
  · simpa only [if_pos h] using hE.sub (hGram i j)
  · simpa only [if_neg h] using contDiffOn_const.sub (hGram i j)

private theorem elasticStress_trace_eq_energyDensity_add_bulk (a : BulkCoefficients) (ε : ElasticScale)
    (q : S0) (D : Gradient) : (elasticStress a ε q D).trace =
      energyDensity a ε q D + 2 * ((ε : ℝ)⁻¹ ^ 2 * bulkPotential a q) := by
  rw [elasticStress_trace, energyDensity]
  ring

/-- Fixed-radius two-patch flux for the elastic stress of a classical solution.
The stress at physical boundary points uses the derivative within the closure. -/
theorem boundary_pohozaev_stressFlux
    (hGG : External.LipschitzGaussGreen) (a : BulkCoefficients) (ε : ElasticScale)
    {U : Set Point} (hU : IsOpen U) (hUnique : UniqueDiffOn ℝ (closure U))
    {Q : Point → S0} (hQ : ContDiffOn ℝ ∞ Q U) (hC : ContDiffOn ℝ 2 Q (closure U))
    (hEuler : ∀ x ∈ U, (ε : ℝ) ^ 2 • (↑(laplacian Q x) : Tensor) = bulkGradient a (Q x))
    (c : Point) {r : ℝ} (hr : 0 < r) {ν ν' : Point → Point}
    (hGeo : PiecewiseRegularBoundary (U ∩ Metric.ball c r) ν')
    (hSeam : Measure.euclideanHausdorffMeasure 2 (frontier U ∩ Metric.sphere c r) = 0)
    (hRad : EqOn ν' (fun x => r⁻¹ • (x - c)) (U ∩ Metric.sphere c r))
    (hPhys : EqOn ν' ν (frontier U ∩ Metric.ball c r)) :
    let σ : Measure Point := Measure.euclideanHausdorffMeasure 2
    let D := closureGradient U Q
    let T := fun x => elasticStress a ε (Q x) (D x)
    let e := fun x => energyDensity a ε (Q x) (D x)
    let p := fun x => (ε : ℝ)⁻¹ ^ 2 * bulkPotential a (Q x)
    let f := centeredStressFlux T c (fun x => r⁻¹ • (x - c))
    let g := centeredStressFlux T c ν
    IntegrableOn f (U ∩ Metric.sphere c r) σ ∧ IntegrableOn g (frontier U ∩ Metric.ball c r) σ ∧
      (∫ x in U ∩ Metric.ball c r, (e x + 2 * p x)) =
        (∫ x in U ∩ Metric.sphere c r, f x ∂σ) + (∫ x in frontier U ∩ Metric.ball c r, g x ∂σ) := by
  let D := closureGradient U Q
  let T (x : Point) := elasticStress a ε (Q x) (D x)
  have hT (i j : Fin 3) : ContDiffOn ℝ 1 (fun x => T x i j) (closure (U ∩ Metric.ball c r)) :=
    (contDiffOn_closureElasticStress_entry a ε hUnique hC i j).mono (closure_mono inter_subset_left)
  have hDiv : ∀ x ∈ U ∩ Metric.ball c r, ∀ i : Fin 3, ∑ j, coordDeriv j (fun y => T y i j) x = 0 := by
    intro x hx i
    have hEq (j : Fin 3) : (fun y => T y i j) =ᶠ[𝓝 x] (fun y => stressTensor a ε Q y i j) := by
      filter_upwards [hU.mem_nhds hx.1] with y hy
      unfold T D
      rw [closureGradient_eq_classicalGradient hU hC hy, elasticStress_classicalGradient]
    have hD' (j : Fin 3) : coordDeriv j (fun y => T y i j) x =
        coordDeriv j (fun y => stressTensor a ε Q y i j) x :=
      congrArg (fun A : Point →L[ℝ] ℝ => A (axis j)) (hEq j).fderiv_eq
    simp_rw [hD']
    exact stressEnergy_rowDivergence_eq_zero_of_pointwise a ε hU hQ hEuler x hx.1 i
  obtain ⟨hF, hG, hFlux⟩ := integral_trace_eq_centeredStressFlux_patches hGG hU c hr
    hGeo hSeam hRad hPhys T hT hDiv
  refine ⟨hF, hG, ?_⟩
  have hTr (x : Point) : (T x).trace =
      energyDensity a ε (Q x) (D x) + 2 * ((ε : ℝ)⁻¹ ^ 2 * bulkPotential a (Q x)) :=
    elasticStress_trace_eq_energyDensity_add_bulk a ε (Q x) (D x)
  simpa only [hTr] using hFlux

/-- The centered flux of the elastic stress in terms of its two gradient
directions. -/
theorem centeredStressFlux_elasticStress (a : BulkCoefficients) (ε : ElasticScale)
    (Q : Point → S0) (D : Point → Gradient) (c : Point) (ν : Point → Point) (x : Point) :
    centeredStressFlux (fun y => elasticStress a ε (Q y) (D y)) c ν x =
      inner ℝ (x - c) (ν x) * energyDensity a ε (Q x) (D x) -
        frobeniusS0 (gradientFromColumns (D x) (x - c)) (gradientFromColumns (D x) (ν x)) := by
  let v := x - c
  let n := ν x
  let e := energyDensity a ε (Q x) (D x)
  have hDiag : (∑ j, (∑ i, v i * (if i = j then e else 0)) * n j) = inner ℝ v n * e := by
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hGram : (∑ j, (∑ i, v i * frobeniusS0 (D x i) (D x j)) * n j) =
      frobeniusS0 (gradientFromColumns (D x) v) (gradientFromColumns (D x) n) := by
    rw [← frobeniusCoordinateEquiv_inner]
    simp only [gradientFromColumns_apply, map_sum, map_smul, sum_inner, inner_sum,
      real_inner_smul_left, real_inner_smul_right, frobeniusCoordinateEquiv_inner, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  simp only [centeredStressFlux, elasticStress_entry, mul_sub, Finset.sum_sub_distrib, sub_mul]
  exact congrArg₂ (· - ·) hDiag hGram

/-- The centered flux on a sphere of radius `r` is the energy flux minus
the radial derivative term with coefficient `r⁻¹`. -/
theorem centeredStressFlux_elasticStress_sphere (a : BulkCoefficients) (ε : ElasticScale)
    (Q : Point → S0) (D : Point → Gradient) (c : Point) {r : ℝ} (hr : 0 < r)
    {x : Point} (hx : x ∈ Metric.sphere c r) :
    centeredStressFlux (fun y => elasticStress a ε (Q y) (D y)) c (fun y => r⁻¹ • (y - c)) x =
      r * energyDensity a ε (Q x) (D x) - r⁻¹ * ‖gradientFromColumns (D x) (x - c)‖ ^ 2 := by
  have hn : ‖x - c‖ = r := by simpa only [Metric.mem_sphere, dist_eq_norm] using hx
  rw [centeredStressFlux_elasticStress, real_inner_smul_right, real_inner_self_eq_norm_sq, hn, map_smul,
    ← frobeniusCoordinateEquiv_inner, map_smul, real_inner_smul_right, real_inner_self_eq_norm_sq,
    LinearIsometryEquiv.norm_map]
  field_simp [hr.ne']

/-- Tangential columns obtained by subtracting the normal part of the
differential. The normal is assumed to be unit in the decomposition lemmas. -/
@[expose] def tangentialGradientColumns (D : Gradient) (n : Point) : Gradient :=
  fun i => D i - n i • gradientFromColumns D n

theorem gradientFromColumns_tangential (D : Gradient) (n v : Point) :
    gradientFromColumns (tangentialGradientColumns D n) v =
      gradientFromColumns D (v - (inner ℝ v n) • n) := by
  rw [map_sub, map_smul, gradientFromColumns_apply (tangentialGradientColumns D n),
    gradientFromColumns_apply D v]
  simp only [tangentialGradientColumns, smul_sub, smul_smul, Finset.sum_sub_distrib,
    ← Finset.sum_smul, EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct,
    mul_comm]

theorem gradientNormSq_eq_normal_add_tangential (D : Gradient) (n : Point) (hn : ‖n‖ = 1) :
    gradientNormSq D = ‖gradientFromColumns D n‖ ^ 2 + gradientNormSq (tangentialGradientColumns D n) := by
  let A := gradientFromColumns D n
  let B := tangentialGradientColumns D n
  have hSumN : (∑ i : Fin 3, (n i) ^ 2) = 1 := by
    rw [← EuclideanSpace.real_norm_sq_eq, hn, one_pow]
  have hSumInner : (∑ i : Fin 3, n i * frobeniusS0 (D i) A) = ‖A‖ ^ 2 := by
    rw [← frobeniusCoordinateEquiv.norm_map A, ← real_inner_self_eq_norm_sq]
    conv_rhs => lhs; change frobeniusCoordinateEquiv (gradientFromColumns D n)
    rw [gradientFromColumns_apply, map_sum, sum_inner]
    simp only [map_smul, real_inner_smul_left, frobeniusCoordinateEquiv_inner]
  have hPoint (i : Fin 3) : ‖B i‖ ^ 2 = ‖D i‖ ^ 2 - 2 * (n i * frobeniusS0 (D i) A) +
      (n i) ^ 2 * ‖A‖ ^ 2 := by
    rw [← frobeniusCoordinateEquiv.norm_map (B i)]
    change ‖frobeniusCoordinateEquiv (D i - n i • A)‖ ^ 2 = _
    rw [map_sub, map_smul, norm_sub_sq_real, real_inner_smul_right, frobeniusCoordinateEquiv_inner,
      LinearIsometryEquiv.norm_map, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, LinearIsometryEquiv.norm_map]
  have hSplit : gradientNormSq B = gradientNormSq D - ‖A‖ ^ 2 := by
    rw [gradientNormSq_eq_sum_norm_sq, gradientNormSq_eq_sum_norm_sq]
    simp_rw [hPoint, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      ← Finset.sum_mul, hSumInner, hSumN, one_mul]
    ring
  change gradientNormSq D = ‖A‖ ^ 2 + gradientNormSq B
  linarith only [hSplit]

/-- The physical-boundary terms in the partial Pohozaev identity, evaluated
at a displacement `v` and outward unit normal `n`. -/
@[expose] def physicalBoundaryStressCorrection (D : Gradient) (v n : Point) : ℝ :=
    let s := inner ℝ v n
    let A := gradientFromColumns D n
    let B := tangentialGradientColumns D n
    let vT := v - s • n
    (1 / 2 : ℝ) * s * (‖A‖ ^ 2 - gradientNormSq B) + frobeniusS0 A (gradientFromColumns B vT)

/-- The negative physical-boundary flux has the two terms of the partial
Pohozaev identity for a vacuum-valued trace. -/
theorem neg_centeredStressFlux_elasticStress_physical (a : BulkCoefficients) (ε : ElasticScale)
    (Q : Point → S0) (D : Point → Gradient) (c : Point) (ν : Point → Point)
    {x : Point} (hn : ‖ν x‖ = 1) (hVac : Q x ∈ vacuum a) :
    -centeredStressFlux (fun y => elasticStress a ε (Q y) (D y)) c ν x =
      physicalBoundaryStressCorrection (D x) (x - c) (ν x) := by
  let n := ν x
  let v := x - c
  let s := inner ℝ v n
  let A := gradientFromColumns (D x) n
  let B := tangentialGradientColumns (D x) n
  let vT := v - s • n
  have hn' : ‖n‖ = 1 := hn
  have hTan : inner ℝ vT n = 0 := by
    change inner ℝ (v - s • n) n = 0
    rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hn']
    simp only [one_pow, mul_one, s, sub_self]
  have hD : gradientFromColumns (D x) v = s • A + gradientFromColumns B vT := by
    rw [gradientFromColumns_tangential, hTan, zero_smul, sub_zero]
    change _ = s • A + gradientFromColumns (D x) (v - s • n)
    rw [map_sub (gradientFromColumns (D x)) v (s • n), map_smul]
    change gradientFromColumns (D x) v = s • A + (gradientFromColumns (D x) v - s • A)
    abel
  have hNorm : gradientNormSq (D x) = ‖A‖ ^ 2 + gradientNormSq B :=
    gradientNormSq_eq_normal_add_tangential (D x) n hn
  have hBulk : bulkPotential a (Q x) = 0 := (bulkPotential_eq_zero_iff a (Q x)).2 hVac
  have hComm : inner ℝ (frobeniusCoordinateEquiv (gradientFromColumns B vT))
      (frobeniusCoordinateEquiv A) = frobeniusS0 A (gradientFromColumns B vT) := by
    rw [← frobeniusCoordinateEquiv_inner]
    exact real_inner_comm _ _
  change -centeredStressFlux (fun y => elasticStress a ε (Q y) (D y)) c ν x =
    (1 / 2 : ℝ) * s * (‖A‖ ^ 2 - gradientNormSq B) + frobeniusS0 A (gradientFromColumns B vT)
  rw [centeredStressFlux_elasticStress]
  change -(s * energyDensity a ε (Q x) (D x) - frobeniusS0 (gradientFromColumns (D x) v) A) = _
  rw [hD, energyDensity, hBulk, mul_zero, add_zero, hNorm, ← frobeniusCoordinateEquiv_inner,
    map_add, map_smul, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
    LinearIsometryEquiv.norm_map, hComm]
  ring

/-- Coarea on an actual intersection with a ball. The derivative uses the
spherical patch with Euclidean Hausdorff area and its exact Jacobian. -/
theorem absolutelyContinuous_integral_inter_ball_and_ae_surface_deriv
    {U : Set Point} (hU : MeasurableSet U) (c : Point) {R : ℝ} (hR : 0 ≤ R)
    {f : Point → ℝ} (hf : IntegrableOn f (U ∩ Metric.ball c R) volume) :
    let F := fun r => ∫ x in U ∩ Metric.ball c r, f x
    AbsolutelyContinuousOnInterval F 0 R ∧ ∀ᵐ r : ℝ, r ∈ Ioo 0 R →
      HasDerivAt F (∫ x in U ∩ Metric.sphere c r, f x ∂(Measure.euclideanHausdorffMeasure 2)) r := by
  let g := U.indicator f
  have hg : IntegrableOn g (Metric.ball c R) volume := by
    change Integrable (U.indicator f) (volume.restrict (Metric.ball c R))
    apply (integrable_indicator_iff hU).mpr
    change Integrable f ((volume.restrict (Metric.ball c R)).restrict U)
    rw [Measure.restrict_restrict hU]
    exact hf
  have hEq (r : ℝ) : (∫ x in Metric.ball c r, g x) = ∫ x in U ∩ Metric.ball c r, f x := by
    dsimp only [g]
    rw [setIntegral_indicator hU, inter_comm]
  have hAbs := HarmonicMaps.absolutelyContinuousOnInterval_integral_ball (n := 3) (by decide) hR hg
  refine ⟨?_, ?_⟩
  · simpa only [hEq] using hAbs
  filter_upwards [HarmonicMaps.ae_hasDerivAt_integral_ball (n := 3) (by decide) hR hg] with r hDer
  intro hr
  have hPolar := StratificationTheory.integral_euclidean_sphereArea_affine (n := 3) (by decide)
    c ⟨r, hr.1⟩ g
  dsimp only [g] at hPolar
  rw [StratificationTheory.euclideanHausdorffMeasure_unitSphere_eq_toSphere (by decide : 0 < 3),
    setIntegral_indicator hU, inter_comm] at hPolar
  have hd := hDer hr
  simpa only [hEq, hPolar] using hd

theorem continuousOn_closureEnergyDensity (a : BulkCoefficients) (ε : ElasticScale)
    {U : Set Point} {Q : Point → S0} (hUnique : UniqueDiffOn ℝ (closure U))
    (hQ : ContDiffOn ℝ 2 Q (closure U)) :
    ContinuousOn (fun x => energyDensity a ε (Q x) (closureGradient U Q x)) (closure U) := by
  let D := closureGradient U Q
  let T (x : Point) := elasticStress a ε (Q x) (D x)
  let p (x : Point) := (ε : ℝ)⁻¹ ^ 2 * bulkPotential a (Q x)
  have hTr : ContinuousOn (fun x => (T x).trace) (closure U) := by
    simp only [Matrix.trace, Matrix.diag_apply]
    exact continuousOn_finsetSum Finset.univ fun i _ =>
      (contDiffOn_closureElasticStress_entry a ε hUnique hQ i i).continuousOn
  have hp : ContinuousOn p (closure U) := continuousOn_const.mul
    ((contDiff_bulkPotential a).continuous.comp_continuousOn hQ.continuousOn)
  have hp₂ : ContinuousOn (fun x => (2 : ℝ) * p x) (closure U) := continuousOn_const.mul hp
  refine (hTr.sub hp₂).congr fun x _ => ?_
  change energyDensity a ε (Q x) (D x) = (T x).trace - 2 * p x
  have ht : (T x).trace = energyDensity a ε (Q x) (D x) + 2 * p x :=
    elasticStress_trace_eq_energyDensity_add_bulk a ε (Q x) (D x)
  rw [ht, add_sub_cancel_right]

private theorem continuousOn_closureRadialNormSq {U : Set Point} {Q : Point → S0}
    (hUnique : UniqueDiffOn ℝ (closure U)) (hQ : ContDiffOn ℝ 2 Q (closure U)) (c : Point) :
    ContinuousOn (fun x => ‖gradientFromColumns (closureGradient U Q x) (x - c)‖ ^ 2) (closure U) := by
  simp_rw [gradientFromColumns_apply]
  apply ContinuousOn.pow (ContinuousOn.norm _)
  refine continuousOn_finsetSum Finset.univ fun i _ => ?_
  have hCoord : Continuous (fun x : Point => (x - c) i) := by
    change Continuous (fun x : Point => (EuclideanSpace.proj i) (x - c))
    fun_prop
  have hCol : ContinuousOn (fun x => closureGradient U Q x i) (closure U) :=
    (ContinuousLinearMap.apply ℝ S0 (axis i)).continuous.comp_continuousOn
      (hQ.continuousOn_fderivWithin hUnique (by norm_num))
  exact hCoord.continuousOn.smul hCol

theorem integrableOn_of_continuousOn_compact_finite_piece
    {μ : Measure Point} {K S : Set Point} (hK : IsCompact K) (hS : S ⊆ K)
    (hSm : MeasurableSet S) (hFin : μ S < ⊤)
    {f : Point → ℝ} (hf : ContinuousOn f K) : IntegrableOn f S μ := by
  letI : IsFiniteMeasure (μ.restrict S) := ⟨by rwa [Measure.restrict_apply_univ]⟩
  have hI := (hf.integrableOn_compact (μ := μ.restrict S) hK).mono_set hS
  simpa only [IntegrableOn, Measure.restrict_restrict hSm, inter_self] using hI

/-- The fixed-radius balance of the partial Pohozaev identity. The bulk and
spherical terms have their exact coefficients and the physical term uses
the tangential projection at the given wall normal. -/
theorem boundary_pohozaev_balance_at_radius
    (hGG : External.LipschitzGaussGreen) (a : BulkCoefficients) (ε : ElasticScale)
    {U : Set Point} (hU : IsOpen U) (hUnique : UniqueDiffOn ℝ (closure U))
    {Q : Point → S0} (hQ : ContDiffOn ℝ ∞ Q U) (hC : ContDiffOn ℝ 2 Q (closure U))
    (hEuler : ∀ x ∈ U, (ε : ℝ) ^ 2 • (↑(laplacian Q x) : Tensor) = bulkGradient a (Q x))
    (c : Point) {r : ℝ} (hr : 0 < r) {ν ν' : Point → Point}
    (hGeo : PiecewiseRegularBoundary (U ∩ Metric.ball c r) ν')
    (hSeam : Measure.euclideanHausdorffMeasure 2 (frontier U ∩ Metric.sphere c r) = 0)
    (hRad : EqOn ν' (fun x => r⁻¹ • (x - c)) (U ∩ Metric.sphere c r))
    (hPhys : EqOn ν' ν (frontier U ∩ Metric.ball c r))
    (hν : ∀ x ∈ frontier U, ‖ν x‖ = 1) (hVac : ∀ x ∈ frontier U, Q x ∈ vacuum a) :
    let σ : Measure Point := Measure.euclideanHausdorffMeasure 2
    let V := U ∩ Metric.ball c r
    let S := U ∩ Metric.sphere c r
    let W := frontier U ∩ Metric.ball c r
    let D := closureGradient U Q
    let e := fun x => energyDensity a ε (Q x) (D x)
    let p := fun x => (ε : ℝ)⁻¹ ^ 2 * bulkPotential a (Q x)
    let Z := fun x => ‖gradientFromColumns (D x) (x - c)‖ ^ 2
    let B := fun x => physicalBoundaryStressCorrection (D x) (x - c) (ν x)
    r * (∫ x in S, e x ∂σ) - (∫ x in V, e x) =
      2 * (∫ x in V, p x) + r⁻¹ * (∫ x in S, Z x ∂σ) + (∫ x in W, B x ∂σ) := by
  let σ : Measure Point := Measure.euclideanHausdorffMeasure 2
  let V := U ∩ Metric.ball c r
  let S := U ∩ Metric.sphere c r
  let W := frontier U ∩ Metric.ball c r
  let D := closureGradient U Q
  let e (x : Point) := energyDensity a ε (Q x) (D x)
  let p (x : Point) := (ε : ℝ)⁻¹ ^ 2 * bulkPotential a (Q x)
  let Z (x : Point) := ‖gradientFromColumns (D x) (x - c)‖ ^ 2
  let B (x : Point) := physicalBoundaryStressCorrection (D x) (x - c) (ν x)
  let T (x : Point) := elasticStress a ε (Q x) (D x)
  let f := centeredStressFlux T c (fun x => r⁻¹ • (x - c))
  let g := centeredStressFlux T c ν
  obtain ⟨_, _, hFlux⟩ := boundary_pohozaev_stressFlux hGG a ε hU hUnique hQ hC hEuler c hr
    hGeo hSeam hRad hPhys
  change (∫ x in V, e x + 2 * p x) = (∫ x in S, f x ∂σ) + (∫ x in W, g x ∂σ) at hFlux
  have hCl : IsCompact (closure V) := hGeo.isBounded.isCompact_closure
  have hClU : closure V ⊆ closure U := closure_mono inter_subset_left
  have he : ContinuousOn e (closure V) := (continuousOn_closureEnergyDensity a ε hUnique hC).mono hClU
  have hp : ContinuousOn p (closure V) := (continuousOn_const.mul
    ((contDiff_bulkPotential a).continuous.comp_continuousOn hC.continuousOn)).mono hClU
  have hZ : ContinuousOn Z (closure V) := (continuousOn_closureRadialNormSq hUnique hC c).mono hClU
  obtain ⟨hSF, _⟩ := sphere_physical_patches_subset_frontier hU c hr
  have hSm : MeasurableSet S := hU.measurableSet.inter Metric.isClosed_sphere.measurableSet
  have hWm : MeasurableSet W := isClosed_frontier.measurableSet.inter Metric.isOpen_ball.measurableSet
  have hArea : σ S < ⊤ := (measure_mono hSF).trans_lt hGeo.area_lt_top
  have heS := integrableOn_of_continuousOn_compact_finite_piece hCl
    (hSF.trans frontier_subset_closure) hSm hArea he
  have hZS := integrableOn_of_continuousOn_compact_finite_piece hCl
    (hSF.trans frontier_subset_closure) hSm hArea hZ
  have hSFlux : (∫ x in S, f x ∂σ) = r * (∫ x in S, e x ∂σ) - r⁻¹ * (∫ x in S, Z x ∂σ) := by
    calc
      _ = ∫ x in S, (r * e x - r⁻¹ * Z x) ∂σ := setIntegral_congr_fun hSm fun x hx =>
        centeredStressFlux_elasticStress_sphere a ε Q D c hr hx.2
      _ = _ := by rw [integral_sub (heS.const_mul r) (hZS.const_mul _), integral_const_mul, integral_const_mul]
  have hWFlux : (∫ x in W, B x ∂σ) = -(∫ x in W, g x ∂σ) := by
    rw [← integral_neg]
    exact setIntegral_congr_fun hWm fun x hx =>
      (neg_centeredStressFlux_elasticStress_physical a ε Q D c ν (hν x hx.1) (hVac x hx.1)).symm
  have heV := (he.integrableOn_compact (μ := volume) hCl).mono_set (subset_closure : V ⊆ closure V)
  have hpV := (hp.integrableOn_compact (μ := volume) hCl).mono_set (subset_closure : V ⊆ closure V)
  rw [integral_add heV (hpV.const_mul _), integral_const_mul, hSFlux] at hFlux
  change r * (∫ x in S, e x ∂σ) - (∫ x in V, e x) =
    2 * (∫ x in V, p x) + r⁻¹ * (∫ x in S, Z x ∂σ) + (∫ x in W, B x ∂σ)
  linarith only [hFlux, hWFlux]

/-- Local absolute continuity and the exact derivative of normalized energy
on truncated balls. The radius-wise geometric hypotheses specify the actual
boundary of each admissible intersection. -/
theorem ae_hasDerivAt_normalized_boundary_energy
    (hGG : External.LipschitzGaussGreen) (a : BulkCoefficients) (ε : ElasticScale)
    {U : Set Point} (hU : IsOpen U) (hUnique : UniqueDiffOn ℝ (closure U))
    {Q : Point → S0} (hQ : ContDiffOn ℝ ∞ Q U) (hC : ContDiffOn ℝ 2 Q (closure U))
    (hEuler : ∀ x ∈ U, (ε : ℝ) ^ 2 • (↑(laplacian Q x) : Tensor) = bulkGradient a (Q x))
    (c : Point) {R : ℝ} (hR : 0 < R) (ν : Point → Point)
    (hν : ∀ x ∈ frontier U, ‖ν x‖ = 1) (hVac : ∀ x ∈ frontier U, Q x ∈ vacuum a)
    (hSliced : ∀ᵐ r : ℝ, r ∈ Ioo 0 R → ∃ ν' : Point → Point,
      PiecewiseRegularBoundary (U ∩ Metric.ball c r) ν' ∧
        Measure.euclideanHausdorffMeasure 2 (frontier U ∩ Metric.sphere c r) = 0 ∧
        EqOn ν' (fun x => r⁻¹ • (x - c)) (U ∩ Metric.sphere c r) ∧
        EqOn ν' ν (frontier U ∩ Metric.ball c r)) :
    let σ : Measure Point := Measure.euclideanHausdorffMeasure 2
    let D := closureGradient U Q
    let F (r : ℝ) := ∫ x in U ∩ Metric.ball c r, energyDensity a ε (Q x) (D x)
    let P (r : ℝ) := ∫ x in U ∩ Metric.ball c r, (ε : ℝ)⁻¹ ^ 2 * bulkPotential a (Q x)
    let Z (r : ℝ) := ∫ x in U ∩ Metric.sphere c r, ‖gradientFromColumns (D x) (x - c)‖ ^ 2 ∂σ
    let B (r : ℝ) := ∫ x in frontier U ∩ Metric.ball c r,
      physicalBoundaryStressCorrection (D x) (x - c) (ν x) ∂σ
    (∀ s t, 0 < s → s ≤ t → t ≤ R → AbsolutelyContinuousOnInterval (fun r => F r / r) s t) ∧
      ∀ᵐ r : ℝ, r ∈ Ioo 0 R → HasDerivAt (fun t => F t / t) ((2 * P r + r⁻¹ * Z r + B r) / r ^ 2) r := by
  let D := closureGradient U Q
  let e (x : Point) := energyDensity a ε (Q x) (D x)
  let F (r : ℝ) := ∫ x in U ∩ Metric.ball c r, e x
  let V := U ∩ Metric.ball c R
  have hK : IsCompact (closure V) := (Metric.isBounded_ball.subset (inter_subset_right :
    V ⊆ Metric.ball c R)).isCompact_closure
  have he : IntegrableOn e V volume :=
    (((continuousOn_closureEnergyDensity a ε hUnique hC).mono
      (closure_mono (inter_subset_left : V ⊆ U))).integrableOn_compact hK).mono_set subset_closure
  obtain ⟨hAbs, hDer⟩ := absolutelyContinuous_integral_inter_ball_and_ae_surface_deriv
    hU.measurableSet c hR.le he
  refine ⟨?_, ?_⟩
  · intro s t hs hst ht
    have hFac : AbsolutelyContinuousOnInterval F s t := hAbs.mono (by
      rw [uIcc_of_le hst, uIcc_of_le hR.le]
      exact fun x hx => ⟨hs.le.trans hx.1, hx.2.trans ht⟩)
    have hinv : AbsolutelyContinuousOnInterval (fun r : ℝ => r⁻¹) s t := by
      apply ContDiffOn.absolutelyContinuousOnInterval
      rw [uIcc_of_le hst]
      exact contDiffOn_id.inv fun x hx => (hs.trans_le hx.1).ne'
    simpa only [div_eq_mul_inv, Pi.mul_def] using hFac.mul hinv
  · filter_upwards [hSliced, hDer] with r hg hd
    intro hr
    obtain ⟨ν', hGeo, hSeam, hRad, hPhys⟩ := hg hr
    have hf := (hd hr).div (hasDerivAt_id r) hr.1.ne'
    have hFlux := boundary_pohozaev_balance_at_radius hGG a ε hU hUnique hQ hC hEuler c hr.1
      hGeo hSeam hRad hPhys hν hVac
    let σ : Measure Point := Measure.euclideanHausdorffMeasure 2
    let S := U ∩ Metric.sphere c r
    have hBalance : r * (∫ x in S, e x ∂σ) - F r = _ := hFlux
    change HasDerivAt (fun t => F t / t) (((∫ x in S, e x ∂σ) * r - F r * 1) / r ^ 2) r at hf
    rw [mul_one, mul_comm (∫ x in S, e x ∂σ) r, hBalance] at hf
    exact hf

theorem norm_gradientFromColumns_le (D : Gradient) (v : Point) :
    ‖gradientFromColumns D v‖ ≤ ‖v‖ * Real.sqrt (gradientNormSq D) := by
  have hg : 0 ≤ gradientNormSq D := by
    rw [gradientNormSq_eq_sum_norm_sq]
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i : Fin 3 => |v i|) (fun i => ‖D i‖)
  simp only [sq_abs, ← EuclideanSpace.real_norm_sq_eq, ← gradientNormSq_eq_sum_norm_sq] at hs
  rw [gradientFromColumns_apply]
  calc
    _ ≤ ∑ i, |v i| * ‖D i‖ := by
      simpa only [norm_smul, Real.norm_eq_abs] using norm_sum_le Finset.univ (fun i => v i • D i)
    _ ≤ _ := by
      apply (sq_le_sq₀ (Finset.sum_nonneg fun _ _ => mul_nonneg (abs_nonneg _) (norm_nonneg _))
        (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))).1
      rw [mul_pow, Real.sq_sqrt hg]
      exact hs

private theorem norm_tangential_displacement_le (v n : Point) (hn : ‖n‖ = 1) :
    ‖v - (inner ℝ v n) • n‖ ≤ ‖v‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1
  rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, hn, mul_one, Real.norm_eq_abs, sq_abs]
  nlinarith only [sq_nonneg (inner ℝ v n)]

/-- Pointwise lower bound on the physical correction from the boundary chart
height inequality and Young's inequality. -/
theorem physicalBoundaryStressCorrection_ge
    (D : Gradient) (v n : Point) {r M : ℝ} (hn : ‖n‖ = 1) (hv : ‖v‖ ≤ r)
    (hWall : -(M * r ^ 2) ≤ inner ℝ v n) :
    let A := gradientFromColumns D n
    let B := tangentialGradientColumns D n
    (-(1 / 2 : ℝ) * (M + 1) * r ^ 2 * ‖A‖ ^ 2 - (1 / 2 : ℝ) * (r + 1) * gradientNormSq B) ≤
      physicalBoundaryStressCorrection D v n := by
  let A := gradientFromColumns D n
  let B := tangentialGradientColumns D n
  let s := inner ℝ v n
  let z := v - s • n
  let b := gradientNormSq B
  have hb : 0 ≤ b := by
    simp only [b, gradientNormSq_eq_sum_norm_sq]
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hs : s ≤ r := by
    change inner ℝ v n ≤ r
    simpa only [hn, mul_one] using (real_inner_le_norm v n).trans
      (mul_le_mul_of_nonneg_right hv (norm_nonneg n))
  have hA := mul_le_mul_of_nonneg_right hWall (sq_nonneg ‖A‖)
  have hB := mul_le_mul_of_nonneg_right hs hb
  have hz : ‖z‖ ≤ r := (norm_tangential_displacement_le v n hn).trans hv
  have hCross : |frobeniusS0 A (gradientFromColumns B z)| ≤ ‖A‖ * (r * Real.sqrt b) := by
    rw [← frobeniusCoordinateEquiv_inner]
    have hInner := abs_real_inner_le_norm (frobeniusCoordinateEquiv A)
      (frobeniusCoordinateEquiv (gradientFromColumns B z))
    rw [LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map] at hInner
    exact hInner.trans (mul_le_mul_of_nonneg_left
      ((norm_gradientFromColumns_le B z).trans (mul_le_mul_of_nonneg_right hz (Real.sqrt_nonneg _))) (norm_nonneg _))
  have hYoung : ‖A‖ * (r * Real.sqrt b) ≤ (r ^ 2 * ‖A‖ ^ 2 + b) / 2 := by
    nlinarith only [sq_nonneg (r * ‖A‖ - Real.sqrt b), Real.sq_sqrt hb]
  have hMixed : -((r ^ 2 * ‖A‖ ^ 2 + b) / 2) ≤ frobeniusS0 A (gradientFromColumns B z) :=
    (neg_le_neg (hCross.trans hYoung)).trans (neg_abs_le _)
  change -(1 / 2 : ℝ) * (M + 1) * r ^ 2 * ‖A‖ ^ 2 - (1 / 2 : ℝ) * (r + 1) * b ≤
    (1 / 2 : ℝ) * s * (‖A‖ ^ 2 - b) + frobeniusS0 A (gradientFromColumns B z)
  nlinarith only [hA, hB, hMixed]

end Thesis

end
