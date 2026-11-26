module

public import Thesis.Variational.ScaledDefects
public import Thesis.Foundation.LinearizedBulk
import Thesis.StressEnergy
import Thesis.Foundation.SpectralProjection

/-! The Bochner identity and energy-density bound near the biaxial vacuum. -/

public section

open Filter Set Topology
open scoped BigOperators ContDiff Matrix Matrix.Norms.Frobenius RealInnerProductSpace

set_option autoImplicit false
noncomputable section

namespace Thesis

private theorem contDiffOn_coordDeriv_infty
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {U : Set Point} (hU : IsOpen U)
    {f : Point → F} (hf : ContDiffOn ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) f U) (j : Fin 3) :
    ContDiffOn ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) (coordDeriv j f) U :=
  (ContinuousLinearMap.apply ℝ F (axis j)).contDiff.comp_contDiffOn
    (hf.fderiv_of_isOpen hU (le_of_eq (by simp)))

private theorem coordDeriv_eq_of_eventuallyEq
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f g : Point → F} {x : Point}
    (h : f =ᶠ[𝓝 x] g) (j : Fin 3) : coordDeriv j f x = coordDeriv j g x :=
  DFunLike.congr_fun h.fderiv_eq (axis j)

private theorem coordDeriv_sum
    {F ι : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {U : Finset ι}
    {f : ι → Point → F} {x : Point} (h : ∀ i ∈ U, DifferentiableAt ℝ (f i) x) (j : Fin 3) :
    coordDeriv j (fun y => ∑ i ∈ U, f i y) x = ∑ i ∈ U, coordDeriv j (f i) x := by
  have hD := HasFDerivAt.fun_sum (u := U) (fun i hi => (h i hi).hasFDerivAt)
  simp only [coordDeriv, hD.fderiv, sum_apply]

private theorem coordDeriv_add
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f g : Point → F} {x : Point}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (j : Fin 3) :
    coordDeriv j (fun y => f y + g y) x = coordDeriv j f x + coordDeriv j g x := by
  have hd := hf.hasFDerivAt.add hg.hasFDerivAt
  exact DFunLike.congr_fun hd.fderiv (axis j)

private theorem laplacian_add
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {U : Set Point} (hU : IsOpen U)
    {f g : Point → F} (hf : ContDiffOn ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) f U)
    (hg : ContDiffOn ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) g U) {x : Point} (hx : x ∈ U) :
    laplacian (fun y => f y + g y) x = laplacian f x + laplacian g x := by
  unfold laplacian
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hEq : coordDeriv j (fun y => f y + g y) =ᶠ[𝓝 x]
      (fun y => coordDeriv j f y + coordDeriv j g y) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact coordDeriv_add ((hf.differentiableOn (by simp) y hy).differentiableAt (hU.mem_nhds hy))
      ((hg.differentiableOn (by simp) y hy).differentiableAt (hU.mem_nhds hy)) j
  rw [coordDeriv_eq_of_eventuallyEq hEq j]
  exact coordDeriv_add
    (((contDiffOn_coordDeriv_infty hU hf j).differentiableOn (by simp) x hx).differentiableAt (hU.mem_nhds hx))
    (((contDiffOn_coordDeriv_infty hU hg j).differentiableOn (by simp) x hx).differentiableAt (hU.mem_nhds hx)) j

private theorem laplacian_sum
    {F ι : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {I : Finset ι}
    {U : Set Point} (hU : IsOpen U) {f : ι → Point → F}
    (hf : ∀ i ∈ I, ContDiffOn ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) (f i) U) {x : Point} (hx : x ∈ U) :
    laplacian (fun y => ∑ i ∈ I, f i y) x = ∑ i ∈ I, laplacian (f i) x := by
  unfold laplacian
  rw [Finset.sum_comm (s := I)]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hEq : coordDeriv j (fun y => ∑ i ∈ I, f i y) =ᶠ[𝓝 x]
      (fun y => ∑ i ∈ I, coordDeriv j (f i) y) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact coordDeriv_sum (fun i hi =>
      (((hf i hi).differentiableOn (by simp)) y hy).differentiableAt (hU.mem_nhds hy)) j
  rw [coordDeriv_eq_of_eventuallyEq hEq j]
  exact coordDeriv_sum (fun i hi =>
    ((contDiffOn_coordDeriv_infty hU (hf i hi) j).differentiableOn (by simp) x hx).differentiableAt
      (hU.mem_nhds hx)) j

private theorem frobeniusS0_self (A : S0) : frobeniusS0 A A = ‖A‖ ^ 2 := by
  exact (norm_sq_eq_frobeniusS0 A).symm

private theorem frobeniusS0_symm (A B : S0) : frobeniusS0 A B = frobeniusS0 B A := by
  rw [← frobeniusCoordinateEquiv_inner A B, ← frobeniusCoordinateEquiv_inner B A, real_inner_comm]

theorem laplacian_frobeniusS0_self
    {U : Set Point} (hU : IsOpen U) {Q : Point → S0}
    (hQ : ContDiffOn ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) Q U) {x : Point} (hx : x ∈ U) :
    laplacian (fun y => frobeniusS0 (Q y) (Q y)) x =
      2 * (frobeniusS0 (laplacian Q x) (Q x) + ∑ j, ‖coordDeriv j Q x‖ ^ 2) := by
  unfold laplacian
  have hDQ (y : Point) (hy : y ∈ U) := (hQ.differentiableOn (by simp) y hy).differentiableAt (hU.mem_nhds hy)
  have hTerm (j : Fin 3) : coordDeriv j (coordDeriv j (fun y => frobeniusS0 (Q y) (Q y))) x =
      2 * (frobeniusS0 (coordDeriv j (coordDeriv j Q) x) (Q x) +
        ‖coordDeriv j Q x‖ ^ 2) := by
    have hEq : coordDeriv j (fun y => frobeniusS0 (Q y) (Q y)) =ᶠ[𝓝 x]
        (fun y => (2 : ℝ) * frobeniusS0 (coordDeriv j Q y) (Q y)) := by
      filter_upwards [hU.mem_nhds hx] with y hy
      rw [coordDeriv_frobenius (hDQ y hy) (hDQ y hy),
        frobeniusS0_symm (Q y) (coordDeriv j Q y), two_mul]
    rw [coordDeriv_eq_of_eventuallyEq hEq j]
    have hj := ((contDiffOn_coordDeriv_infty hU hQ j).differentiableOn (by simp) x hx).differentiableAt
      (hU.mem_nhds hx)
    let e := frobeniusCoordinateEquiv.toContinuousLinearEquiv.toContinuousLinearMap
    have hFrob' : DifferentiableAt ℝ (fun y => frobeniusS0 (coordDeriv j Q y) (Q y)) x := by
      simpa only [e, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
        ContinuousLinearEquiv.coe_coe, Function.comp_def, frobeniusCoordinateEquiv_inner] using
        (e.differentiableAt.comp x hj).inner ℝ (e.differentiableAt.comp x (hDQ x hx))
    have hd := (hFrob'.hasFDerivAt.const_mul (2 : ℝ)).fderiv
    rw [show coordDeriv j (fun y => (2 : ℝ) * frobeniusS0 (coordDeriv j Q y) (Q y)) x =
      2 * coordDeriv j (fun y => frobeniusS0 (coordDeriv j Q y) (Q y)) x from
      DFunLike.congr_fun hd (axis j), coordDeriv_frobenius hj (hDQ x hx), frobeniusS0_self]
  simp_rw [hTerm, ← Finset.mul_sum]
  rw [Finset.sum_add_distrib]
  congr 1
  rw [← frobeniusCoordinateEquiv_inner, map_sum, sum_inner]
  simp only [frobeniusCoordinateEquiv_inner]

theorem laplacian_coordDeriv_comm
    {U : Set Point} (hU : IsOpen U) {Q : Point → S0}
    (hQ : ContDiffOn ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) Q U) {x : Point} (hx : x ∈ U) (i : Fin 3) :
    laplacian (coordDeriv i Q) x = coordDeriv i (laplacian Q) x := by
  unfold laplacian
  have hD (j : Fin 3) := contDiffOn_coordDeriv_infty hU hQ j
  rw [coordDeriv_sum (fun j _ => ((contDiffOn_coordDeriv_infty hU (hD j) j).differentiableOn
    (by simp) x hx).differentiableAt (hU.mem_nhds hx)) i]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hEq : coordDeriv j (coordDeriv i Q) =ᶠ[𝓝 x] coordDeriv i (coordDeriv j Q) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    have hyQ := (hQ y hy).contDiffAt (hU.mem_nhds hy)
    exact coordDeriv_comm (hyQ.of_le (WithTop.coe_le_coe.mpr le_top)) j i
  rw [coordDeriv_eq_of_eventuallyEq hEq j]
  have hj := ((hD j) x hx).contDiffAt (hU.mem_nhds hx)
  exact coordDeriv_comm (hj.of_le (WithTop.coe_le_coe.mpr le_top)) j i

private theorem laplacian_bulkPotential
    (a : BulkCoefficients) {U : Set Point} (hU : IsOpen U) {Q : Point → S0}
    (hQ : ContDiffOn ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) Q U) {x : Point} (hx : x ∈ U) :
    laplacian (fun y => bulkPotential a (Q y)) x =
      (∑ j, frobeniusS0 ((fderiv ℝ (bulkForce a) (Q x)) (coordDeriv j Q x)) (coordDeriv j Q x)) +
        frobeniusS0 (bulkForce a (Q x)) (laplacian Q x) := by
  unfold laplacian
  have hDQ (y : Point) (hy : y ∈ U) := (hQ.differentiableOn (by simp) y hy).differentiableAt (hU.mem_nhds hy)
  have hTerm (j : Fin 3) : coordDeriv j (coordDeriv j (fun y => bulkPotential a (Q y))) x =
      frobeniusS0 ((fderiv ℝ (bulkForce a) (Q x)) (coordDeriv j Q x)) (coordDeriv j Q x) +
        frobeniusS0 (bulkForce a (Q x)) (coordDeriv j (coordDeriv j Q) x) := by
    have hEq : coordDeriv j (fun y => bulkPotential a (Q y)) =ᶠ[𝓝 x]
        (fun y => frobeniusS0 (bulkForce a (Q y)) (coordDeriv j Q y)) := by
      filter_upwards [hU.mem_nhds hx] with y hy
      have hB := ((contDiff_bulkPotential a).differentiable (by simp) (Q y)).hasFDerivAt
      change fderiv ℝ (bulkPotential a ∘ Q) y (axis j) = _
      rw [(hB.comp y (hDQ y hy).hasFDerivAt).fderiv, ContinuousLinearMap.comp_apply]
      exact fderiv_bulkPotential a (Q y) (coordDeriv j Q y)
    rw [coordDeriv_eq_of_eventuallyEq hEq j]
    have hF := ((contDiff_bulkForce a).differentiable (by simp) (Q x)).hasFDerivAt.comp x (hDQ x hx).hasFDerivAt
    have hj := ((contDiffOn_coordDeriv_infty hU hQ j).differentiableOn (by simp) x hx).differentiableAt
      (hU.mem_nhds hx)
    change coordDeriv j (fun y => frobeniusS0 ((bulkForce a ∘ Q) y) (coordDeriv j Q y)) x = _
    rw [coordDeriv_frobenius hF.differentiableAt hj]
    have hd : coordDeriv j (bulkForce a ∘ Q) x =
        (fderiv ℝ (bulkForce a) (Q x)) (coordDeriv j Q x) :=
      DFunLike.congr_fun hF.fderiv (axis j)
    exact congrArg (fun A => frobeniusS0 A (coordDeriv j Q x) +
      frobeniusS0 (bulkForce a (Q x)) (coordDeriv j (coordDeriv j Q) x)) hd
  simp_rw [hTerm, Finset.sum_add_distrib]
  congr 1
  rw [← frobeniusCoordinateEquiv_inner, map_sum, inner_sum]
  simp only [frobeniusCoordinateEquiv_inner]

/-- The exact Bochner identity for the half-normalized sextic energy.
The two force-derivative contributions carry the same ε⁻² factor. -/
theorem classicalEnergyDensity_laplacian_bochner
    (a : BulkCoefficients) (ε : ElasticScale) {U : Set Point} (hU : IsOpen U)
    {Q : Point → S0} (hQ : ContDiffOn ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) Q U)
    (hEuler : ∀ x ∈ U, (ε : ℝ) ^ 2 • (↑(laplacian Q x) : Tensor) = bulkGradient a (Q x))
    {x : Point} (hx : x ∈ U) :
    laplacian (fun y => energyDensity a ε (Q y) (ClassicalGradient Q y)) x =
      (∑ i, ∑ j, ‖coordDeriv j (coordDeriv i Q) x‖ ^ 2) +
        (2 * (ε : ℝ)⁻¹ ^ 2) * (∑ j,
          frobeniusS0 ((fderiv ℝ (bulkForce a) (Q x)) (coordDeriv j Q x)) (coordDeriv j Q x)) +
        (ε : ℝ)⁻¹ ^ 4 * ‖bulkForce a (Q x)‖ ^ 2 := by
  let s : ℝ := (ε : ℝ)⁻¹ ^ 2
  let L (y : Point) := bulkForce a (Q y)
  let K (i : Fin 3) (y : Point) := frobeniusS0 (coordDeriv i Q y) (coordDeriv i Q y)
  let P (y : Point) := bulkPotential a (Q y)
  have hP : ContDiffOn ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) P U := (contDiff_bulkPotential a).comp_contDiffOn hQ
  have hD (i : Fin 3) := contDiffOn_coordDeriv_infty hU hQ i
  have hK (i : Fin 3) : ContDiffOn ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) (K i) U := by
    have hc := frobeniusCoordinateEquiv.toContinuousLinearEquiv.toContinuousLinearMap.contDiff.comp_contDiffOn
      (hD i)
    simpa only [K, Function.comp_def, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      ContinuousLinearEquiv.coe_coe, frobeniusCoordinateEquiv_inner] using hc.inner ℝ hc
  have hE (y : Point) (hy : y ∈ U) : laplacian Q y = s • L y := by
    apply Subtype.ext
    change (↑(laplacian Q y) : Tensor) = s • bulkGradient a (Q y)
    have hε : (ε : ℝ) ≠ 0 := ε.2.1.ne'
    have hScale : s * (ε : ℝ) ^ 2 = 1 := by dsimp only [s]; rw [← mul_pow, inv_mul_cancel₀ hε, one_pow]
    simpa only [smul_smul, hScale, one_smul] using congrArg (s • ·) (hEuler y hy)
  have hEC (i : Fin 3) : laplacian (coordDeriv i Q) x =
      s • (fderiv ℝ (bulkForce a) (Q x)) (coordDeriv i Q x) := by
    rw [laplacian_coordDeriv_comm hU hQ hx]
    have hEq : laplacian Q =ᶠ[𝓝 x] (fun y => s • L y) := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact hE y hy
    rw [coordDeriv_eq_of_eventuallyEq hEq i]
    have hDQ := (hQ.differentiableOn (by simp) x hx).differentiableAt (hU.mem_nhds hx)
    have hh := ((contDiff_bulkForce a).differentiable (by simp) (Q x)).hasFDerivAt.comp x hDQ.hasFDerivAt
    have hd := (hh.const_smul s).fderiv
    exact DFunLike.congr_fun hd (axis i)
  have hKS : ContDiffOn ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) (fun y => ∑ i, K i y) U :=
    ContDiffOn.sum fun i _ => hK i
  have hKl (i : Fin 3) : laplacian (K i) x =
      2 * (frobeniusS0 (laplacian (coordDeriv i Q) x) (coordDeriv i Q x) +
        ∑ j, ‖coordDeriv j (coordDeriv i Q) x‖ ^ 2) :=
    laplacian_frobeniusS0_self hU (hD i) hx
  have hEqP := laplacian_bulkPotential a hU hQ hx
  change laplacian (fun y => (1 / 2 : ℝ) • (∑ i, K i y) + s • P y) x = _
  rw [laplacian_add hU (hKS.const_smul _) (hP.const_smul _) hx,
    laplacian_const_smul hU (hKS.of_le (WithTop.coe_le_coe.mpr le_top)) hx,
    laplacian_const_smul hU (hP.of_le (WithTop.coe_le_coe.mpr le_top)) hx,
    laplacian_sum hU (fun i _ => hK i) hx]
  simp_rw [hKl, hEC]
  rw [show laplacian P x = _ from hEqP, hE x hx]
  have hLeft (B D : S0) : frobeniusS0 (s • B) D = s * frobeniusS0 B D := by
    rw [← frobeniusCoordinateEquiv_inner, map_smul, real_inner_smul_left, frobeniusCoordinateEquiv_inner]
  have hRight (B D : S0) : frobeniusS0 B (s • D) = s * frobeniusS0 B D := by
    rw [← frobeniusCoordinateEquiv_inner, map_smul, real_inner_smul_right, frobeniusCoordinateEquiv_inner]
  simp only [hLeft, hRight, frobeniusS0_self, Finset.sum_add_distrib, ← Finset.mul_sum, smul_eq_mul, L, s]
  ring

private theorem norm_sq_smul_add_smul (A B : S0) (c d : ℝ) :
    ‖c • A + d • B‖ ^ 2 =
      c ^ 2 * ‖A‖ ^ 2 + 2 * c * d * frobeniusS0 A B + d ^ 2 * ‖B‖ ^ 2 := by
  rw [← frobeniusCoordinateEquiv.norm_map (c • A + d • B), map_add, map_smul, map_smul, norm_add_sq_real]
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, frobeniusCoordinateEquiv.norm_map,
    real_inner_smul_left, real_inner_smul_right, frobeniusCoordinateEquiv_inner]
  ring

/-- The force controls the distance to the vacuum uniformly on a fixed
tube. The two material coefficients are recovered from the Gram estimate
for the tensor and its trace-free square. -/
theorem exists_bulkForce_distance_lower (a : BulkCoefficients) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧
      ∀ A ∈ vacuumTube a δ, Metric.infDist A (vacuum a) ≤ C * ‖bulkForce a A‖ := by
  let r := vacuumRadius a
  have hr : 0 < r := vacuumRadius_pos a
  let m := min (2 * r ^ 2) (2 * r ^ 4 / 3)
  have hm : 0 < m := lt_min (by positivity) (by positivity)
  let g (A : S0) := min (‖A‖ ^ 2) (‖traceFreeSquare A‖ ^ 2) -
    |frobeniusS0 A (traceFreeSquare A)|
  have hInner : Continuous (fun A : S0 => frobeniusS0 A (traceFreeSquare A)) := by
    let e := frobeniusCoordinateEquiv
    have h1 : Continuous (fun A : S0 => e A) := e.continuous
    have h2 : Continuous (fun A : S0 => e (traceFreeSquare A)) :=
      e.continuous.comp contDiff_traceFreeSquare.continuous
    have hI : Continuous (fun A : S0 => inner ℝ (e A) (e (traceFreeSquare A))) := h1.inner h2
    simpa only [e, frobeniusCoordinateEquiv_inner] using hI
  have hg : Continuous g := (continuous_norm.pow 2 |>.min
    ((contDiff_traceFreeSquare.continuous.norm).pow 2)).sub hInner.abs
  let V := {A | m / 2 < g A}
  have hV : IsOpen V := isOpen_lt continuous_const hg
  have hVacSub : vacuum a ⊆ V := by
    intro A hA
    obtain ⟨hA₁, hA₂, hA₃⟩ := vacuum_normal_basis_pairings hA
    change m / 2 < min (‖A‖ ^ 2) (‖traceFreeSquare A‖ ^ 2) - |frobeniusS0 A (traceFreeSquare A)|
    rw [← frobeniusS0_self A, ← frobeniusS0_self (traceFreeSquare A), hA₁, hA₂, hA₃, abs_zero, sub_zero]
    exact half_lt_self hm
  obtain ⟨δ₁, hδ₁, hCover⟩ := (isCompact_vacuum a).exists_thickening_subset_open hV hVacSub
  obtain ⟨K, δ₂, hK, hδ₂, hInvariant⟩ := exists_vacuumInvariantErrorBound a
  let δ := min δ₁ δ₂
  let b := min a.a4 a.a6'
  have hb : 0 < b := lt_min a.a4_pos a.a6'_pos
  let k := Real.sqrt (m / 2) * b
  have hk : 0 < k := mul_pos (Real.sqrt_pos.mpr (half_pos hm)) hb
  refine ⟨δ, K / k, lt_min hδ₁ hδ₂, div_pos hK hk, ?_⟩
  intro A hA
  have hAd : Metric.infDist A (vacuum a) < δ := hA
  have hG : A ∈ V := hCover ((Metric.mem_thickening_iff_infDist_lt (vacuum_nonempty a)).mpr
    (hAd.trans_le (min_le_left _ _)))
  let T := traceFreeSquare A
  let t := (vacuumInvariants A).1
  let s := (vacuumInvariants A).2
  let f := -a.a2 + a.a4 * t + a.a6 * t ^ 2
  let e := a.a6' * s
  let μ := preferredTraceSq a
  let p := frobeniusS0 A T
  have hG' : m / 2 < min (‖A‖ ^ 2) (‖T‖ ^ 2) - |p| := hG
  have hDiag₁ : m / 2 + |p| ≤ ‖A‖ ^ 2 :=
    (le_sub_iff_add_le.mp hG'.le).trans (min_le_left _ _)
  have hDiag₂ : m / 2 + |p| ≤ ‖T‖ ^ 2 :=
    (le_sub_iff_add_le.mp hG'.le).trans (min_le_right _ _)
  have hForce : bulkForce a A = f • A + e • T := bulkForce_eq_smul_components a A
  have hCrossAbs : |2 * f * e * p| ≤ (f ^ 2 + e ^ 2) * |p| := by
    have hTwo : 2 * |f| * |e| ≤ f ^ 2 + e ^ 2 := by
      nlinarith only [sq_nonneg (|f| - |e|), sq_abs f, sq_abs e]
    simpa only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] using
      mul_le_mul_of_nonneg_right hTwo (abs_nonneg p)
  have hCross := (neg_le_neg hCrossAbs).trans (neg_abs_le (2 * f * e * p))
  have hSq : (m / 2) * (f ^ 2 + e ^ 2) ≤ ‖bulkForce a A‖ ^ 2 := by
    rw [hForce, norm_sq_smul_add_smul]
    change _ ≤ f ^ 2 * ‖A‖ ^ 2 + 2 * f * e * p + e ^ 2 * ‖T‖ ^ 2
    have h₁ := mul_le_mul_of_nonneg_left hDiag₁ (sq_nonneg f)
    have h₂ := mul_le_mul_of_nonneg_left hDiag₂ (sq_nonneg e)
    linarith only [h₁, h₂, hCross]
  have hRoot : (Real.sqrt (m / 2)) ^ 2 = m / 2 := Real.sq_sqrt (half_pos hm).le
  have hAbsBound (u : ℝ) (hu : u ^ 2 ≤ f ^ 2 + e ^ 2) :
      Real.sqrt (m / 2) * |u| ≤ ‖bulkForce a A‖ := by
    apply (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)) (norm_nonneg _)).mp
    rw [mul_pow, hRoot, sq_abs]
    exact (mul_le_mul_of_nonneg_left hu (half_pos hm).le).trans hSq
  have hA4 : a.a4 ≤ a.a4 + a.a6 * (t + μ) := by
    have ht : 0 ≤ t := A.trace_sq_nonneg
    exact le_add_of_nonneg_right (mul_nonneg a.a6_pos.le (add_nonneg ht (preferredTraceSq_pos a).le))
  have hFact : f = (a.a4 + a.a6 * (t + μ)) * (t - μ) := by
    change -a.a2 + a.a4 * t + a.a6 * t ^ 2 = (a.a4 + a.a6 * (t + μ)) * (t - μ)
    rw [show a.a2 = a.a6 * μ ^ 2 + a.a4 * μ from (preferredTraceSq_equation a).symm]
    ring
  have hfLower : b * |t - μ| ≤ |f| := by
    rw [hFact, abs_mul, abs_of_pos (a.a4_pos.trans_le hA4)]
    exact mul_le_mul_of_nonneg_right ((min_le_left _ _).trans hA4) (abs_nonneg _)
  have heLower : b * |s| ≤ |e| := by
    change _ ≤ |a.a6' * s|
    rw [abs_mul, abs_of_pos a.a6'_pos]
    exact mul_le_mul_of_nonneg_right (min_le_right _ _) (abs_nonneg _)
  have hOne (u v : ℝ) (hUV : b * |u| ≤ |v|) (hv : v ^ 2 ≤ f ^ 2 + e ^ 2) :
      |u| ≤ ‖bulkForce a A‖ / k := by
    apply (le_div_iff₀ hk).mpr
    change |u| * (Real.sqrt (m / 2) * b) ≤ _
    rw [mul_comm |u|, mul_assoc]
    exact (mul_le_mul_of_nonneg_left hUV (Real.sqrt_nonneg _)).trans (hAbsBound v hv)
  have hInv : vacuumInvariantError a A ≤ ‖bulkForce a A‖ / k := by
    change ‖(t, s) - (2 * r ^ 2, 0)‖ ≤ _
    rw [Prod.norm_def, Prod.fst_sub, Prod.snd_sub, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs,
      show 2 * r ^ 2 = μ from two_mul_vacuumRadius_sq a]
    exact max_le (hOne (t - μ) f hfLower (le_add_of_nonneg_right (sq_nonneg e)))
      (hOne s e heLower (le_add_of_nonneg_left (sq_nonneg f)))
  calc
    _ ≤ K * vacuumInvariantError a A := hInvariant A (hAd.trans_le (min_le_right _ _))
    _ ≤ K * (‖bulkForce a A‖ / k) := mul_le_mul_of_nonneg_left hInv hK.le
    _ = _ := by ring

/-- The derivative of the material force is nonnegative in the Frobenius
pairing at every vacuum tensor. -/
theorem bulkForce_fderiv_frobenius_nonneg_of_mem_vacuum
    {a : BulkCoefficients} {A : S0} (hA : A ∈ vacuum a) (B : S0) :
    0 ≤ frobeniusS0 ((fderiv ℝ (bulkForce a) A) B) B := by
  have hAB : ((A : Tensor) * (B : Tensor)).trace = frobeniusS0 A B := by
    rw [frobeniusS0, frobenius, A.transpose_eq]
  have hTB : (((A : Tensor) ^ 2) * (B : Tensor)).trace = frobeniusS0 (traceFreeSquare A) B := by
    rw [frobeniusS0, frobenius, (traceFreeSquare A).transpose_eq, traceFreeSquare_coe]
    simp only [
      Matrix.sub_mul, Matrix.trace_sub, Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul,
      B.trace_eq_zero, smul_eq_mul, mul_zero, sub_zero]
  rw [fderiv_bulkForce_at_vacuum hA, bulkForceLinearization_apply, hAB, hTB,
    ← frobeniusCoordinateEquiv_inner, map_add, map_smul, map_smul, inner_add_left,
    real_inner_smul_left, real_inner_smul_left, frobeniusCoordinateEquiv_inner,
    frobeniusCoordinateEquiv_inner]
  have h := add_nonneg
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (bulkRadialCoefficient_pos a).le)
      (sq_nonneg (frobeniusS0 A B)))
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) a.a6'_pos.le)
      (sq_nonneg (frobeniusS0 (traceFreeSquare A) B)))
  nlinarith only [h]

private theorem exists_norm_image_sub_le_of_smooth_closedBall
    {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace ℝ E] [NormedSpace ℝ F] [ProperSpace E]
    {f : E → F} (hf : ContDiff ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) f) (R : ℝ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x ∈ Metric.closedBall (0 : E) R, ∀ y ∈ Metric.closedBall (0 : E) R,
      ‖f x - f y‖ ≤ L * ‖x - y‖ := by
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : E) R).exists_bound_of_continuousOn
    (hf.continuous_fderiv (by simp)).continuousOn
  refine ⟨max M 0, le_max_right _ _, fun x hx y hy => ?_⟩
  exact (convex_closedBall (0 : E) R).norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => hf.differentiable (by simp) z) (fun z hz => (hM z hz).trans (le_max_left _ _)) hy hx

local instance bulkForceDerivativeNorm : Norm (S0 →L[ℝ] S0) :=
  ContinuousLinearMap.hasOpNorm (σ₁₂ := RingHom.id ℝ) (E := S0) (F := S0)

local instance bulkForceDerivativeNormedGroup : NormedAddCommGroup (S0 →L[ℝ] S0) :=
  ContinuousLinearMap.toNormedAddCommGroup (σ₁₂ := RingHom.id ℝ) (E := S0) (F := S0)

local instance bulkForceDerivativeNormedSpace : NormedSpace ℝ (S0 →L[ℝ] S0) :=
  ContinuousLinearMap.toNormedSpace (σ₁₂ := RingHom.id ℝ) (E := S0) (F := S0)

/-- On a fixed tube, the negative part of the force derivative is bounded
by the force size times the squared Frobenius norm of the direction. -/
theorem exists_bulkForce_fderiv_frobenius_lower (a : BulkCoefficients) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧ ∀ A ∈ vacuumTube a δ, ∀ B : S0,
      -(C * ‖bulkForce a A‖ * ‖B‖ ^ 2) ≤ frobeniusS0 ((fderiv ℝ (bulkForce a) A) B) B := by
  obtain ⟨δ₀, N, hδ₀, hN, hForce⟩ := exists_bulkForce_distance_lower a
  let δ := min δ₀ 1
  let R := Real.sqrt 2 * vacuumRadius a + 1
  let J := fderiv ℝ (bulkForce a)
  have hJ : ContDiff ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) J := (contDiff_bulkForce a).fderiv_right (by simp)
  obtain ⟨L, hL, hLip⟩ := exists_norm_image_sub_le_of_smooth_closedBall hJ R
  refine ⟨δ, L * N, lt_min hδ₀ zero_lt_one, mul_nonneg hL hN.le, ?_⟩
  intro A hA B
  have hAd : Metric.infDist A (vacuum a) < δ := hA
  let P := (spectralVacuumPoint a A).val
  have hP : P ∈ vacuum a := (spectralVacuumPoint a A).property
  have hpNorm : ‖P‖ = Real.sqrt 2 * vacuumRadius a := vacuum_norm hP
  have hDist : ‖A - P‖ = Metric.infDist A (vacuum a) := by
    rw [← dist_eq_norm]
    exact spectralVacuumPoint_dist_eq_infDist a A
  have hAB : A ∈ Metric.closedBall (0 : S0) R := by
    rw [Metric.mem_closedBall, dist_zero_right]
    have hTri := norm_add_le (A - P) P
    rw [sub_add_cancel, hpNorm, hDist] at hTri
    refine hTri.trans ?_
    dsimp only [R]
    linarith only [hAd.le.trans (min_le_right δ₀ (1 : ℝ))]
  have hPB : P ∈ Metric.closedBall (0 : S0) R := by
    rw [Metric.mem_closedBall, dist_zero_right, hpNorm]
    exact le_add_of_nonneg_right zero_le_one
  have hDiff := hLip A hAB P hPB
  let D := J A - J P
  have hFrob : |frobeniusS0 (D B) B| ≤ ‖D‖ * ‖B‖ ^ 2 := by
    have h := abs_real_inner_le_norm (frobeniusCoordinateEquiv (D B)) (frobeniusCoordinateEquiv B)
    rw [frobeniusCoordinateEquiv_inner, LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map] at h
    calc
      _ ≤ ‖D B‖ * ‖B‖ := h
      _ ≤ (‖D‖ * ‖B‖) * ‖B‖ := mul_le_mul_of_nonneg_right (D.le_opNorm B) (norm_nonneg _)
      _ = _ := by rw [mul_assoc, pow_two]
  have hD : ‖D‖ ≤ (L * N) * ‖bulkForce a A‖ := by
    have hd := hForce A (show A ∈ vacuumTube a δ₀ from hAd.trans_le (min_le_left _ _))
    rw [hDist] at hDiff
    calc
      _ ≤ L * Metric.infDist A (vacuum a) := hDiff
      _ ≤ L * (N * ‖bulkForce a A‖) := mul_le_mul_of_nonneg_left hd hL
      _ = _ := (mul_assoc _ _ _).symm
  have hLow := (neg_le_neg (hFrob.trans (mul_le_mul_of_nonneg_right hD (sq_nonneg _)))).trans
    (neg_abs_le (frobeniusS0 (D B) B))
  have hEq : frobeniusS0 (D B) B = frobeniusS0 (J A B) B - frobeniusS0 (J P B) B := by
    change frobeniusS0 ((J A - J P) B) B = _
    rw [sub_apply, ← frobeniusCoordinateEquiv_inner, map_sub, inner_sub_left,
      frobeniusCoordinateEquiv_inner, frobeniusCoordinateEquiv_inner]
  rw [hEq] at hLow
  have hPos : 0 ≤ frobeniusS0 (J P B) B := bulkForce_fderiv_frobenius_nonneg_of_mem_vacuum hP B
  exact hLow.trans (sub_le_self _ hPos)

/-- The energy density of a classical solution is a quadratic subsolution
on the fixed material tube. The radius and constant are independent of
the domain, point, scale and solution. -/
theorem exists_near_vacuum_classicalEnergyDensity_bochner_bound (a : BulkCoefficients) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧ ∀ (ε : ElasticScale) (U : Set Point), IsOpen U →
      ∀ Q : Point → S0, ContDiffOn ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) Q U →
        (∀ x ∈ U, (ε : ℝ) ^ 2 • (↑(laplacian Q x) : Tensor) = bulkGradient a (Q x)) →
        ∀ x ∈ U, Q x ∈ vacuumTube a δ →
          let e (y : Point) := energyDensity a ε (Q y) (ClassicalGradient Q y);
          -laplacian e x ≤ C * (e x) ^ 2 := by
  obtain ⟨δ, B, hδ, hB, hMaterial⟩ := exists_bulkForce_fderiv_frobenius_lower a
  refine ⟨δ, 4 * B ^ 2 + 1, hδ, by positivity, ?_⟩
  intro ε U hU Q hQ hEuler x hx hTube
  let s : ℝ := (ε : ℝ)⁻¹ ^ 2
  let p := ‖bulkForce a (Q x)‖
  let G := gradientNormSq (ClassicalGradient Q x)
  let e (y : Point) := energyDensity a ε (Q y) (ClassicalGradient Q y)
  let F (j : Fin 3) := frobeniusS0 ((fderiv ℝ (bulkForce a) (Q x)) (coordDeriv j Q x)) (coordDeriv j Q x)
  have hG : 0 ≤ G := by
    change 0 ≤ gradientNormSq (ClassicalGradient Q x)
    rw [gradientNormSq_eq_sum_norm_sq]
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hG2 : G ≤ 2 * e x := by
    have hp : 0 ≤ s * bulkPotential a (Q x) := mul_nonneg (sq_nonneg _) (bulkPotential_nonneg _ _)
    change G ≤ 2 * ((1 / 2 : ℝ) * G + s * bulkPotential a (Q x))
    linarith only [hp]
  have hForce : -(B * p) * G ≤ ∑ j, F j := by
    change -(B * p) * gradientNormSq (ClassicalGradient Q x) ≤ _
    rw [gradientNormSq_eq_sum_norm_sq, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    simpa only [ClassicalGradient, p, F, neg_mul] using hMaterial (Q x) hTube (coordDeriv j Q x)
  have hTwo := mul_le_mul_of_nonneg_left hForce (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (sq_nonneg (ε : ℝ)⁻¹))
  have hDer := classicalEnergyDensity_laplacian_bochner a ε hU hQ hEuler hx
  have hs : (ε : ℝ)⁻¹ ^ 4 = s ^ 2 := by dsimp only [s]; ring
  rw [hs] at hDer
  change laplacian e x = (∑ i, ∑ j, ‖coordDeriv j (coordDeriv i Q) x‖ ^ 2) +
    (2 * s) * (∑ j, F j) + s ^ 2 * p ^ 2 at hDer
  have hDerNonneg : 0 ≤ ∑ i : Fin 3, ∑ j : Fin 3, ‖coordDeriv j (coordDeriv i Q) x‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  change -laplacian e x ≤ (4 * B ^ 2 + 1) * (e x) ^ 2
  calc
    _ ≤ 2 * s * B * p * G - s ^ 2 * p ^ 2 := by linarith only [hDer, hTwo, hDerNonneg]
    _ ≤ B ^ 2 * G ^ 2 := by nlinarith only [sq_nonneg (s * p - B * G)]
    _ ≤ B ^ 2 * (2 * e x) ^ 2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hG hG2 2) (sq_nonneg _)
    _ ≤ _ := by nlinarith only [sq_nonneg (e x)]

end Thesis

end
