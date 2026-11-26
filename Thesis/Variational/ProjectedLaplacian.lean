module

public import Thesis.Variational.ScaledDefects
public import Thesis.Foundation.SpectralProjection
import Thesis.Foundation.LinearizedBulk

/-! Spectral force cancellation and the Laplacian of the nearest vacuum projection. -/

public section

open Filter Set Topology
open scoped BigOperators ContDiff Matrix Matrix.Norms.Frobenius RealInnerProductSpace

set_option autoImplicit false
noncomputable section

namespace Thesis

private theorem toEuclideanLin_eq_of_mulVec {A : S0} {v : Point} {s : ℝ}
    (h : (A : Tensor) *ᵥ v.ofLp = s • v.ofLp) :
    (A : Tensor).toEuclideanLin v = s • v := by
  apply PiLp.ext
  intro i
  exact congrFun h i

private theorem tensorRayleigh_eq_weighted_of_eigenbasis
    (A : S0) (b : OrthonormalBasis (Fin 3) ℝ Point) (ℓ : Fin 3 → ℝ)
    (hb : ∀ i, (A : Tensor) *ᵥ (b i).ofLp = ℓ i • (b i).ofLp) (v : Point) :
    tensorRayleigh A v = ∑ i, ℓ i * (b.repr v i) ^ 2 := by
  let T := (A : Tensor).toEuclideanLin
  have hT : T.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr A.isHermitian
  have hrepr (i : Fin 3) : b.repr (T v) i = ℓ i * b.repr v i := by
    rw [b.repr_apply_apply, ← hT, toEuclideanLin_eq_of_mulVec (hb i), inner_smul_left]
    change ℓ i * inner ℝ (b i) v = _
    rw [← b.repr_apply_apply]
  change inner ℝ v (T v) = _
  rw [← b.repr.inner_map_map v (T v), EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  refine Finset.sum_congr rfl fun i _ => ?_
  change b.repr (T v) i * b.repr v i = ℓ i * (b.repr v i) ^ 2
  rw [hrepr]
  ring

private theorem traceFreeSquare_mulVec_orderedEigenbasis (A : S0) (i : Fin 3) :
    (traceFreeSquare A : Tensor) *ᵥ (orderedEigenbasis A i).ofLp =
      ((orderedEigenvalue A i) ^ 2 - (((A : Tensor) ^ 2).trace / 3)) • (orderedEigenbasis A i).ofLp := by
  rw [traceFreeSquare_coe, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, pow_two,
    ← Matrix.mulVec_mulVec, orderedEigenbasis_mulVec, Matrix.mulVec_smul, orderedEigenbasis_mulVec,
    smul_smul, ← sub_smul, pow_two]

/-- A perturbation in a linear combination of the two spectral directions
preserves the nearest vacuum tensor for all sufficiently small parameters. -/
theorem eventually_vacuum_projection_constant_along_spectral_direction
    {a : BulkCoefficients} (p : VacuumTubularProjection a) {A : S0}
    (hA : A ∈ vacuumTube a p.radius) (hSimple : A ∈ simpleSpectrumLocus)
    (u v : ℝ) :
    ∀ᶠ t : ℝ in 𝓝 0, p.extend (A + t • (u • A + v • traceFreeSquare A)) = p.extend A := by
  let b := orderedEigenbasis A
  let P := spectralVacuumPoint a A
  let B (t : ℝ) := A + t • (u • A + v • traceFreeSquare A)
  let ℓ (t : ℝ) (i : Fin 3) := orderedEigenvalue A i + t *
    (u * orderedEigenvalue A i + v * ((orderedEigenvalue A i) ^ 2 - (((A : Tensor) ^ 2).trace / 3)))
  have hEig (t : ℝ) (i : Fin 3) :
      (B t : Tensor) *ᵥ (b i).ofLp = ℓ t i • (b i).ofLp := by
    change ((A : Tensor) + t • (u • (A : Tensor) + v • (traceFreeSquare A : Tensor))) *ᵥ
      (orderedEigenbasis A i).ofLp = _
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
      orderedEigenbasis_mulVec, traceFreeSquare_mulVec_orderedEigenbasis, smul_smul, smul_smul, ← add_smul,
      smul_smul, ← add_smul]
  have hB : Continuous B := continuous_const.add (continuous_id.smul continuous_const)
  have hB0 : B 0 = A := by simp only [B, zero_smul, add_zero]
  have hNearTube : ∀ᶠ t in 𝓝 0, B t ∈ vacuumTube a p.radius := by
    apply hB.continuousAt.tendsto
    rw [hB0]
    exact (isOpen_vacuumTube a p.radius).mem_nhds hA
  have hC (i : Fin 3) : Continuous (fun t => ℓ t i) := by
    dsimp only [ℓ]
    exact continuous_const.add (continuous_id.mul continuous_const)
  have hNearMax : ∀ᶠ t in 𝓝 0, ℓ t 1 < ℓ t 0 :=
    (hC 1).continuousAt.eventually_lt (hC 0).continuousAt (by simpa only [ℓ, zero_mul, add_zero] using hSimple.1)
  have hNearMin : ∀ᶠ t in 𝓝 0, ℓ t 2 < ℓ t 1 :=
    (hC 2).continuousAt.eventually_lt (hC 1).continuousAt (by simpa only [ℓ, zero_mul, add_zero] using hSimple.2)
  filter_upwards [hNearTube, hNearMax, hNearMin] with t ht hMax hMin
  have hEnds (i : Fin 3) : ℓ t 2 ≤ ℓ t i ∧ ℓ t i ≤ ℓ t 0 := by
    fin_cases i
    · exact ⟨hMin.le.trans hMax.le, le_rfl⟩
    · exact ⟨hMin.le, hMax.le⟩
    · exact ⟨le_rfl, hMin.le.trans hMax.le⟩
  have hNorm (n : Point) (hn : ‖n‖ = 1) : ∑ i, (b.repr n i) ^ 2 = 1 := by
    simpa only [OrthonormalBasis.repr_apply_apply, hn, one_pow] using b.sum_sq_inner_right n
  have hRay (n : Point) (hn : ‖n‖ = 1) :
      ℓ t 2 ≤ tensorRayleigh (B t) n ∧ tensorRayleigh (B t) n ≤ ℓ t 0 := by
    rw [tensorRayleigh_eq_weighted_of_eigenbasis (B t) b (ℓ t) (hEig t)]
    constructor
    · calc
        _ = ∑ i, ℓ t 2 * (b.repr n i) ^ 2 := by rw [← Finset.mul_sum, hNorm n hn, mul_one]
        _ ≤ _ := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hEnds i).1 (sq_nonneg _)
    · calc
        _ ≤ ∑ i, ℓ t 0 * (b.repr n i) ^ 2 :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hEnds i).2 (sq_nonneg _)
        _ = _ := by rw [← Finset.mul_sum, hNorm n hn, mul_one]
  have hRayEig (i : Fin 3) : tensorRayleigh (B t) (b i) = ℓ t i := by
    rw [tensorRayleigh, toEuclideanLin_eq_of_mulVec (hEig t i), real_inner_smul_right,
      real_inner_self_eq_norm_sq, b.orthonormal.norm_eq_one i, one_pow, mul_one]
  have hNear (P' : vacuum a) : dist (B t) P.val ≤ dist (B t) P'.val := by
    obtain ⟨n, m, hn, hm, _, hForm⟩ := P'.property
    apply (sq_le_sq₀ dist_nonneg dist_nonneg).mp
    rw [dist_sq_of_biaxial (B t) P (spectralVacuumPoint_coe a A), dist_sq_of_biaxial (B t) P' hForm,
      hRayEig, hRayEig]
    have hDiff := sub_le_sub (hRay n hn).2 (hRay m hm).1
    exact sub_le_sub_left (mul_le_mul_of_nonneg_left hDiff (by
      have := vacuumRadius_pos a; positivity)) _
  have hP₁ : P = p.project ⟨B t, ht⟩ := p.unique ⟨B t, ht⟩ P hNear
  have hP₀ : P = p.project ⟨A, hA⟩ := spectralVacuumPoint_eq_tubeProjection p ⟨A, hA⟩
  change p.extend (B t) = p.extend A
  rw [p.extend_eq ⟨B t, ht⟩, p.extend_eq ⟨A, hA⟩, ← hP₁, ← hP₀]

/-- The force direction is in the kernel of the derivative of the
nearest-point projection on the simple-spectrum tube. -/
theorem fderiv_vacuum_projection_bulkForce_eq_zero
    {a : BulkCoefficients} (p : VacuumTubularProjection a) {A : S0}
    (hA : A ∈ vacuumTube a p.radius) (hSimple : A ∈ simpleSpectrumLocus) :
    (fderiv ℝ p.extend A) (bulkForce a A) = 0 := by
  let γ (t : ℝ) := A + t • bulkForce a A
  have hγ0 : γ 0 = A := by simp only [γ, zero_smul, add_zero]
  have hγ : HasDerivAt γ (bulkForce a A) 0 := by
    simpa only [γ, id_eq, one_smul] using!
      ((hasDerivAt_id (0 : ℝ)).smul_const (bulkForce a A)).const_add A
  have hDP : HasFDerivAt p.extend (fderiv ℝ p.extend A) (γ 0) := by
    rw [hγ0]
    exact (p.contDiff_extend.differentiable (by simp) A).hasFDerivAt
  have hD := hDP.comp_hasDerivAt 0 hγ
  have hEq : p.extend ∘ γ =ᶠ[𝓝 (0 : ℝ)] (fun _ => p.extend A) := by
    change ∀ᶠ t : ℝ in 𝓝 0, p.extend (A + t • bulkForce a A) = p.extend A
    simpa only [bulkForce_eq_smul_components] using
      eventually_vacuum_projection_constant_along_spectral_direction p hA hSimple
        (-a.a2 + a.a4 * (vacuumInvariants A).1 + a.a6 * (vacuumInvariants A).1 ^ 2)
        (a.a6' * (vacuumInvariants A).2)
  exact hD.unique ((hasDerivAt_const 0 (p.extend A)).congr_of_eventuallyEq hEq)

/-- The classical Laplacian chain rule, with the second Fréchet derivative
evaluated on each actual spatial derivative column. -/
theorem laplacian_comp_smooth_map
    {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace ℝ E] [NormedSpace ℝ F] {f : E → F}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) f)
    {U : Set Point} (hU : IsOpen U) {u : Point → E} (hu : ContDiffOn ℝ 2 u U)
    {x : Point} (hx : x ∈ U) :
    laplacian (f ∘ u) x = (fderiv ℝ f (u x)) (laplacian u x) +
      ∑ j, ((fderiv ℝ (fderiv ℝ f) (u x)) (coordDeriv j u x)) (coordDeriv j u x) := by
  have hDu (y : Point) (hy : y ∈ U) : DifferentiableAt ℝ u y :=
    ((hu y hy).contDiffAt (hU.mem_nhds hy)).differentiableAt two_ne_zero
  have hD₁ : ContDiff ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) (fderiv ℝ f) := hf.fderiv_right (by simp)
  have hD₂ := (hD₁.differentiable (by simp) (u x)).hasFDerivAt.comp x (hDu x hx).hasFDerivAt
  have hJ (j : Fin 3) : coordDeriv j (f ∘ u) =ᶠ[𝓝 x]
      (fun y => (fderiv ℝ f (u y)) (coordDeriv j u y)) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    have h := (hf.differentiable (by simp) (u y)).hasFDerivAt.comp y (hDu y hy).hasFDerivAt
    exact DFunLike.congr_fun h.fderiv (axis j)
  have hTerm (j : Fin 3) : coordDeriv j (coordDeriv j (f ∘ u)) x =
      (fderiv ℝ f (u x)) (coordDeriv j (coordDeriv j u) x) +
        ((fderiv ℝ (fderiv ℝ f) (u x)) (coordDeriv j u x)) (coordDeriv j u x) := by
    have hD := (differentiableAt_coordDeriv_of_contDiffAt
      ((hu x hx).contDiffAt (hU.mem_nhds hx)) j).hasFDerivAt
    have hp := (hD₂.clm_apply hD).congr_of_eventuallyEq (hJ j)
    exact DFunLike.congr_fun hp.fderiv (axis j)
  simp only [laplacian, hTerm, Finset.sum_add_distrib, map_sum]

private theorem exists_hessian_direction_bound_on_closedBall
    {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace ℝ E] [NormedSpace ℝ F] [ProperSpace E] {f : E → F}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) f) (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Metric.closedBall (0 : E) R, ∀ v : E,
      ‖((fderiv ℝ (fderiv ℝ f) x) v) v‖ ≤ C * ‖v‖ ^ 2 := by
  have hSmooth : ContDiff ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) (fderiv ℝ f) := hf.fderiv_right (by simp)
  have h := hSmooth.continuous_fderiv (by simp)
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : E) R).exists_bound_of_continuousOn h.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun x hx v => ?_⟩
  let D := fderiv ℝ (fderiv ℝ f) x
  calc
    ‖(D v) v‖ ≤ ‖D v‖ * ‖v‖ := (D v).le_opNorm v
    _ ≤ (‖D‖ * ‖v‖) * ‖v‖ := mul_le_mul_of_nonneg_right (D.le_opNorm v) (norm_nonneg _)
    _ = ‖D‖ * ‖v‖ ^ 2 := by rw [mul_assoc, pow_two]
    _ ≤ _ := mul_le_mul_of_nonneg_right ((hM x hx).trans (le_max_left _ _)) (sq_nonneg _)

/-- The nearest vacuum projection of a classical penalized solution has
the exact Hessian chain formula and the uniform quadratic Laplacian bound
on a fixed material tube. The positive scale is allowed after dilation. -/
theorem VacuumTubularProjection.exists_projected_laplacian_quadratic_bound
    {a : BulkCoefficients} (p : VacuumTubularProjection a) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧ δ ≤ p.radius ∧
      ∀ (ε : ℝ), 0 < ε → ∀ (U : Set Point), IsOpen U →
        ∀ Q : Point → S0, ContDiffOn ℝ 2 Q U →
          ∀ x ∈ U, Q x ∈ vacuumTube a δ →
            ε ^ 2 • (↑(laplacian Q x) : Tensor) = bulkGradient a (Q x) →
            laplacian (p.extend ∘ Q) x =
              (∑ j, ((fderiv ℝ (fderiv ℝ p.extend) (Q x)) (coordDeriv j Q x)) (coordDeriv j Q x)) ∧
            ‖laplacian (p.extend ∘ Q) x‖ ≤ C * gradientNormSq (ClassicalGradient Q x) := by
  let δ := min p.radius (min (vacuumRadius a / 2) 1)
  let R := Real.sqrt 2 * vacuumRadius a + 1
  obtain ⟨C, hC, hB⟩ := exists_hessian_direction_bound_on_closedBall p.contDiff_extend R
  refine ⟨δ, C + 1, lt_min p.radius_pos (lt_min (half_pos (vacuumRadius_pos a)) zero_lt_one),
    add_pos_of_nonneg_of_pos hC zero_lt_one, min_le_left _ _, ?_⟩
  intro ε hε U hU Q hQ x hx hTube hEuler
  have hDist : Metric.infDist (Q x) (vacuum a) < δ := hTube
  have hTube' : Q x ∈ vacuumTube a p.radius := hDist.trans_le (min_le_left _ _)
  have hSimple : Q x ∈ simpleSpectrumLocus := vacuumTube_vacuumRadius_half_subset_simpleSpectrum a
    (hDist.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
  have hForce := fderiv_vacuum_projection_bulkForce_eq_zero p hTube' hSimple
  have hEq : ε ^ 2 • laplacian Q x = bulkForce a (Q x) := Subtype.ext hEuler
  let D := fderiv ℝ p.extend (Q x)
  have hD : D (laplacian Q x) = 0 := by
    have hScale : ε ^ 2 • D (laplacian Q x) = 0 := by
      rw [← map_smul, hEq]
      exact hForce
    rcases smul_eq_zero.mp hScale with hZero | hZero
    · exact ((sq_pos_of_pos hε).ne' hZero).elim
    · exact hZero
  let H := ∑ j, ((fderiv ℝ (fderiv ℝ p.extend) (Q x)) (coordDeriv j Q x)) (coordDeriv j Q x)
  have hChain : laplacian (p.extend ∘ Q) x = H := calc
    _ = D (laplacian Q x) + H := laplacian_comp_smooth_map p.contDiff_extend hU hQ hx
    _ = 0 + H := congrArg (· + H) hD
    _ = H := zero_add H
  refine ⟨hChain, ?_⟩
  let P := (spectralVacuumPoint a (Q x)).val
  have hP : P ∈ vacuum a := (spectralVacuumPoint a (Q x)).property
  have hNear : ‖Q x - P‖ < 1 := by
    rw [← dist_eq_norm, show dist (Q x) P = Metric.infDist (Q x) (vacuum a) from
      spectralVacuumPoint_dist_eq_infDist a (Q x)]
    exact hDist.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hBall : Q x ∈ Metric.closedBall (0 : S0) R := by
    rw [Metric.mem_closedBall, dist_zero_right]
    have ht := norm_add_le (Q x - P) P
    rw [sub_add_cancel, vacuum_norm hP] at ht
    refine ht.trans ?_
    dsimp only [R]
    linarith only [hNear]
  rw [hChain, gradientNormSq_eq_sum_norm_sq, Finset.mul_sum]
  dsimp only [H]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ =>
    (hB (Q x) hBall (coordDeriv j Q x)).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (sq_nonneg _)))

/-- The nearest vacuum projection of a classical penalized solution has
the exact Hessian chain formula and the uniform quadratic Laplacian bound
on a fixed material tube. The positive scale is allowed after dilation. -/
theorem exists_projected_laplacian_quadratic_bound (a : BulkCoefficients) :
    ∃ (p : VacuumTubularProjection a) (δ C : ℝ), 0 < δ ∧ 0 < C ∧ δ ≤ p.radius ∧
      ∀ (ε : ℝ), 0 < ε → ∀ (U : Set Point), IsOpen U →
        ∀ Q : Point → S0, ContDiffOn ℝ 2 Q U →
          ∀ x ∈ U, Q x ∈ vacuumTube a δ →
            ε ^ 2 • (↑(laplacian Q x) : Tensor) = bulkGradient a (Q x) →
            laplacian (p.extend ∘ Q) x =
              (∑ j, ((fderiv ℝ (fderiv ℝ p.extend) (Q x)) (coordDeriv j Q x)) (coordDeriv j Q x)) ∧
            ‖laplacian (p.extend ∘ Q) x‖ ≤ C * gradientNormSq (ClassicalGradient Q x) := by
  let p := vacuumTubularProjection a
  obtain ⟨δ, C, hδ, hC, hRad, hBound⟩ := p.exists_projected_laplacian_quadratic_bound
  exact ⟨p, δ, C, hδ, hC, hRad, hBound⟩

end Thesis

end
