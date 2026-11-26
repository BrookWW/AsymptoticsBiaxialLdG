module

public import Mathlib.Analysis.Calculus.ImplicitContDiff
public import Thesis.Foundation.VacuumTube

/-! Ordered eigenvalues and the nearest biaxial vacuum tensor. -/

@[expose] public section

set_option autoImplicit false
noncomputable section

open Filter Set
open scoped BigOperators ContDiff Matrix Matrix.Norms.Frobenius Topology

namespace Thesis

private def orderedSpectralIndex : Fin 3 ≃ Fin 3 :=
  (Fin.castOrderIso (Fintype.card_fin 3).symm).toEquiv.trans
    (Fintype.equivOfCardEq (Fintype.card_fin _))

/-- The eigenvalues in descending order, with multiplicity. -/
@[no_expose] def orderedEigenvalue (A : S0) (i : Fin 3) : ℝ :=
  A.isHermitian.eigenvalues (orderedSpectralIndex i)

theorem orderedEigenvalue_antitone (A : S0) : Antitone (orderedEigenvalue A) := by
  have he (i : Fin 3) :
      orderedEigenvalue A i = A.isHermitian.eigenvalues₀ (Fin.cast (Fintype.card_fin 3).symm i) := by
    unfold orderedEigenvalue Matrix.IsHermitian.eigenvalues orderedSpectralIndex
    rw [Equiv.trans_apply, Equiv.symm_apply_apply]
    rfl
  intro i j hij
  rw [he i, he j]
  exact A.isHermitian.eigenvalues₀_antitone (show
    Fin.cast (Fintype.card_fin 3).symm i ≤ Fin.cast (Fintype.card_fin 3).symm j from hij)

theorem trace_pow_eq_sum_orderedEigenvalue_pow (A : S0) (k : ℕ) :
    ((A : Tensor) ^ k).trace = ∑ i, orderedEigenvalue A i ^ k := by
  rw [trace_pow_eq_sum_eigenvalues_pow A.isHermitian]
  exact (Equiv.sum_comp orderedSpectralIndex (fun i => A.isHermitian.eigenvalues i ^ k)).symm

theorem sum_orderedEigenvalue (A : S0) : ∑ i, orderedEigenvalue A i = 0 := by
  simpa only [pow_one, A.trace_eq_zero] using (trace_pow_eq_sum_orderedEigenvalue_pow A 1).symm

/-- An orthonormal eigenbasis indexed in the order of the eigenvalues. -/
@[no_expose] def orderedEigenbasis (A : S0) : OrthonormalBasis (Fin 3) ℝ Point :=
  A.isHermitian.eigenvectorBasis.reindex orderedSpectralIndex.symm

theorem orderedEigenbasis_mulVec (A : S0) (i : Fin 3) :
    (A : Tensor) *ᵥ (orderedEigenbasis A i).ofLp =
      orderedEigenvalue A i • (orderedEigenbasis A i).ofLp := by
  unfold orderedEigenbasis orderedEigenvalue
  rw [OrthonormalBasis.reindex_apply, Equiv.symm_symm]
  exact A.isHermitian.mulVec_eigenvectorBasis _

private theorem orderedEigenbasis_toEuclideanLin (A : S0) (i : Fin 3) :
    (A : Tensor).toEuclideanLin (orderedEigenbasis A i) =
      orderedEigenvalue A i • orderedEigenbasis A i := by
  apply PiLp.ext
  intro j
  exact congrFun (orderedEigenbasis_mulVec A i) j

/-- The quadratic form of a tensor evaluated on a direction. -/
def tensorRayleigh (A : S0) (v : Point) : ℝ :=
  inner ℝ v ((A : Tensor).toEuclideanLin v)

private theorem tensorRayleigh_eq_dotProduct (A : S0) (v : Point) :
    tensorRayleigh A v = ((A : Tensor) *ᵥ v.ofLp) ⬝ᵥ v.ofLp := by
  simp only [tensorRayleigh, EuclideanSpace.inner_eq_star_dotProduct, star_trivial,
    Matrix.ofLp_toLpLin]
  rfl

theorem tensorRayleigh_orderedEigenbasis (A : S0) (i : Fin 3) :
    tensorRayleigh A (orderedEigenbasis A i) = orderedEigenvalue A i := by
  rw [tensorRayleigh, orderedEigenbasis_toEuclideanLin, inner_smul_right,
    real_inner_self_eq_norm_sq, (orderedEigenbasis A).orthonormal.norm_eq_one i, one_pow, mul_one]

private theorem sum_orderedEigenbasis_repr_sq (A : S0) (v : Point) :
    ∑ i, ((orderedEigenbasis A).repr v i) ^ 2 = ‖v‖ ^ 2 := by
  simpa only [OrthonormalBasis.repr_apply_apply] using (orderedEigenbasis A).sum_sq_inner_right v

theorem tensorRayleigh_eq_weighted_eigenvalues (A : S0) (v : Point) :
    tensorRayleigh A v = ∑ i, orderedEigenvalue A i * ((orderedEigenbasis A).repr v i) ^ 2 := by
  let b := orderedEigenbasis A
  let T := (A : Tensor).toEuclideanLin
  have hT : T.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr A.isHermitian
  have hrepr (i : Fin 3) : b.repr (T v) i = orderedEigenvalue A i * b.repr v i := by
    rw [b.repr_apply_apply, ← hT, orderedEigenbasis_toEuclideanLin, inner_smul_left]
    change orderedEigenvalue A i * inner ℝ (b i) v = _
    rw [← b.repr_apply_apply]
  change inner ℝ v (T v) = _
  rw [← b.repr.inner_map_map v (T v), EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  refine Finset.sum_congr rfl fun i _ => ?_
  change b.repr (T v) i * b.repr v i = orderedEigenvalue A i * (b.repr v i) ^ 2
  rw [hrepr]
  ring

theorem tensorRayleigh_le_max (A : S0) {v : Point} (hv : ‖v‖ = 1) :
    tensorRayleigh A v ≤ orderedEigenvalue A 0 := by
  rw [tensorRayleigh_eq_weighted_eigenvalues]
  calc
    _ ≤ ∑ i, orderedEigenvalue A 0 * ((orderedEigenbasis A).repr v i) ^ 2 :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right
        (orderedEigenvalue_antitone A (Fin.zero_le i)) (sq_nonneg _)
    _ = _ := by rw [← Finset.mul_sum, sum_orderedEigenbasis_repr_sq, hv, one_pow, mul_one]

theorem min_le_tensorRayleigh (A : S0) {v : Point} (hv : ‖v‖ = 1) :
    orderedEigenvalue A 2 ≤ tensorRayleigh A v := by
  rw [tensorRayleigh_eq_weighted_eigenvalues]
  calc
    _ = ∑ i, orderedEigenvalue A 2 * ((orderedEigenbasis A).repr v i) ^ 2 := by
      rw [← Finset.mul_sum, sum_orderedEigenbasis_repr_sq, hv, one_pow, mul_one]
    _ ≤ _ := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right
      (orderedEigenvalue_antitone A (show i ≤ (2 : Fin 3) from Fin.le_last i)) (sq_nonneg _)

private def biaxialVacuumPoint (a : BulkCoefficients) (n m : Point) (hn : ‖n‖ = 1) (hm : ‖m‖ = 1)
    (hnm : inner ℝ n m = 0) : vacuum a := by
  let P := biaxialTensor a n m
  have hntr : ((fun i => n i) ⬝ᵥ (fun i => n i)) = 1 := by
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, hn, one_pow] using
      real_inner_self_eq_norm_sq n
  have hmtr : ((fun i => m i) ⬝ᵥ (fun i => m i)) = 1 := by
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, hm, one_pow] using
      real_inner_self_eq_norm_sq m
  have hP : P ∈ symmetricTraceless := by
    change Pᵀ = P ∧ P.trace = 0
    constructor
    · simp only [P, biaxialTensor, Matrix.transpose_smul, Matrix.transpose_sub,
        Matrix.transpose_vecMulVec]
    · change (biaxialTensor a n m).trace = 0
      rw [biaxialTensor, Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_vecMulVec,
        Matrix.trace_vecMulVec, hntr, hmtr, sub_self, smul_zero]
  exact ⟨⟨P, hP⟩, n, m, hn, hm, hnm, rfl⟩

/-- The vacuum tensor formed from a highest and a lowest eigenvector in the ordered frame. -/
@[no_expose] def spectralVacuumPoint (a : BulkCoefficients) (A : S0) : vacuum a :=
  let b := orderedEigenbasis A
  biaxialVacuumPoint a (b 0) (b 2) (b.orthonormal.norm_eq_one _) (b.orthonormal.norm_eq_one _)
    (b.inner_eq_zero (by decide : (0 : Fin 3) ≠ 2))

theorem spectralVacuumPoint_coe (a : BulkCoefficients) (A : S0) :
    ((spectralVacuumPoint a A).val : Tensor) =
      biaxialTensor a (orderedEigenbasis A 0) (orderedEigenbasis A 2) := by
  unfold spectralVacuumPoint biaxialVacuumPoint
  rfl

private theorem trace_mul_biaxialTensor (a : BulkCoefficients) (A : S0) (n m : Point) :
    ((A : Tensor) * biaxialTensor a n m).trace =
      vacuumRadius a * (tensorRayleigh A n - tensorRayleigh A m) := by
  rw [biaxialTensor, Matrix.mul_smul, Matrix.trace_smul, Matrix.mul_sub, Matrix.trace_sub,
    Matrix.mul_vecMulVec, Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, Matrix.trace_vecMulVec,
    tensorRayleigh_eq_dotProduct, tensorRayleigh_eq_dotProduct, smul_eq_mul]

theorem dist_sq_of_biaxial {a : BulkCoefficients} (A : S0) (P : vacuum a)
    {n m : Point} (hP : (P.val : Tensor) = biaxialTensor a n m) :
    dist A P.val ^ 2 = ((A : Tensor) ^ 2).trace + 2 * vacuumRadius a ^ 2 -
      2 * vacuumRadius a * (tensorRayleigh A n - tensorRayleigh A m) := by
  rw [dist_eq_norm, norm_sq_eq_trace_sq]
  change (((A : Tensor) - (P.val : Tensor)) ^ 2).trace = _
  rw [pow_two, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.trace_sub,
    Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_mul_comm (P.val : Tensor) (A : Tensor),
    ← pow_two, ← pow_two, (vacuum_traces P.property).1, hP, trace_mul_biaxialTensor]
  ring

theorem spectralVacuumPoint_nearest (a : BulkCoefficients) (A : S0) (P : vacuum a) :
    dist A (spectralVacuumPoint a A).val ≤ dist A P.val := by
  obtain ⟨n, m, hn, hm, _, hP⟩ := P.property
  apply (sq_le_sq₀ dist_nonneg dist_nonneg).mp
  rw [dist_sq_of_biaxial A _ (spectralVacuumPoint_coe a A), dist_sq_of_biaxial A P hP,
    tensorRayleigh_orderedEigenbasis, tensorRayleigh_orderedEigenbasis]
  have hRay := sub_le_sub (tensorRayleigh_le_max A hn) (min_le_tensorRayleigh A hm)
  have hMul : 0 ≤ 2 * vacuumRadius a := by
    have := vacuumRadius_pos a
    positivity
  exact sub_le_sub_left (mul_le_mul_of_nonneg_left hRay hMul) _

theorem spectralVacuumPoint_dist_eq_infDist (a : BulkCoefficients) (A : S0) :
    dist A (spectralVacuumPoint a A).val = Metric.infDist A (vacuum a) := by
  apply le_antisymm
  · exact (Metric.le_infDist (vacuum_nonempty a)).2
      (fun _ hP => spectralVacuumPoint_nearest a A ⟨_, hP⟩)
  · exact Metric.infDist_le_dist_of_mem (spectralVacuumPoint a A).property

/-- The squared distance in the ordered eigenframe, with multiplicities allowed. -/
theorem infDist_vacuum_sq_eq_orderedEigenvalue (a : BulkCoefficients) (A : S0) :
    Metric.infDist A (vacuum a) ^ 2 =
      (orderedEigenvalue A 0 - vacuumRadius a) ^ 2 + orderedEigenvalue A 1 ^ 2 +
        (orderedEigenvalue A 2 + vacuumRadius a) ^ 2 := by
  rw [← spectralVacuumPoint_dist_eq_infDist a A, dist_sq_of_biaxial A _ (spectralVacuumPoint_coe a A),
    tensorRayleigh_orderedEigenbasis, tensorRayleigh_orderedEigenbasis,
    trace_pow_eq_sum_orderedEigenvalue_pow A 2, Fin.sum_univ_three]
  ring

theorem infDist_vacuum_sq_compare_extremalEigenvalues (a : BulkCoefficients) (A : S0) :
    let edge := (orderedEigenvalue A 0 - vacuumRadius a) ^ 2 +
      (orderedEigenvalue A 2 + vacuumRadius a) ^ 2
    edge ≤ Metric.infDist A (vacuum a) ^ 2 ∧
      Metric.infDist A (vacuum a) ^ 2 ≤ 3 * edge := by
  dsimp only
  rw [infDist_vacuum_sq_eq_orderedEigenvalue]
  have hsum : orderedEigenvalue A 0 + orderedEigenvalue A 1 + orderedEigenvalue A 2 = 0 := by
    simpa only [Fin.sum_univ_three] using sum_orderedEigenvalue A
  have hMid : orderedEigenvalue A 1 =
      -((orderedEigenvalue A 0 - vacuumRadius a) + (orderedEigenvalue A 2 + vacuumRadius a)) := by
    linarith only [hsum]
  constructor
  · nlinarith only [sq_nonneg (orderedEigenvalue A 1)]
  · rw [hMid, neg_sq]
    nlinarith only [sq_nonneg ((orderedEigenvalue A 0 - vacuumRadius a) -
      (orderedEigenvalue A 2 + vacuumRadius a))]

theorem spectralVacuumPoint_eq_tubeProjection {a : BulkCoefficients}
    (p : VacuumTubularProjection a) (A : vacuumTube a p.radius) :
    spectralVacuumPoint a A.val = p.project A :=
  p.unique A _ (spectralVacuumPoint_nearest a A.val)

/-- The locus where both adjacent gaps between the ordered eigenvalues are positive. -/
def simpleSpectrumLocus : Set S0 :=
  {A | orderedEigenvalue A 1 < orderedEigenvalue A 0 ∧
    orderedEigenvalue A 2 < orderedEigenvalue A 1}

private theorem unitProjector_eq_of_rayleigh_extreme (A : S0) {v : Point} (hv : ‖v‖ = 1)
    (k : Fin 3) (s : ℝ) (hStrict : ∀ i ≠ k, 0 < s * (orderedEigenvalue A k - orderedEigenvalue A i))
    (heq : tensorRayleigh A v = orderedEigenvalue A k) :
    Matrix.vecMulVec (fun i => v i) (fun i => v i) =
      Matrix.vecMulVec (fun i => orderedEigenbasis A k i) (fun i => orderedEigenbasis A k i) := by
  let b := orderedEigenbasis A
  let c (i : Fin 3) := b.repr v i
  let d (i : Fin 3) := s * (orderedEigenvalue A k - orderedEigenvalue A i)
  have hsumC : ∑ i, (c i) ^ 2 = 1 := by
    change (∑ i, ((orderedEigenbasis A).repr v i) ^ 2) = 1
    rw [sum_orderedEigenbasis_repr_sq, hv, one_pow]
  have hsumRay : ∑ i, orderedEigenvalue A i * (c i) ^ 2 = orderedEigenvalue A k :=
    (tensorRayleigh_eq_weighted_eigenvalues A v).symm.trans heq
  have hsumD : ∑ i, d i * (c i) ^ 2 = 0 := by
    calc
      _ = ∑ i, s * (orderedEigenvalue A k * (c i) ^ 2 - orderedEigenvalue A i * (c i) ^ 2) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        dsimp only [d]
        ring
      _ = _ := by
        rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum, hsumC, hsumRay]
        ring
  have hnonneg (i : Fin 3) : 0 ≤ d i * (c i) ^ 2 := by
    by_cases hi : i = k
    · simp [d, hi]
    · exact mul_nonneg (hStrict i hi).le (sq_nonneg _)
  have hzero (i : Fin 3) (hi : i ≠ k) : c i = 0 := by
    have hDz := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hnonneg i)).1 hsumD i
      (Finset.mem_univ i)
    exact (pow_eq_zero_iff two_ne_zero).mp ((mul_eq_zero.mp hDz).resolve_left (hStrict i hi).ne')
  have hreprV : v = c k • b k := by
    calc
      v = ∑ i, c i • b i := (b.sum_repr v).symm
      _ = _ := Finset.sum_eq_single k (fun i _ hi => by rw [hzero i hi, zero_smul]) (by simp)
  have hck : (c k) ^ 2 = 1 := by
    calc
      _ = ∑ i, (c i) ^ 2 := by
        symm
        exact Finset.sum_eq_single k (fun i _ hi => by rw [hzero i hi, zero_pow two_ne_zero]) (by simp)
      _ = _ := hsumC
  ext i j
  change v i * v j = b k i * b k j
  rw [hreprV]
  change (c k * b k i) * (c k * b k j) = _
  calc
    _ = (c k) ^ 2 * (b k i * b k j) := by ring
    _ = _ := by rw [hck, one_mul]

theorem spectralVacuumPoint_eq_of_nearest {a : BulkCoefficients} {A : S0}
    (hA : A ∈ simpleSpectrumLocus) (P : vacuum a)
    (hP : ∀ P' : vacuum a, dist A P.val ≤ dist A P'.val) : P = spectralVacuumPoint a A := by
  obtain ⟨n, m, hn, hm, _, hForm⟩ := P.property
  have hDist : dist A P.val = dist A (spectralVacuumPoint a A).val :=
    le_antisymm (hP _) (spectralVacuumPoint_nearest a A P)
  have hDistSq := congrArg (fun x : ℝ => x ^ 2) hDist
  change dist A P.val ^ 2 = dist A (spectralVacuumPoint a A).val ^ 2 at hDistSq
  rw [dist_sq_of_biaxial A P hForm, dist_sq_of_biaxial A _ (spectralVacuumPoint_coe a A),
    tensorRayleigh_orderedEigenbasis, tensorRayleigh_orderedEigenbasis] at hDistSq
  have hr : 0 < vacuumRadius a := vacuumRadius_pos a
  have hDiffMul : 2 * vacuumRadius a * ((tensorRayleigh A n - tensorRayleigh A m) -
      (orderedEigenvalue A 0 - orderedEigenvalue A 2)) = 0 := by
    linear_combination -hDistSq
  have hDiff := sub_eq_zero.mp ((mul_eq_zero.mp hDiffMul).resolve_left (by positivity))
  have hMax := tensorRayleigh_le_max A hn
  have hMin := min_le_tensorRayleigh A hm
  have hnRay : tensorRayleigh A n = orderedEigenvalue A 0 := by linarith only [hMax, hMin, hDiff]
  have hmRay : tensorRayleigh A m = orderedEigenvalue A 2 := by linarith only [hMax, hMin, hDiff]
  have hStrictMax (i : Fin 3) (hi : i ≠ 0) :
      0 < (1 : ℝ) * (orderedEigenvalue A 0 - orderedEigenvalue A i) := by
    have hi' : (1 : Fin 3) ≤ i := by fin_cases i <;> simp_all
    exact mul_pos zero_lt_one (sub_pos.mpr ((orderedEigenvalue_antitone A hi').trans_lt hA.1))
  have hStrictMin (i : Fin 3) (hi : i ≠ 2) :
      0 < (-1 : ℝ) * (orderedEigenvalue A 2 - orderedEigenvalue A i) := by
    have hi' : i ≤ (1 : Fin 3) := by fin_cases i <;> simp_all
    have h := hA.2.trans_le (orderedEigenvalue_antitone A hi')
    linarith only [h]
  have hnProj := unitProjector_eq_of_rayleigh_extreme A hn 0 1 hStrictMax hnRay
  have hmProj := unitProjector_eq_of_rayleigh_extreme A hm 2 (-1) hStrictMin hmRay
  apply Subtype.ext
  apply Subtype.ext
  simp only [hForm, spectralVacuumPoint_coe, biaxialTensor, hnProj, hmProj]

theorem spectralVacuumPoint_strict_nearest {a : BulkCoefficients} {A : S0}
    (hA : A ∈ simpleSpectrumLocus) {P : vacuum a} (hP : P ≠ spectralVacuumPoint a A) :
    dist A (spectralVacuumPoint a A).val < dist A P.val := by
  apply lt_of_le_of_ne (spectralVacuumPoint_nearest a A P)
  intro heq
  apply hP (spectralVacuumPoint_eq_of_nearest hA P ?_)
  intro P'
  rw [← heq]
  exact spectralVacuumPoint_nearest a A P'

theorem vacuumTube_vacuumRadius_half_subset_simpleSpectrum (a : BulkCoefficients) :
    vacuumTube a (vacuumRadius a / 2) ⊆ simpleSpectrumLocus := by
  intro A hA
  have hr := vacuumRadius_pos a
  have hdist : Metric.infDist A (vacuum a) < vacuumRadius a / 2 := hA
  have hsq := (sq_lt_sq₀ Metric.infDist_nonneg (half_pos hr).le).2 hdist
  rw [infDist_vacuum_sq_eq_orderedEigenvalue] at hsq
  constructor
  · by_contra! h
    have hEq := le_antisymm h (orderedEigenvalue_antitone A (by decide : (0 : Fin 3) ≤ 1))
    rw [hEq] at hsq
    nlinarith only [hsq, sq_nonneg (orderedEigenvalue A 1 - vacuumRadius a / 2),
      sq_nonneg (orderedEigenvalue A 2 + vacuumRadius a), sq_nonneg (vacuumRadius a)]
  · by_contra! h
    have hEq := le_antisymm h (orderedEigenvalue_antitone A (by decide : (1 : Fin 3) ≤ 2))
    rw [← hEq] at hsq
    nlinarith only [hsq, sq_nonneg (orderedEigenvalue A 1 + vacuumRadius a / 2),
      sq_nonneg (orderedEigenvalue A 0 - vacuumRadius a), sq_nonneg (vacuumRadius a)]

theorem exists_vacuumTube_subset_simpleSpectrum (a : BulkCoefficients) :
    let p := vacuumTubularProjection a
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ δ ≤ p.radius ∧ vacuumTube a δ ⊆ simpleSpectrumLocus := by
  let p := vacuumTubularProjection a
  let δ := min p.radius (vacuumRadius a / 2)
  have hδ : δ ≤ p.radius := min_le_left _ _
  refine ⟨δ, lt_min p.radius_pos (half_pos (vacuumRadius_pos a)), hδ.trans_lt p.radius_lt_one,
    hδ, ?_⟩
  intro A hA
  apply vacuumTube_vacuumRadius_half_subset_simpleSpectrum a
  change Metric.infDist A (vacuum a) < δ at hA
  exact hA.trans_le (min_le_right _ _)

private theorem abs_tensorRayleigh_le_norm (A : S0) {v : Point} (hv : ‖v‖ = 1) :
    |tensorRayleigh A v| ≤ ‖A‖ := by
  let V : Tensor := Matrix.vecMulVec (fun i => v i) (fun i => v i)
  let P := traceFreeSymmetricPart V
  have hvv : v.ofLp ⬝ᵥ v.ofLp = 1 := by
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, hv, one_pow] using
      real_inner_self_eq_norm_sq v
  have hNormV : ‖V‖ = 1 := by
    apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
    rw [norm_sq_eq_frobenius, frobenius]
    dsimp only [V]
    rw [Matrix.transpose_vecMulVec, Matrix.vecMulVec_mul_vecMulVec, hvv, one_smul,
      Matrix.trace_vecMulVec, hvv, one_pow]
  have hPNorm : ‖P‖ ≤ 1 := (norm_traceFreeSymmetricPart_le _).trans hNormV.le
  have hPair : frobeniusS0 A P = tensorRayleigh A v := by
    rw [frobeniusS0, frobenius_comm (A : Tensor), frobenius_traceFreeSymmetricPart,
      frobenius_comm V, frobenius, A.transpose_eq]
    dsimp only [V]
    rw [Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, tensorRayleigh_eq_dotProduct]
  let e := frobeniusCoordinateEquiv
  calc
    |tensorRayleigh A v| = |inner ℝ (e A) (e P)| := by rw [frobeniusCoordinateEquiv_inner, hPair]
    _ ≤ ‖e A‖ * ‖e P‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖A‖ := by
      rw [e.norm_map, e.norm_map]
      exact mul_le_of_le_one_right (norm_nonneg _) hPNorm

private theorem abs_tensorRayleigh_sub_le_dist (A B : S0) {v : Point} (hv : ‖v‖ = 1) :
    |tensorRayleigh A v - tensorRayleigh B v| ≤ dist A B := by
  have h : tensorRayleigh (A - B) v = tensorRayleigh A v - tensorRayleigh B v := by
    simp only [tensorRayleigh_eq_dotProduct, Submodule.coe_sub, Matrix.sub_mulVec, sub_dotProduct]
  rw [← h, dist_eq_norm]
  exact abs_tensorRayleigh_le_norm _ hv

private theorem orderedEigenvalue_max_sub_le_dist (A B : S0) :
    orderedEigenvalue A 0 - orderedEigenvalue B 0 ≤ dist A B := by
  let v := orderedEigenbasis A 0
  have hv : ‖v‖ = 1 := (orderedEigenbasis A).orthonormal.norm_eq_one _
  have hA : tensorRayleigh A v = orderedEigenvalue A 0 := tensorRayleigh_orderedEigenbasis A _
  have hB := tensorRayleigh_le_max B hv
  have hDiff := (abs_le.mp (abs_tensorRayleigh_sub_le_dist A B hv)).2
  linarith only [hA, hB, hDiff]

private theorem orderedEigenvalue_min_sub_le_dist (A B : S0) :
    orderedEigenvalue A 2 - orderedEigenvalue B 2 ≤ dist A B := by
  let v := orderedEigenbasis B 2
  have hv : ‖v‖ = 1 := (orderedEigenbasis B).orthonormal.norm_eq_one _
  have hA := min_le_tensorRayleigh A hv
  have hB : tensorRayleigh B v = orderedEigenvalue B 2 := tensorRayleigh_orderedEigenbasis B _
  have hDiff := (abs_le.mp (abs_tensorRayleigh_sub_le_dist A B hv)).2
  linarith only [hA, hB, hDiff]

theorem lipschitzWith_orderedEigenvalue_max : LipschitzWith 1 (fun A : S0 => orderedEigenvalue A 0) := by
  apply LipschitzWith.of_dist_le_mul
  intro A B
  change dist (orderedEigenvalue A 0) (orderedEigenvalue B 0) ≤ (1 : ℝ) * dist A B
  rw [Real.dist_eq, one_mul, abs_le]
  have hAB := orderedEigenvalue_max_sub_le_dist A B
  have hBA := orderedEigenvalue_max_sub_le_dist B A
  rw [dist_comm B A] at hBA
  exact ⟨by linarith only [hBA], hAB⟩

theorem lipschitzWith_orderedEigenvalue_min : LipschitzWith 1 (fun A : S0 => orderedEigenvalue A 2) := by
  apply LipschitzWith.of_dist_le_mul
  intro A B
  change dist (orderedEigenvalue A 2) (orderedEigenvalue B 2) ≤ (1 : ℝ) * dist A B
  rw [Real.dist_eq, one_mul, abs_le]
  have hAB := orderedEigenvalue_min_sub_le_dist A B
  have hBA := orderedEigenvalue_min_sub_le_dist B A
  rw [dist_comm B A] at hBA
  exact ⟨by linarith only [hBA], hAB⟩

theorem orderedEigenvalue_mid (A : S0) :
    orderedEigenvalue A 1 = -orderedEigenvalue A 0 - orderedEigenvalue A 2 := by
  have h := sum_orderedEigenvalue A
  rw [Fin.sum_univ_three] at h
  linarith only [h]

theorem continuous_orderedEigenvalue (i : Fin 3) : Continuous (fun A : S0 => orderedEigenvalue A i) := by
  fin_cases i
  · exact lipschitzWith_orderedEigenvalue_max.continuous
  · change Continuous (fun A : S0 => orderedEigenvalue A 1)
    simp only [orderedEigenvalue_mid]
    exact lipschitzWith_orderedEigenvalue_max.continuous.neg.sub lipschitzWith_orderedEigenvalue_min.continuous
  · exact lipschitzWith_orderedEigenvalue_min.continuous

theorem continuous_orderedSpectrum : Continuous orderedEigenvalue :=
  continuous_pi continuous_orderedEigenvalue

theorem isOpen_simpleSpectrumLocus : IsOpen simpleSpectrumLocus :=
  (isOpen_lt (continuous_orderedEigenvalue 1) (continuous_orderedEigenvalue 0)).inter
    (isOpen_lt (continuous_orderedEigenvalue 2) (continuous_orderedEigenvalue 1))

private def traceCubic (x : (ℝ × ℝ) × ℝ) : ℝ :=
  x.2 ^ 3 - (x.1.1 / 2) * x.2 - x.1.2 / 3

private theorem traceCubic_eq_factor (A : S0) (t : ℝ) :
    traceCubic (vacuumInvariants A, t) =
      (t - orderedEigenvalue A 0) * (t - orderedEigenvalue A 1) * (t - orderedEigenvalue A 2) := by
  unfold traceCubic vacuumInvariants
  rw [trace_pow_eq_sum_orderedEigenvalue_pow A 2, trace_pow_eq_sum_orderedEigenvalue_pow A 3,
    Fin.sum_univ_three, Fin.sum_univ_three, orderedEigenvalue_mid]
  ring

theorem orderedEigenvalue_cubic_equation (A : S0) (i : Fin 3) :
    (orderedEigenvalue A i) ^ 3 - (((A : Tensor) ^ 2).trace / 2) * orderedEigenvalue A i -
      ((A : Tensor) ^ 3).trace / 3 = 0 := by
  change traceCubic (vacuumInvariants A, orderedEigenvalue A i) = 0
  rw [traceCubic_eq_factor]
  fin_cases i <;> simp

private theorem contDiff_traceCubic : ContDiff ℝ ∞ traceCubic := by
  unfold traceCubic
  fun_prop

private def traceCubicSlope (u : (ℝ × ℝ) × ℝ) : ℝ :=
  3 * u.2 ^ 2 - u.1.1 / 2

private theorem traceCubicSlope_at_eigenvalues (A : S0) :
    let v := vacuumInvariants A
    let x := orderedEigenvalue A 0
    let y := orderedEigenvalue A 1
    let z := orderedEigenvalue A 2
    traceCubicSlope (v, x) = (x - y) * (x - z) ∧
      traceCubicSlope (v, y) = (y - x) * (y - z) ∧
      traceCubicSlope (v, z) = (z - x) * (z - y) := by
  dsimp only [traceCubicSlope, vacuumInvariants]
  rw [trace_pow_eq_sum_orderedEigenvalue_pow A 2, Fin.sum_univ_three, orderedEigenvalue_mid]
  constructor
  · ring
  · constructor <;> ring

private theorem traceCubicSlope_ne_zero {A : S0} {i : Fin 3}
    (hi : ∀ j ≠ i, orderedEigenvalue A j ≠ orderedEigenvalue A i) :
    traceCubicSlope (vacuumInvariants A, orderedEigenvalue A i) ≠ 0 := by
  have hs := traceCubicSlope_at_eigenvalues A
  fin_cases i
  · change traceCubicSlope (vacuumInvariants A, orderedEigenvalue A 0) ≠ 0
    rw [hs.1]
    exact mul_ne_zero (sub_ne_zero.mpr (hi 1 (by decide)).symm)
      (sub_ne_zero.mpr (hi 2 (by decide)).symm)
  · change traceCubicSlope (vacuumInvariants A, orderedEigenvalue A 1) ≠ 0
    rw [hs.2.1]
    exact mul_ne_zero (sub_ne_zero.mpr (hi 0 (by decide)).symm)
      (sub_ne_zero.mpr (hi 2 (by decide)).symm)
  · change traceCubicSlope (vacuumInvariants A, orderedEigenvalue A 2) ≠ 0
    rw [hs.2.2]
    exact mul_ne_zero (sub_ne_zero.mpr (hi 0 (by decide)).symm)
      (sub_ne_zero.mpr (hi 1 (by decide)).symm)

private theorem traceCubic_inr_fderiv (u : (ℝ × ℝ) × ℝ) :
    (fderiv ℝ traceCubic u).comp (ContinuousLinearMap.inr ℝ (ℝ × ℝ) ℝ) =
      traceCubicSlope u • ContinuousLinearMap.id ℝ ℝ := by
  have hPair : HasFDerivAt (fun t : ℝ => (u.1, t))
      (ContinuousLinearMap.inr ℝ (ℝ × ℝ) ℝ) u.2 := by
    refine ((hasFDerivAt_const u.1 u.2).prodMk (hasFDerivAt_id u.2)).congr_fderiv ?_
    apply ContinuousLinearMap.ext
    intro v
    rfl
  have hSlice : HasDerivAt (fun t : ℝ => traceCubic (u.1, t)) (traceCubicSlope u) u.2 := by
    have h₁ : HasDerivAt (fun t : ℝ => t ^ 3) (3 * u.2 ^ 2) u.2 := by
      have h := (hasDerivAt_id u.2).pow 3
      change HasDerivAt (fun t : ℝ => t ^ 3) (3 * u.2 ^ (3 - 1) * 1) u.2 at h
      simpa using h
    have h₂ : HasDerivAt (fun t : ℝ => (u.1.1 / 2) * t) (u.1.1 / 2) u.2 := by
      simpa using (hasDerivAt_id u.2).const_mul (u.1.1 / 2)
    exact (h₁.sub h₂).sub_const (u.1.2 / 3)
  have hChain := ((contDiff_traceCubic.differentiable (by simp) u).hasFDerivAt).comp u.2 hPair
  rw [hChain.unique hSlice.hasFDerivAt]
  apply ContinuousLinearMap.ext
  intro v
  exact mul_comm _ _

private theorem traceCubic_inr_isInvertible (u : (ℝ × ℝ) × ℝ) (hu : traceCubicSlope u ≠ 0) :
    ((fderiv ℝ traceCubic u).comp (ContinuousLinearMap.inr ℝ (ℝ × ℝ) ℝ)).IsInvertible := by
  rw [traceCubic_inr_fderiv]
  let d := traceCubicSlope u • ContinuousLinearMap.id ℝ ℝ
  have hd : Function.Bijective d := by
    constructor
    · intro v w h
      exact mul_left_cancel₀ hu h
    · intro w
      refine ⟨w / traceCubicSlope u, ?_⟩
      change traceCubicSlope u * (w / traceCubicSlope u) = w
      field_simp
  refine ⟨(LinearEquiv.ofBijective d.toLinearMap hd).toContinuousLinearEquiv, ?_⟩
  apply ContinuousLinearMap.ext
  intro v
  rfl

/-- An ordered eigenvalue is smooth wherever it is a simple root. -/
theorem contDiffAt_orderedEigenvalue_of_ne {A : S0} {i : Fin 3}
    (hi : ∀ j ≠ i, orderedEigenvalue A j ≠ orderedEigenvalue A i) :
    ContDiffAt ℝ ∞ (fun B : S0 => orderedEigenvalue B i) A := by
  let u := (vacuumInvariants A, orderedEigenvalue A i)
  have hFun : ContDiffAt ℝ ∞ traceCubic u := contDiff_traceCubic.contDiffAt
  have hInv := traceCubic_inr_isInvertible u (traceCubicSlope_ne_zero hi)
  let ψ := hFun.implicitFunction (by simp) hInv
  have hψ : ContDiffAt ℝ ∞ ψ (vacuumInvariants A) := hFun.contDiffAt_implicitFunction (by simp) hInv
  have hNear : ∀ᶠ w in 𝓝 u, traceCubic w = traceCubic u ↔ ψ w.1 = w.2 :=
    hFun.eventually_apply_eq_iff_implicitFunction (by simp) hInv
  have hContinuous : Continuous (fun B : S0 => (vacuumInvariants B, orderedEigenvalue B i)) :=
    contDiff_vacuumInvariants.continuous.prodMk (continuous_orderedEigenvalue i)
  have hNear' := hContinuous.continuousAt.eventually hNear
  have hEq : (fun B => orderedEigenvalue B i) =ᶠ[𝓝 A] (ψ ∘ vacuumInvariants) := by
    filter_upwards [hNear'] with B hB
    have hBRoot : traceCubic (vacuumInvariants B, orderedEigenvalue B i) = 0 :=
      orderedEigenvalue_cubic_equation B i
    have hARoot : traceCubic u = 0 := orderedEigenvalue_cubic_equation A i
    exact (hB.1 (hBRoot.trans hARoot.symm)).symm
  exact (hψ.comp A contDiff_vacuumInvariants.contDiffAt).congr_of_eventuallyEq hEq

private theorem max_gap_orderedEigenvalue_ne {A : S0}
    (h : orderedEigenvalue A 1 < orderedEigenvalue A 0) :
    ∀ j ≠ 0, orderedEigenvalue A j ≠ orderedEigenvalue A 0 := by
  intro j hj
  have hj' : (1 : Fin 3) ≤ j := by fin_cases j <;> simp_all
  exact ((orderedEigenvalue_antitone A hj').trans_lt h).ne

private theorem min_gap_orderedEigenvalue_ne {A : S0}
    (h : orderedEigenvalue A 2 < orderedEigenvalue A 1) :
    ∀ j ≠ 2, orderedEigenvalue A j ≠ orderedEigenvalue A 2 := by
  intro j hj
  have hj' : j ≤ (1 : Fin 3) := by fin_cases j <;> simp_all
  exact (h.trans_le (orderedEigenvalue_antitone A hj')).ne'

theorem contDiffAt_orderedEigenvalue_of_mem_simpleSpectrum {A : S0}
    (hA : A ∈ simpleSpectrumLocus) (i : Fin 3) :
    ContDiffAt ℝ ∞ (fun B : S0 => orderedEigenvalue B i) A := by
  fin_cases i
  · exact contDiffAt_orderedEigenvalue_of_ne (max_gap_orderedEigenvalue_ne hA.1)
  · apply contDiffAt_orderedEigenvalue_of_ne
    intro j hj
    fin_cases j
    · exact hA.1.ne'
    · exact (hj rfl).elim
    · exact hA.2.ne
  · exact contDiffAt_orderedEigenvalue_of_ne (min_gap_orderedEigenvalue_ne hA.2)

theorem contDiffOn_orderedEigenvalue (i : Fin 3) :
    ContDiffOn ℝ ∞ (fun A : S0 => orderedEigenvalue A i) simpleSpectrumLocus :=
  fun _ hA => (contDiffAt_orderedEigenvalue_of_mem_simpleSpectrum hA i).contDiffWithinAt

theorem contDiffOn_orderedSpectrum : ContDiffOn ℝ ∞ orderedEigenvalue simpleSpectrumLocus :=
  contDiffOn_pi.2 contDiffOn_orderedEigenvalue

/-- The orthogonal projector onto the selected eigenline of the ordered frame. -/
def orderedEigenlineProjector (A : S0) (i : Fin 3) : Tensor :=
  Matrix.vecMulVec (fun j => orderedEigenbasis A i j) (fun j => orderedEigenbasis A i j)

theorem spectralVacuumPoint_coe_eq_projectors (a : BulkCoefficients) (A : S0) :
    ((spectralVacuumPoint a A).val : Tensor) =
      vacuumRadius a • (orderedEigenlineProjector A 0 - orderedEigenlineProjector A 2) := by
  rw [spectralVacuumPoint_coe]
  rfl

theorem spectralVacuumPoint_coe_eq_scaled_projectors (a : BulkCoefficients) (A : S0) :
    ((spectralVacuumPoint a A).val : Tensor) =
      vacuumRadius a • orderedEigenlineProjector A 0 - vacuumRadius a • orderedEigenlineProjector A 2 := by
  rw [spectralVacuumPoint_coe_eq_projectors, smul_sub]

/-- The rank-one tensors obtained by scaling a unit-direction projector by the vacuum radius. -/
def scaledRankOneProjectors (a : BulkCoefficients) : Set Tensor :=
  {P | ∃ n : Point, ‖n‖ = 1 ∧
    P = vacuumRadius a • Matrix.vecMulVec (fun i => n i) (fun i => n i)}

theorem scaled_orderedEigenlineProjector_mem (a : BulkCoefficients) (A : S0) (i : Fin 3) :
    vacuumRadius a • orderedEigenlineProjector A i ∈ scaledRankOneProjectors a :=
  ⟨orderedEigenbasis A i, (orderedEigenbasis A).orthonormal.norm_eq_one i, rfl⟩

private theorem orderedEigenlineProjector_mulVec (A : S0) (i j : Fin 3) :
    orderedEigenlineProjector A i *ᵥ (orderedEigenbasis A j).ofLp =
      if j = i then (orderedEigenbasis A j).ofLp else 0 := by
  let b := orderedEigenbasis A
  change Matrix.vecMulVec (b i).ofLp (b i).ofLp *ᵥ (b j).ofLp = _
  rw [Matrix.vecMulVec_mulVec, op_smul_eq_smul]
  by_cases hij : j = i
  · subst j
    have h := real_inner_self_eq_norm_sq (b i)
    rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, b.orthonormal.norm_eq_one, one_pow] at h
    rw [h, one_smul, if_pos rfl]
  · have h := b.inner_eq_zero hij
    rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial] at h
    rw [h, zero_smul, if_neg hij]

private def spectralProjectorPolynomial (A : S0) (μ : ℝ) : Tensor :=
  (traceCubicSlope (vacuumInvariants A, μ))⁻¹ •
    ((A : Tensor) ^ 2 + μ • (A : Tensor) + (μ ^ 2 - (vacuumInvariants A).1 / 2) • (1 : Tensor))

private theorem spectralProjectorPolynomial_mulVec (A : S0) (μ : ℝ) (j : Fin 3) :
    spectralProjectorPolynomial A μ *ᵥ (orderedEigenbasis A j).ofLp =
      ((traceCubicSlope (vacuumInvariants A, μ))⁻¹ *
        ((orderedEigenvalue A j) ^ 2 + μ * orderedEigenvalue A j +
          (μ ^ 2 - (vacuumInvariants A).1 / 2))) • (orderedEigenbasis A j).ofLp := by
  simp only [spectralProjectorPolynomial, Matrix.smul_mulVec, Matrix.add_mulVec, pow_two,
    ← Matrix.mulVec_mulVec, Matrix.mulVec_smul, orderedEigenbasis_mulVec, Matrix.one_mulVec,
    smul_smul, ← add_smul]

private theorem orderedEigenlineProjector_eq_polynomial {A : S0} {i : Fin 3}
    (hi : ∀ j ≠ i, orderedEigenvalue A j ≠ orderedEigenvalue A i) :
    orderedEigenlineProjector A i = spectralProjectorPolynomial A (orderedEigenvalue A i) := by
  let μ := orderedEigenvalue A i
  let u := (vacuumInvariants A, μ)
  have hSlope : traceCubicSlope u ≠ 0 := traceCubicSlope_ne_zero hi
  have hCoeff (j : Fin 3) : (traceCubicSlope u)⁻¹ *
      ((orderedEigenvalue A j) ^ 2 + μ * orderedEigenvalue A j +
        (μ ^ 2 - (vacuumInvariants A).1 / 2)) = (if j = i then 1 else 0) := by
    by_cases hij : j = i
    · rw [hij, if_pos rfl]
      have hTerm : (orderedEigenvalue A i) ^ 2 + μ * orderedEigenvalue A i +
          (μ ^ 2 - (vacuumInvariants A).1 / 2) = traceCubicSlope u := by
        dsimp only [traceCubicSlope, u, μ]
        ring
      rw [hTerm, inv_mul_cancel₀ hSlope]
    · rw [if_neg hij]
      have hz : (orderedEigenvalue A j - μ) * ((orderedEigenvalue A j) ^ 2 +
          μ * orderedEigenvalue A j + (μ ^ 2 - (vacuumInvariants A).1 / 2)) = 0 := by
        change (orderedEigenvalue A j - orderedEigenvalue A i) *
            ((orderedEigenvalue A j) ^ 2 + orderedEigenvalue A i * orderedEigenvalue A j +
              ((orderedEigenvalue A i) ^ 2 - ((A : Tensor) ^ 2).trace / 2)) = 0
        linear_combination orderedEigenvalue_cubic_equation A j - orderedEigenvalue_cubic_equation A i
      rw [(mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr (hi j hij)), mul_zero]
  apply Matrix.toEuclideanLin.injective
  apply (orderedEigenbasis A).toBasis.ext
  intro j
  apply PiLp.ext
  intro k
  change (orderedEigenlineProjector A i *ᵥ (orderedEigenbasis A j).ofLp) k =
    (spectralProjectorPolynomial A μ *ᵥ (orderedEigenbasis A j).ofLp) k
  rw [orderedEigenlineProjector_mulVec, spectralProjectorPolynomial_mulVec, hCoeff]
  by_cases hij : j = i <;> simp [hij]

/-- A simple eigenline projector is a quadratic polynomial of the tensor, divided by the cubic slope. -/
theorem orderedEigenlineProjector_eq_trace_formula {A : S0} {i : Fin 3}
    (hi : ∀ j ≠ i, orderedEigenvalue A j ≠ orderedEigenvalue A i) :
    let μ := orderedEigenvalue A i
    let s := ((A : Tensor) ^ 2).trace / 2
    orderedEigenlineProjector A i =
      (3 * μ ^ 2 - s)⁻¹ • ((A : Tensor) ^ 2 + μ • (A : Tensor) + (μ ^ 2 - s) • (1 : Tensor)) :=
  orderedEigenlineProjector_eq_polynomial hi

private theorem contDiffAt_spectralProjectorPolynomial {A : S0} {i : Fin 3}
    (hi : ∀ j ≠ i, orderedEigenvalue A j ≠ orderedEigenvalue A i) :
    ContDiffAt ℝ ∞ (fun B : S0 => spectralProjectorPolynomial B (orderedEigenvalue B i)) A := by
  have hμ := contDiffAt_orderedEigenvalue_of_ne hi
  have hTrace := (contDiff_vacuumInvariants.fst.contDiffAt (x := A)).div_const 2
  have hMatrix : ContDiffAt ℝ ∞ (fun B : S0 => (B : Tensor)) A :=
    symmetricTraceless.subtypeL.contDiff.contDiffAt
  have hThree : ContDiffAt ℝ ∞ (fun _ : S0 => (3 : ℝ)) A := contDiffAt_const
  have hOne : ContDiffAt ℝ ∞ (fun _ : S0 => (1 : Tensor)) A := contDiffAt_const
  have hSlope := (hThree.mul (hμ.pow 2)).sub hTrace
  have hSlopeInv := hSlope.inv (traceCubicSlope_ne_zero hi)
  have hPoly := ((hMatrix.pow 2).add (hμ.smul hMatrix)).add
    (((hμ.pow 2).sub hTrace).smul hOne)
  exact hSlopeInv.smul hPoly

theorem contDiffOn_orderedEigenlineProjector (i : Fin 3) :
    ContDiffOn ℝ ∞ (fun A : S0 => orderedEigenlineProjector A i)
      {A | ∀ j ≠ i, orderedEigenvalue A j ≠ orderedEigenvalue A i} := by
  intro A hA
  exact (contDiffAt_spectralProjectorPolynomial hA).contDiffWithinAt.congr_of_mem
    (fun _ hB => orderedEigenlineProjector_eq_polynomial hB) hA

theorem contDiffOn_scaled_orderedEigenlineProjector_max (a : BulkCoefficients) :
    ContDiffOn ℝ ∞ (fun A : S0 => vacuumRadius a • orderedEigenlineProjector A 0)
      {A | orderedEigenvalue A 1 < orderedEigenvalue A 0} :=
  (contDiff_const : ContDiff ℝ ∞ (fun _ : S0 => vacuumRadius a)).contDiffOn.smul
    ((contDiffOn_orderedEigenlineProjector 0).mono
    (fun _ hA => max_gap_orderedEigenvalue_ne hA))

theorem contDiffOn_scaled_orderedEigenlineProjector_min (a : BulkCoefficients) :
    ContDiffOn ℝ ∞ (fun A : S0 => vacuumRadius a • orderedEigenlineProjector A 2)
      {A | orderedEigenvalue A 2 < orderedEigenvalue A 1} :=
  (contDiff_const : ContDiff ℝ ∞ (fun _ : S0 => vacuumRadius a)).contDiffOn.smul
    ((contDiffOn_orderedEigenlineProjector 2).mono
    (fun _ hA => min_gap_orderedEigenvalue_ne hA))

theorem contDiffOn_spectralVacuumPoint (a : BulkCoefficients) :
    ContDiffOn ℝ ∞ (fun A : S0 => (spectralVacuumPoint a A).val) simpleSpectrumLocus := by
  have hMax := (contDiffOn_scaled_orderedEigenlineProjector_max a).mono
    (show simpleSpectrumLocus ⊆ _ from fun _ hA => hA.1)
  have hMin := (contDiffOn_scaled_orderedEigenlineProjector_min a).mono
    (show simpleSpectrumLocus ⊆ _ from fun _ hA => hA.2)
  refine (traceFreeSymmetricPartCLM.contDiff.comp_contDiffOn (hMax.sub hMin)).congr ?_
  intro A _
  change (spectralVacuumPoint a A).val = traceFreeSymmetricPartCLM
    (vacuumRadius a • orderedEigenlineProjector A 0 - vacuumRadius a • orderedEigenlineProjector A 2)
  rw [← smul_sub, ← spectralVacuumPoint_coe_eq_projectors, traceFreeSymmetricPartCLM_apply,
    traceFreeSymmetricPart_of_S0]

/-- The bulk estimates on a simple-spectrum vacuum tube, written with the spectral projection. -/
theorem bulkPotential_spectralVacuumPoint_tubular_estimates (a : BulkCoefficients) :
    ∃ (c C δ : ℝ), 0 < c ∧ 0 < C ∧ 0 < δ ∧ vacuumTube a δ ⊆ simpleSpectrumLocus ∧
      ∀ A ∈ vacuumTube a δ,
        c * Metric.infDist A (vacuum a) ^ 2 ≤ bulkPotential a A ∧
        ∀ t ∈ Icc (0 : ℝ) 1, bulkPotential a
          (t • A + (1 - t) • (spectralVacuumPoint a A).val) ≤ C * t ^ 2 * bulkPotential a A := by
  obtain ⟨c, C, d, hc, hC, hd, hp, hEst⟩ := bulkPotential_tubular_estimates a
  let δ := min d (vacuumRadius a / 2)
  refine ⟨c, C, δ, hc, hC, lt_min hd (half_pos (vacuumRadius_pos a)), ?_, ?_⟩
  · intro A hA
    apply vacuumTube_vacuumRadius_half_subset_simpleSpectrum a
    change Metric.infDist A (vacuum a) < δ at hA
    exact hA.trans_le (min_le_right _ _)
  · intro A hA
    change Metric.infDist A (vacuum a) < δ at hA
    have hAd : Metric.infDist A (vacuum a) < d := hA.trans_le (min_le_left _ _)
    let p := vacuumTubularProjection a
    let B : vacuumTube a p.radius := ⟨A, hAd.trans_le hp⟩
    have h := hEst B hAd
    have hProjection := spectralVacuumPoint_eq_tubeProjection p B
    change spectralVacuumPoint a A = (vacuumTubularProjection a).project B at hProjection
    rw [← hProjection] at h
    exact h

end Thesis

end

end
