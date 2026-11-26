module

public import Thesis.Foundation.VacuumQuaternionDeck

/-! The pullback of the Frobenius metric along the biaxial quaternion cover. -/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped ContDiff Matrix Matrix.Norms.Frobenius NNReal Quaternion Topology

namespace Thesis

private def frameDyad (u v : Point) : Tensor :=
  Matrix.vecMulVec (fun i => u i) (fun i => v i)

private def frameDyadCLM : Point →L[ℝ] Point →L[ℝ] Tensor :=
  (LinearMap.mk₂ ℝ frameDyad
    (fun u v z => by ext i j; simp [frameDyad, Matrix.vecMulVec_apply, add_mul])
    (fun c u v => by ext i j; simp [frameDyad, Matrix.vecMulVec_apply, mul_assoc])
    (fun u v z => by ext i j; simp [frameDyad, Matrix.vecMulVec_apply, mul_add])
    (fun c u v => by
      ext i j
      simp [frameDyad, Matrix.vecMulVec_apply, mul_left_comm])).toContinuousBilinearMap

private theorem hasDerivAt_frameDyad {u v : ℝ → Point} {du dv : Point} {t : ℝ}
    (hu : HasDerivAt u du t) (hv : HasDerivAt v dv t) :
    HasDerivAt (fun s => frameDyad (u s) (v s))
      (frameDyad du (v t) + frameDyad (u t) dv) t := by
  have hd := (frameDyadCLM.hasFDerivAt_of_bilinear hu.hasFDerivAt hv.hasFDerivAt).hasDerivAt
  change HasDerivAt (fun s => frameDyad (u s) (v s))
    (frameDyad (u t) ((1 : ℝ) • dv) + frameDyad ((1 : ℝ) • du) (v t)) t at hd
  simpa only [one_smul, add_comm] using hd

private theorem frobenius_frameDyad (u v w z : Point) :
    frobenius (frameDyad u v) (frameDyad w z) = inner ℝ u w * inner ℝ v z := by
  simp only [frobenius, frameDyad, Matrix.transpose_vecMulVec, Matrix.vecMulVec_mul_vecMulVec,
    Matrix.trace_vecMulVec, EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  rw [dotProduct_comm (fun i => u i), dotProduct_comm (fun i => v i)]
  exact smul_dotProduct (w.ofLp ⬝ᵥ u.ofLp) z.ofLp v.ofLp

theorem frobenius_directorProjector (u v : Point) :
    frobenius (directorProjector u) (directorProjector v) = (inner ℝ u v) ^ 2 := by
  change frobenius (frameDyad u u) (frameDyad v v) = (inner ℝ u v) ^ 2
  simpa only [pow_two] using frobenius_frameDyad u u v v

private theorem frobenius_sub_left_frame (A B C : Tensor) :
    frobenius (A - B) C = frobenius A C - frobenius B C := by
  simp [frobenius, Matrix.transpose_sub, Matrix.sub_mul, Matrix.trace_sub]

private theorem frobenius_sub_right_frame (A B C : Tensor) :
    frobenius A (B - C) = frobenius A B - frobenius A C := by
  simp [frobenius, Matrix.mul_sub, Matrix.trace_sub]

private theorem frobenius_smul_left_frame (r : ℝ) (A B : Tensor) :
    frobenius (r • A) B = r * frobenius A B := by
  simp only [frobenius, Matrix.transpose_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]

private theorem frobenius_smul_right_frame (r : ℝ) (A B : Tensor) :
    frobenius A (r • B) = r * frobenius A B := by
  simp only [frobenius, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]

private theorem biaxial_tangent_norm_sq (a : BulkCoefficients) (n m dn dm : Point)
    (hn : ‖n‖ = 1) (hm : ‖m‖ = 1) (hnm : inner ℝ n m = 0)
    (hdn : inner ℝ n dn = 0) (hdm : inner ℝ m dm = 0)
    (hrel : inner ℝ n dm = -inner ℝ dn m) :
    (1 / 2 : ℝ) * ‖vacuumRadius a •
      (frameDyad dn n + frameDyad n dn - (frameDyad dm m + frameDyad m dm))‖ ^ 2 =
      vacuumRadius a ^ 2 * (‖dn‖ ^ 2 + ‖dm‖ ^ 2 + 2 * (inner ℝ dn m) ^ 2) := by
  have hmn : inner ℝ m n = 0 := by rw [real_inner_comm, hnm]
  have hdn' : inner ℝ dn n = 0 := by rw [real_inner_comm, hdn]
  have hdm' : inner ℝ dm m = 0 := by rw [real_inner_comm, hdm]
  have hrel' : inner ℝ dm n = -inner ℝ dn m := by rw [real_inner_comm n dm, hrel]
  simp only [norm_sq_eq_frobenius, frobenius_smul_left_frame, frobenius_smul_right_frame,
    frobenius_sub_left_frame, frobenius_sub_right_frame, frobenius_add_left, frobenius_add_right,
    frobenius_frameDyad, real_inner_self_eq_norm_sq, hnm, hmn, hdn, hdn', hdm, hdm',
    hrel, hrel', real_inner_comm dn m, hn, hm]
  ring

/-- The director form of the Frobenius metric for a differentiable biaxial tensor curve. -/
theorem biaxialTensor_curve_metric (a : BulkCoefficients) {n m : ℝ → Point} {dn dm : Point}
    {t : ℝ} (hnd : HasDerivAt n dn t) (hmd : HasDerivAt m dm t)
    (hn : ‖n t‖ = 1) (hm : ‖m t‖ = 1) (hnm : inner ℝ (n t) (m t) = 0)
    (hdn : inner ℝ (n t) dn = 0) (hdm : inner ℝ (m t) dm = 0)
    (hrel : inner ℝ (n t) dm = -inner ℝ dn (m t)) :
    (1 / 2 : ℝ) * ‖deriv (fun s => biaxialTensor a (n s) (m s)) t‖ ^ 2 =
      vacuumRadius a ^ 2 * (‖dn‖ ^ 2 + ‖dm‖ ^ 2 + 2 * (inner ℝ dn (m t)) ^ 2) := by
  have hd := ((hasDerivAt_frameDyad hnd hnd).sub (hasDerivAt_frameDyad hmd hmd)).const_smul
    (vacuumRadius a)
  change HasDerivAt (fun s => biaxialTensor a (n s) (m s)) _ t at hd
  calc
    _ = _ := congrArg (fun D : Tensor => (1 / 2 : ℝ) * ‖D‖ ^ 2) hd.deriv
    _ = _ := biaxial_tangent_norm_sq a _ _ _ _ hn hm hnm hdn hdm hrel

/-- The third quaternion unit, the product of the first two units. -/
def thirdQuaternionUnit : ℍ := ⟨0, 0, 0, 1⟩

private def quaternionImaginaryCLM : ℍ →L[ℝ] Point :=
  (show ℍ →ₗ[ℝ] Point from {
    toFun := quaternionImaginaryVector
    map_add' := fun q r => by
      apply PiLp.ext
      intro i
      fin_cases i <;> rfl
    map_smul' := fun c q => by
      apply PiLp.ext
      intro i
      fin_cases i <;> rfl }).toContinuousLinearMap

/-- The director obtained by rotating an imaginary quaternion by a unit quaternion. -/
def quaternionDirector (q x : ℍ) : Point :=
  quaternionImaginaryVector (quaternionConjugate q x)

private theorem quaternionDirector_add_smul (q x y : ℍ) (a b : ℝ) :
    quaternionDirector q (a • x + b • y) =
      a • quaternionDirector q x + b • quaternionDirector q y := by
  change quaternionImaginaryCLM (q * (a • x + b • y) * star q) = _
  rw [mul_add, add_mul, mul_smul_comm, mul_smul_comm, smul_mul_assoc, smul_mul_assoc, map_add,
    map_smul, map_smul]
  rfl

private theorem norm_quaternionDirector {q x : ℍ} (hq : ‖q‖ = 1) (hx : x.re = 0) :
    ‖quaternionDirector q x‖ = ‖x‖ := by
  rw [quaternionDirector, ← norm_pureQuaternion,
    pureQuaternion_quaternionImaginaryVector (quaternionConjugate_re_eq_zero q hx)]
  simp only [quaternionConjugate, norm_mul, Quaternion.norm_star, hq, one_mul, mul_one]

private theorem inner_quaternionDirector {q x y : ℍ} (hq : ‖q‖ = 1)
    (hx : x.re = 0) (hy : y.re = 0) (hxy : (x * y).re = 0) :
    inner ℝ (quaternionDirector q x) (quaternionDirector q y) = 0 := by
  rw [quaternionDirector, quaternionDirector, inner_eq_neg_re_pureQuaternion_mul,
    pureQuaternion_quaternionImaginaryVector (quaternionConjugate_re_eq_zero q hx),
    pureQuaternion_quaternionImaginaryVector (quaternionConjugate_re_eq_zero q hy),
    ← quaternionConjugate_mul q hq, quaternionConjugate_re_eq_zero q hxy, neg_zero]

private def quaternionStarCLM : ℍ →L[ℝ] ℍ :=
  (show ℍ →ₗ[ℝ] ℍ from {
    toFun := star
    map_add' := star_add
    map_smul' := Quaternion.star_smul }).toContinuousLinearMap

private theorem hasDerivAt_quaternionStar {q : ℝ → ℍ} {dq : ℍ} {t : ℝ}
    (hd : HasDerivAt q dq t) : HasDerivAt (fun s => star (q s)) (star dq) t := by
  have houter : HasFDerivAt (⇑quaternionStarCLM) quaternionStarCLM (q t) :=
    quaternionStarCLM.hasFDerivAt
  exact houter.comp_hasDerivAt (f := q) (f' := dq) t hd

private theorem quaternionVelocity_re_eq_zero {q : ℝ → ℍ} {dq : ℍ} {t : ℝ}
    (hd : HasDerivAt q dq t) (hunit : ∀ᶠ s in 𝓝 t, ‖q s‖ = 1) :
    (star (q t) * dq).re = 0 := by
  let u := star (q t) * dq
  have hconstant : HasDerivAt (fun s => star (q s) * q s) 0 t :=
    (hasDerivAt_const t (1 : ℍ)).congr_of_eventuallyEq
      (hunit.mono fun _ hs => quaternionUnit_star_mul hs)
  have hzero := ((hasDerivAt_quaternionStar hd).fun_mul hd).unique hconstant
  have hu : star u + u = 0 := by simpa only [u, star_mul, star_star] using hzero
  have hre := congrArg (fun z : ℍ => z.re) hu
  simp only [Quaternion.re_add, Quaternion.re_star, Quaternion.re_zero] at hre
  linarith

theorem hasDerivAt_quaternionConjugate {q : ℝ → ℍ} {dq : ℍ} {t : ℝ}
    (hd : HasDerivAt q dq t) (hunit : ∀ᶠ s in 𝓝 t, ‖q s‖ = 1) (x : ℍ) :
    let u := star (q t) * dq
    HasDerivAt (fun s => quaternionConjugate (q s) x)
      (quaternionConjugate (q t) (u * x - x * u)) t := by
  dsimp
  let u := star (q t) * dq
  have hq : ‖q t‖ = 1 := hunit.self_of_nhds
  have hvelocity : dq = q t * u := by
    change dq = q t * (star (q t) * dq)
    rw [← mul_assoc, quaternionUnit_mul_star hq, one_mul]
  have hstar : star u = -u := Quaternion.star_eq_neg.mpr (quaternionVelocity_re_eq_zero hd hunit)
  have hproduct := (hd.mul_const x).fun_mul (hasDerivAt_quaternionStar hd)
  change HasDerivAt (fun s => q s * x * star (q s)) _ t at hproduct
  have heq : dq * x * star (q t) + q t * x * star dq =
      quaternionConjugate (q t) (u * x - x * u) := by
    conv_lhs => rw [hvelocity, star_mul, hstar]
    simp only [quaternionConjugate, sub_eq_add_neg, add_mul, mul_add, mul_assoc, neg_mul, mul_neg]
  rwa [heq] at hproduct

private theorem hasDerivAt_quaternionDirector {q : ℝ → ℍ} {dq : ℍ} {t : ℝ}
    (hd : HasDerivAt q dq t) (hunit : ∀ᶠ s in 𝓝 t, ‖q s‖ = 1) (x : ℍ) :
    let u := star (q t) * dq
    HasDerivAt (fun s => quaternionDirector (q s) x)
      (quaternionDirector (q t) (u * x - x * u)) t := by
  let u := star (q t) * dq
  have houter : HasFDerivAt (⇑quaternionImaginaryCLM) quaternionImaginaryCLM
      (quaternionConjugate (q t) x) := quaternionImaginaryCLM.hasFDerivAt
  exact houter.comp_hasDerivAt (f := fun s => quaternionConjugate (q s) x)
    (f' := quaternionConjugate (q t) (u * x - x * u)) t (hasDerivAt_quaternionConjugate hd hunit x)

theorem commutator_firstQuaternionUnit (u : ℍ) :
    u * firstQuaternionUnit - firstQuaternionUnit * u =
      (2 * u.imK) • secondQuaternionUnit + (-2 * u.imJ) • thirdQuaternionUnit := by
  ext <;> simp [firstQuaternionUnit, secondQuaternionUnit, thirdQuaternionUnit] <;> ring

theorem commutator_secondQuaternionUnit (u : ℍ) :
    u * secondQuaternionUnit - secondQuaternionUnit * u =
      (-2 * u.imK) • firstQuaternionUnit + (2 * u.imI) • thirdQuaternionUnit := by
  ext <;> simp [firstQuaternionUnit, secondQuaternionUnit, thirdQuaternionUnit] <;> ring

private theorem commutator_thirdQuaternionUnit (u : ℍ) :
    u * thirdQuaternionUnit - thirdQuaternionUnit * u =
      (2 * u.imJ) • firstQuaternionUnit + (-2 * u.imI) • secondQuaternionUnit := by
  ext <;> simp [firstQuaternionUnit, secondQuaternionUnit, thirdQuaternionUnit] <;> ring

private theorem norm_thirdQuaternionUnit : ‖thirdQuaternionUnit‖ = 1 := by
  conv_lhs =>
    rw [show thirdQuaternionUnit = firstQuaternionUnit * secondQuaternionUnit from by
      ext <;> norm_num [thirdQuaternionUnit, firstQuaternionUnit, secondQuaternionUnit]]
  rw [norm_mul, norm_firstQuaternionUnit, norm_secondQuaternionUnit, one_mul]

private theorem quaternionImaginaryVector_mul_pureQuaternion (n m : Point) :
    quaternionImaginaryVector (pureQuaternion n * pureQuaternion m) =
      WithLp.toLp 2 (n.ofLp ⨯₃ m.ofLp) := by
  apply PiLp.ext
  intro i
  fin_cases i <;> simp [quaternionImaginaryVector, pureQuaternion, cross_apply]
  ring

/-- The third lifted director is the oriented cross product of the first two. -/
theorem quaternionDirector_third_cross {q : ℍ} (hq : ‖q‖ = 1) :
    quaternionDirector q thirdQuaternionUnit = WithLp.toLp 2
      ((quaternionDirector q firstQuaternionUnit).ofLp ⨯₃
        (quaternionDirector q secondQuaternionUnit).ofLp) := by
  rw [← quaternionImaginaryVector_mul_pureQuaternion]
  rw [show pureQuaternion (quaternionDirector q firstQuaternionUnit) =
    quaternionConjugate q firstQuaternionUnit from pureQuaternion_quaternionImaginaryVector
      (quaternionConjugate_re_eq_zero q rfl)]
  rw [show pureQuaternion (quaternionDirector q secondQuaternionUnit) =
    quaternionConjugate q secondQuaternionUnit from pureQuaternion_quaternionImaginaryVector
      (quaternionConjugate_re_eq_zero q rfl), ← quaternionConjugate_mul q hq]
  congr 2
  ext <;> norm_num [firstQuaternionUnit, secondQuaternionUnit, thirdQuaternionUnit]

private theorem norm_sq_smul_add_of_inner_eq_zero {u v : Point} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (huv : inner ℝ u v = 0) (s t : ℝ) : ‖s • u + t • v‖ ^ 2 = s ^ 2 + t ^ 2 := by
  rw [norm_add_sq_real, real_inner_smul_left, real_inner_smul_right, huv]
  simp [norm_smul, hu, hv, Real.norm_eq_abs, sq_abs]

/-- The exact anisotropic Frobenius metric for a unit quaternion lift. -/
theorem quaternionFrame_curve_metric (a : BulkCoefficients) {q : ℝ → ℍ} {dq : ℍ} {t : ℝ}
    (hd : HasDerivAt q dq t) (hunit : ∀ᶠ s in 𝓝 t, ‖q s‖ = 1) :
    let u := star (q t) * dq
    (1 / 2 : ℝ) * ‖deriv (fun s => biaxialTensor a
      (quaternionDirector (q s) firstQuaternionUnit)
      (quaternionDirector (q s) secondQuaternionUnit)) t‖ ^ 2 =
      4 * vacuumRadius a ^ 2 * (u.imI ^ 2 + u.imJ ^ 2 + 4 * u.imK ^ 2) := by
  let u := star (q t) * dq
  let n := quaternionDirector (q t) firstQuaternionUnit
  let m := quaternionDirector (q t) secondQuaternionUnit
  let p := quaternionDirector (q t) thirdQuaternionUnit
  have hq : ‖q t‖ = 1 := hunit.self_of_nhds
  have hn : ‖n‖ = 1 := (norm_quaternionDirector hq rfl).trans norm_firstQuaternionUnit
  have hm : ‖m‖ = 1 := (norm_quaternionDirector hq rfl).trans norm_secondQuaternionUnit
  have hp : ‖p‖ = 1 := (norm_quaternionDirector hq rfl).trans norm_thirdQuaternionUnit
  have hnm : inner ℝ n m = 0 := inner_quaternionDirector hq rfl rfl (by
    norm_num [firstQuaternionUnit, secondQuaternionUnit])
  have hnp : inner ℝ n p = 0 := inner_quaternionDirector hq rfl rfl (by
    norm_num [firstQuaternionUnit, thirdQuaternionUnit])
  have hmp : inner ℝ m p = 0 := inner_quaternionDirector hq rfl rfl (by
    norm_num [secondQuaternionUnit, thirdQuaternionUnit])
  have hpm : inner ℝ p m = 0 := (real_inner_comm m p).trans hmp
  have hmn : inner ℝ m n = 0 := (real_inner_comm n m).trans hnm
  have hd₁ : HasDerivAt (fun s => quaternionDirector (q s) firstQuaternionUnit)
      ((2 * u.imK) • m + (-2 * u.imJ) • p) t := by
    simpa only [u, m, p, commutator_firstQuaternionUnit, quaternionDirector_add_smul] using
      hasDerivAt_quaternionDirector hd hunit firstQuaternionUnit
  have hd₂ : HasDerivAt (fun s => quaternionDirector (q s) secondQuaternionUnit)
      ((-2 * u.imK) • n + (2 * u.imI) • p) t := by
    simpa only [u, n, p, commutator_secondQuaternionUnit, quaternionDirector_add_smul] using
      hasDerivAt_quaternionDirector hd hunit secondQuaternionUnit
  have h := biaxialTensor_curve_metric a hd₁ hd₂ hn hm hnm
    (by
      change inner ℝ n ((2 * u.imK) • m + (-2 * u.imJ) • p) = 0
      simp [inner_add_right, real_inner_smul_right, hnm, hnp])
    (by
      change inner ℝ m ((-2 * u.imK) • n + (2 * u.imI) • p) = 0
      simp [inner_add_right, real_inner_smul_right, hmn, hmp])
    (by
      change inner ℝ n ((-2 * u.imK) • n + (2 * u.imI) • p) =
        -inner ℝ ((2 * u.imK) • m + (-2 * u.imJ) • p) m
      simp [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
        hn, hm, hnp, hpm, neg_mul])
  change _ = 4 * vacuumRadius a ^ 2 * (u.imI ^ 2 + u.imJ ^ 2 + 4 * u.imK ^ 2)
  calc
    _ = vacuumRadius a ^ 2 * (‖(2 * u.imK) • m + (-2 * u.imJ) • p‖ ^ 2 +
        ‖(-2 * u.imK) • n + (2 * u.imI) • p‖ ^ 2 +
        2 * (inner ℝ ((2 * u.imK) • m + (-2 * u.imJ) • p) m) ^ 2) := h
    _ = _ := by
      rw [norm_sq_smul_add_of_inner_eq_zero hm hp hmp, norm_sq_smul_add_of_inner_eq_zero hn hp hnp]
      simp only [inner_add_left, real_inner_smul_left, hpm, mul_zero, add_zero,
        real_inner_self_eq_norm_sq, hm, one_pow, mul_one]
      ring

private theorem quaternionDirector_firstFrame (v : QuaternionCoordinates) :
    quaternionDirector (Quaternion.linearIsometryEquivTuple.symm v) firstQuaternionUnit =
      firstFrameVector v := by
  rw [quaternionDirector, ← firstFrameVector_pureQuaternion, quaternionImaginaryVector_pureQuaternion]

private theorem quaternionDirector_secondFrame (v : QuaternionCoordinates) :
    quaternionDirector (Quaternion.linearIsometryEquivTuple.symm v) secondQuaternionUnit =
      secondFrameVector v := by
  rw [quaternionDirector, ← secondFrameVector_pureQuaternion, quaternionImaginaryVector_pureQuaternion]

/-- Smoothness of the tensor-valued cover along a smooth unit quaternion curve. -/
theorem contDiff_cover_curve (a : BulkCoefficients) (v : ℝ → Sphere3) {n : ℕ∞ω}
    (hv : ContDiff ℝ n (fun t => Quaternion.linearIsometryEquivTuple.symm (v t).val)) :
    ContDiff ℝ n (fun t => (cover a (v t) : Tensor)) := by
  let q (t : ℝ) := Quaternion.linearIsometryEquivTuple.symm (v t).val
  have hstar : ContDiff ℝ n (fun t => star (q t)) := quaternionStarCLM.contDiff.comp hv
  have hdir (b : ℍ) : ContDiff ℝ n (fun t => quaternionDirector (q t) b) :=
    quaternionImaginaryCLM.contDiff.comp ((hv.mul contDiff_const).mul hstar)
  have hDyad : ContDiff ℝ n (fun p : Point × Point => frameDyad p.1 p.2) :=
    frameDyadCLM.isBoundedBilinearMap.contDiff
  let f (t : ℝ) := quaternionDirector (q t) firstQuaternionUnit
  let g (t : ℝ) := quaternionDirector (q t) secondQuaternionUnit
  have hf : ContDiff ℝ n (fun t => frameDyad (f t) (f t)) := hDyad.comp ((hdir _).prodMk (hdir _))
  have hg : ContDiff ℝ n (fun t => frameDyad (g t) (g t)) := hDyad.comp ((hdir _).prodMk (hdir _))
  have hEq : (fun t => (cover a (v t) : Tensor)) = fun t => biaxialTensor a (f t) (g t) := by
    funext t
    rw [cover_eq_quaternionFrameProjection, vacuumFrameProjection_tensor]
    change biaxialTensor a (firstFrameVector (v t).val) (secondFrameVector (v t).val) = _
    unfold f g q
    rw [quaternionDirector_firstFrame, quaternionDirector_secondFrame]
  rw [hEq]
  exact (hf.sub hg).const_smul (vacuumRadius a)

/-- The metric identity for the actual frozen quaternion cover. -/
theorem cover_curve_metric (a : BulkCoefficients) (v : ℝ → Sphere3) {dq : ℍ} {t : ℝ}
    (hd : HasDerivAt (fun s => Quaternion.linearIsometryEquivTuple.symm
      (v s : QuaternionCoordinates)) dq t) :
    let u := star (Quaternion.linearIsometryEquivTuple.symm (v t : QuaternionCoordinates)) * dq
    (1 / 2 : ℝ) * ‖deriv (fun s => (cover a (v s) : Tensor)) t‖ ^ 2 =
      4 * vacuumRadius a ^ 2 * (u.imI ^ 2 + u.imJ ^ 2 + 4 * u.imK ^ 2) := by
  have h := quaternionFrame_curve_metric a hd
    (Eventually.of_forall fun s => quaternionTuple_symm_norm_eq_one (v s))
  have heq : (fun s => (cover a (v s) : Tensor)) = fun s =>
      biaxialTensor a (firstFrameVector (v s : QuaternionCoordinates))
        (secondFrameVector (v s : QuaternionCoordinates)) := by
    funext s
    rw [cover_eq_quaternionFrameProjection, vacuumFrameProjection_tensor]
    rfl
  rw [heq]
  simpa only [quaternionDirector_firstFrame, quaternionDirector_secondFrame] using h

/-- The Frobenius norm of the full lifted frame derivative. -/
theorem quaternion_directors_curve_metric {q : ℝ → ℍ} {dq : ℍ} {t : ℝ}
    (hd : HasDerivAt q dq t) (hunit : ∀ᶠ s in 𝓝 t, ‖q s‖ = 1) :
    ‖deriv (fun s => quaternionDirector (q s) firstQuaternionUnit) t‖ ^ 2 +
      ‖deriv (fun s => quaternionDirector (q s) secondQuaternionUnit) t‖ ^ 2 +
      ‖deriv (fun s => quaternionDirector (q s) thirdQuaternionUnit) t‖ ^ 2 =
      8 * ‖dq‖ ^ 2 := by
  let u := star (q t) * dq
  let n := quaternionDirector (q t) firstQuaternionUnit
  let m := quaternionDirector (q t) secondQuaternionUnit
  let p := quaternionDirector (q t) thirdQuaternionUnit
  have hq : ‖q t‖ = 1 := hunit.self_of_nhds
  have hn : ‖n‖ = 1 := (norm_quaternionDirector hq rfl).trans norm_firstQuaternionUnit
  have hm : ‖m‖ = 1 := (norm_quaternionDirector hq rfl).trans norm_secondQuaternionUnit
  have hp : ‖p‖ = 1 := (norm_quaternionDirector hq rfl).trans norm_thirdQuaternionUnit
  have hnm : inner ℝ n m = 0 := inner_quaternionDirector hq rfl rfl (by
    norm_num [firstQuaternionUnit, secondQuaternionUnit])
  have hnp : inner ℝ n p = 0 := inner_quaternionDirector hq rfl rfl (by
    norm_num [firstQuaternionUnit, thirdQuaternionUnit])
  have hmp : inner ℝ m p = 0 := inner_quaternionDirector hq rfl rfl (by
    norm_num [secondQuaternionUnit, thirdQuaternionUnit])
  have hd₁ : HasDerivAt (fun s => quaternionDirector (q s) firstQuaternionUnit)
      ((2 * u.imK) • m + (-2 * u.imJ) • p) t := by
    simpa only [u, m, p, commutator_firstQuaternionUnit, quaternionDirector_add_smul] using
      hasDerivAt_quaternionDirector hd hunit firstQuaternionUnit
  have hd₂ : HasDerivAt (fun s => quaternionDirector (q s) secondQuaternionUnit)
      ((-2 * u.imK) • n + (2 * u.imI) • p) t := by
    simpa only [u, n, p, commutator_secondQuaternionUnit, quaternionDirector_add_smul] using
      hasDerivAt_quaternionDirector hd hunit secondQuaternionUnit
  have hd₃ : HasDerivAt (fun s => quaternionDirector (q s) thirdQuaternionUnit)
      ((2 * u.imJ) • n + (-2 * u.imI) • m) t := by
    simpa only [u, n, m, commutator_thirdQuaternionUnit, quaternionDirector_add_smul] using
      hasDerivAt_quaternionDirector hd hunit thirdQuaternionUnit
  have huv : ‖u‖ = ‖dq‖ := by
    simp only [u, norm_mul, Quaternion.norm_star, hq, one_mul]
  have hure : u.re = 0 := quaternionVelocity_re_eq_zero hd hunit
  rw [hd₁.deriv, hd₂.deriv, hd₃.deriv, norm_sq_smul_add_of_inner_eq_zero hm hp hmp,
    norm_sq_smul_add_of_inner_eq_zero hn hp hnp, norm_sq_smul_add_of_inner_eq_zero hn hm hnm,
    ← huv, pow_two ‖u‖, ← Quaternion.normSq_eq_norm_mul_self, Quaternion.normSq_def', hure]
  ring

/-- The biaxial energy density dominates half the full frame speed squared times the radius squared. -/
theorem cover_curve_metric_ge (a : BulkCoefficients) (v : ℝ → Sphere3) {dq : ℍ} {t : ℝ}
    (hd : HasDerivAt (fun s => Quaternion.linearIsometryEquivTuple.symm
      (v s : QuaternionCoordinates)) dq t) :
    4 * vacuumRadius a ^ 2 * ‖dq‖ ^ 2 ≤
      (1 / 2 : ℝ) * ‖deriv (fun s => (cover a (v s) : Tensor)) t‖ ^ 2 := by
  let q (s : ℝ) := Quaternion.linearIsometryEquivTuple.symm (v s : QuaternionCoordinates)
  let u := star (q t) * dq
  have hure : u.re = 0 := quaternionVelocity_re_eq_zero (q := q) hd
    (Eventually.of_forall fun s => quaternionTuple_symm_norm_eq_one (v s))
  have hu : ‖u‖ = ‖dq‖ := by
    simp only [u, q, norm_mul, Quaternion.norm_star, quaternionTuple_symm_norm_eq_one, one_mul]
  have hm := cover_curve_metric a v hd
  change _ = 4 * vacuumRadius a ^ 2 * (u.imI ^ 2 + u.imJ ^ 2 + 4 * u.imK ^ 2) at hm
  rw [hm, ← hu, pow_two ‖u‖, ← Quaternion.normSq_eq_norm_mul_self, Quaternion.normSq_def', hure]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  nlinarith [sq_nonneg u.imK]

theorem cover_curve_metric_le (a : BulkCoefficients) (v : ℝ → Sphere3) {dq : ℍ} {t : ℝ}
    (hd : HasDerivAt (fun s => Quaternion.linearIsometryEquivTuple.symm
      (v s : QuaternionCoordinates)) dq t) :
    (1 / 2 : ℝ) * ‖deriv (fun s => (cover a (v s) : Tensor)) t‖ ^ 2 ≤
      16 * vacuumRadius a ^ 2 * ‖dq‖ ^ 2 := by
  let q (s : ℝ) := Quaternion.linearIsometryEquivTuple.symm (v s : QuaternionCoordinates)
  let u := star (q t) * dq
  have hure : u.re = 0 := quaternionVelocity_re_eq_zero (q := q) hd
    (Eventually.of_forall fun s => quaternionTuple_symm_norm_eq_one (v s))
  have hu : ‖u‖ = ‖dq‖ := by
    simp only [u, q, norm_mul, Quaternion.norm_star, quaternionTuple_symm_norm_eq_one, one_mul]
  have hm := cover_curve_metric a v hd
  change _ = 4 * vacuumRadius a ^ 2 * (u.imI ^ 2 + u.imJ ^ 2 + 4 * u.imK ^ 2) at hm
  rw [hm, ← hu, pow_two ‖u‖, ← Quaternion.normSq_eq_norm_mul_self, Quaternion.normSq_def', hure]
  calc
    _ ≤ 4 * vacuumRadius a ^ 2 * (4 * (0 ^ 2 + u.imI ^ 2 + u.imJ ^ 2 + u.imK ^ 2)) :=
      mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg u.imI, sq_nonneg u.imJ]) (by positivity)
    _ = _ := by ring

theorem cover_curve_metric_ge_directors (a : BulkCoefficients) (v : ℝ → Sphere3) {dq : ℍ} {t : ℝ}
    (hd : HasDerivAt (fun s => Quaternion.linearIsometryEquivTuple.symm
      (v s : QuaternionCoordinates)) dq t) :
    vacuumRadius a ^ 2 / 2 *
      (‖deriv (fun s => firstFrameVector (v s : QuaternionCoordinates)) t‖ ^ 2 +
        ‖deriv (fun s => secondFrameVector (v s : QuaternionCoordinates)) t‖ ^ 2 +
        ‖deriv (fun s => WithLp.toLp 2
          ((firstFrameVector (v s : QuaternionCoordinates)).ofLp ⨯₃
            (secondFrameVector (v s : QuaternionCoordinates)).ofLp)) t‖ ^ 2) ≤
      (1 / 2 : ℝ) * ‖deriv (fun s => (cover a (v s) : Tensor)) t‖ ^ 2 := by
  have hframe := quaternion_directors_curve_metric hd
    (Eventually.of_forall fun s => quaternionTuple_symm_norm_eq_one (v s))
  simp only [quaternionDirector_third_cross (quaternionTuple_symm_norm_eq_one (v _)),
    quaternionDirector_firstFrame, quaternionDirector_secondFrame] at hframe
  rw [hframe]
  convert cover_curve_metric_ge a v hd using 1
  ring

theorem ac_comp_lipschitzOn {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {f : ℝ → X} {g : X → Y} {s : Set X} {a b : ℝ} {K : ℝ≥0}
    (hf : AbsolutelyContinuousOnInterval f a b) (hg : LipschitzOnWith K g s)
    (hmap : MapsTo f (uIcc a b) s) : AbsolutelyContinuousOnInterval (g ∘ f) a b := by
  rw [absolutelyContinuousOnInterval_iff] at hf ⊢
  intro ε hε
  obtain ⟨δ, hδ, hsmall⟩ := hf (ε / ((K : ℝ) + 1)) (by positivity)
  refine ⟨δ, hδ, fun E hE hlength => ?_⟩
  have hsum := hsmall E hE hlength
  have hcmp : ∀ i ∈ Finset.range E.1,
      dist (g (f (E.2 i).1)) (g (f (E.2 i).2)) ≤
        ((K : ℝ) + 1) * dist (f (E.2 i).1) (f (E.2 i).2) := by
    intro i hi
    have hends := hE.1 i hi
    exact (hg.dist_le_mul _ (hmap hends.1) _ (hmap hends.2)).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) dist_nonneg)
  calc
    _ ≤ ∑ i ∈ Finset.range E.1, ((K : ℝ) + 1) * dist (f (E.2 i).1) (f (E.2 i).2) :=
      Finset.sum_le_sum hcmp
    _ < ε := by rwa [← Finset.mul_sum, ← lt_div_iff₀' (by positivity)]

theorem ae_differentiableAt_quaternion_of_ac {q : ℝ → ℍ} {a b : ℝ}
    (hq : AbsolutelyContinuousOnInterval q a b) :
    ∀ᵐ t, t ∈ uIcc a b → DifferentiableAt ℝ q t := by
  let e := Quaternion.linearIsometryEquivTuple
  let F : ℍ ≃L[ℝ] (Fin 4 → ℝ) :=
    e.toContinuousLinearEquiv.trans (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 => ℝ))
  let c (i : Fin 4) : ℍ →L[ℝ] ℝ := (ContinuousLinearMap.proj i).comp F.toContinuousLinearMap
  have hcoord (i : Fin 4) : AbsolutelyContinuousOnInterval (fun t => c i (q t)) a b :=
    ac_comp_lipschitzOn hq (c i).lipschitz.lipschitzOnWith (mapsTo_univ _ _)
  filter_upwards [ae_all_iff.mpr fun i => (hcoord i).ae_differentiableAt] with t ht
  intro hmem
  have hF : DifferentiableAt ℝ (fun t => F (q t)) t :=
    differentiableAt_pi.mpr fun i => ht i hmem
  have h := F.symm.toContinuousLinearMap.differentiableAt.comp t hF
  have hfun : (⇑F.symm ∘ fun t => F (q t)) = q :=
    funext fun s => F.symm_apply_apply (q s)
  change DifferentiableAt ℝ (⇑F.symm ∘ fun t => F (q t)) t at h
  rwa [hfun] at h

/-- The integrated anisotropic metric on an absolutely continuous lift. -/
theorem cover_curve_energy_eq (a : BulkCoefficients) (v : ℝ → Sphere3) {s t : ℝ} :
    let q (x : ℝ) := Quaternion.linearIsometryEquivTuple.symm (v x : QuaternionCoordinates)
    let u (x : ℝ) := star (q x) * deriv q x
    AbsolutelyContinuousOnInterval q s t →
    (∫ x in s..t, (1 / 2 : ℝ) * ‖deriv (fun y => (cover a (v y) : Tensor)) x‖ ^ 2) =
      vacuumRadius a ^ 2 *
        ∫ x in s..t, 4 * (2 * (u x).imK) ^ 2 + (-2 * (u x).imJ) ^ 2 + (2 * (u x).imI) ^ 2 := by
  intro q u hq
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [ae_differentiableAt_quaternion_of_ac hq] with x hx hmem
  have hmetric := cover_curve_metric a v (hx (uIoc_subset_uIcc hmem)).hasDerivAt
  change _ = 4 * vacuumRadius a ^ 2 * ((u x).imI ^ 2 + (u x).imJ ^ 2 + 4 * (u x).imK ^ 2)
    at hmetric
  exact hmetric.trans (by ring)

private theorem abs_inner_tangent_le (e x dx : ℍ) (he : ‖e‖ = 1) (hx : ‖x‖ = 1)
    (htan : inner ℝ x dx = 0) :
    |inner ℝ e dx| ≤ Real.sqrt (1 - (inner ℝ e x) ^ 2) * ‖dx‖ := by
  let s := inner ℝ e x
  let y := e - s • x
  have hy : ‖y‖ ^ 2 = 1 - s ^ 2 := by
    rw [show y = e - s • x from rfl, norm_sub_sq_real, real_inner_smul_right,
      norm_smul, he, hx, mul_one, Real.norm_eq_abs, sq_abs]
    change 1 ^ 2 - 2 * (s * s) + s ^ 2 = 1 - s ^ 2
    ring
  have hnorm : Real.sqrt (1 - s ^ 2) = ‖y‖ := by rw [← hy, Real.sqrt_sq (norm_nonneg _)]
  have hinner : inner ℝ y dx = inner ℝ e dx := by simp [y, inner_sub_left, real_inner_smul_left, htan]
  rw [← hinner, hnorm]
  exact abs_real_inner_le_norm _ _

private theorem abs_angle_derivative_le (e x dx : ℍ) (he : ‖e‖ = 1) (hx : ‖x‖ = 1)
    (htan : inner ℝ x dx = 0) {ρ : ℝ} (hρ : ρ ∈ Ioo 0 1) :
    |(-(1 / Real.sqrt (1 - (ρ * inner ℝ e x) ^ 2))) * (ρ * inner ℝ e dx)| ≤ ‖dx‖ := by
  let s := inner ℝ e x
  have hs : |s| ≤ 1 := by simpa only [s, he, hx, mul_one] using abs_real_inner_le_norm e x
  have hρs : |ρ * s| < 1 := by
    rw [abs_mul, abs_of_pos hρ.1]
    exact (mul_le_mul_of_nonneg_left hs hρ.1.le).trans_lt (by simpa using hρ.2)
  have hsSq : s ^ 2 ≤ 1 := by nlinarith [sq_abs s, abs_nonneg s]
  have hρsSq : (ρ * s) ^ 2 < 1 := by nlinarith [sq_abs (ρ * s), abs_nonneg (ρ * s)]
  have hd := Real.sqrt_pos.2 (sub_pos.mpr hρsSq)
  have hratio : ρ * Real.sqrt (1 - s ^ 2) ≤ Real.sqrt (1 - (ρ * s) ^ 2) := by
    apply (sq_le_sq₀ (mul_nonneg hρ.1.le (Real.sqrt_nonneg _)) hd.le).mp
    rw [mul_pow, Real.sq_sqrt (sub_nonneg.mpr hsSq), Real.sq_sqrt (sub_nonneg.mpr hρsSq.le)]
    nlinarith [sq_nonneg (1 - ρ), hρ.1, hρ.2, mul_nonneg hρ.1.le (sub_nonneg.mpr hρ.2.le)]
  change |(-(1 / Real.sqrt (1 - (ρ * s) ^ 2))) * (ρ * inner ℝ e dx)| ≤ ‖dx‖
  rw [abs_mul, abs_neg, abs_of_pos (one_div_pos.mpr hd), abs_mul, abs_of_pos hρ.1,
    one_div_mul_eq_div]
  apply (div_le_iff₀ hd).2
  calc
    ρ * |inner ℝ e dx| ≤ ρ * (Real.sqrt (1 - s ^ 2) * ‖dx‖) :=
      mul_le_mul_of_nonneg_left (abs_inner_tangent_le e x dx he hx htan) hρ.1.le
    _ ≤ ‖dx‖ * Real.sqrt (1 - (ρ * s) ^ 2) := by
      rw [← mul_assoc, mul_comm ‖dx‖]
      exact mul_le_mul_of_nonneg_right hratio (norm_nonneg _)

/-- The unit quaternion spherical distance is bounded by the length of an absolutely continuous lift. -/
theorem quaternion_curve_arc_le_integral_speed {q : ℝ → ℍ} {a b : ℝ} (hab : a ≤ b)
    (hq : AbsolutelyContinuousOnInterval q a b) (hunit : ∀ t, ‖q t‖ = 1)
    (hspeed : IntervalIntegrable (fun t => ‖deriv q t‖) volume a b) :
    Real.arccos (inner ℝ (q a) (q b)) ≤ ∫ t in a..b, ‖deriv q t‖ := by
  let e := q a
  have he : ‖e‖ = 1 := hunit a
  have hreg (ρ : ℝ) (hρ : ρ ∈ Ioo 0 1) :
      Real.arccos (ρ * inner ℝ e (q b)) - Real.arccos ρ ≤ ∫ t in a..b, ‖deriv q t‖ := by
    let P : ℍ →L[ℝ] ℝ := ρ • innerSL ℝ e
    let v (t : ℝ) := ρ * inner ℝ e (q t)
    let F (t : ℝ) := Real.arccos (v t)
    have hP (x : ℍ) : P x = ρ * inner ℝ e x := rfl
    have hv (t : ℝ) : v t ∈ Icc (-ρ) ρ := by
      have h := abs_real_inner_le_norm e (q t)
      rw [he, hunit t, mul_one] at h
      have hv : |v t| ≤ ρ := by
        change |ρ * inner ℝ e (q t)| ≤ ρ
        rw [abs_mul, abs_of_pos hρ.1]
        simpa using mul_le_mul_of_nonneg_left h hρ.1.le
      exact abs_le.mp hv
    have hmac : ContDiffOn ℝ 1 Real.arccos (Icc (-ρ) ρ) := by
      intro x hx
      exact (Real.contDiffAt_arccos (by linarith [hx.1, hρ.2])
        (by linarith [hx.2, hρ.2])).contDiffWithinAt
    obtain ⟨K, hK⟩ := hmac.exists_lipschitzOnWith (by decide) (convex_Icc _ _) isCompact_Icc
    have hvac : AbsolutelyContinuousOnInterval v a b :=
      ac_comp_lipschitzOn (f := q) (g := ⇑P) hq P.lipschitz.lipschitzOnWith (mapsTo_univ _ _)
    have hmap : MapsTo v (uIcc a b) (Icc (-ρ) ρ) := fun t _ => hv t
    have hFac : AbsolutelyContinuousOnInterval F a b :=
      ac_comp_lipschitzOn (f := v) (g := Real.arccos) hvac hK hmap
    have hderiv : deriv F ≤ᵐ[volume.restrict (Icc a b)] fun t => ‖deriv q t‖ := by
      apply (ae_restrict_iff' measurableSet_Icc).2
      filter_upwards [ae_differentiableAt_quaternion_of_ac hq] with t ht
      intro htmem
      have hq' := (ht (by simpa only [uIcc_of_le hab] using htmem)).hasDerivAt
      have ho : HasFDerivAt (⇑P) P (q t) := P.hasFDerivAt
      have hV : HasDerivAt v (ρ * inner ℝ e (deriv q t)) t := by
        exact ho.comp_hasDerivAt (f := q) (f' := deriv q t) t hq'
      have hr := Real.hasDerivAt_arccos (x := v t) (by linarith [(hv t).1, hρ.2])
        (by linarith [(hv t).2, hρ.2])
      have hF := hr.comp t hV
      have htan : inner ℝ (q t) (deriv q t) = 0 := by
        rw [real_inner_comm, Quaternion.inner_def]
        have hqre := quaternionVelocity_re_eq_zero hq' (Eventually.of_forall hunit)
        rw [show (deriv q t * star (q t)).re = (star (q t) * deriv q t).re from by
          simp only [Quaternion.re_mul]
          ring]
        exact hqre
      exact (le_abs_self _).trans <| by
        rw [show deriv F t = _ from hF.deriv]
        exact abs_angle_derivative_le e (q t) (deriv q t) he (hunit t) htan hρ
    have hFTC := hFac.integral_deriv_eq_sub
    have hFa : F a = Real.arccos ρ := by
      change Real.arccos (ρ * inner ℝ e e) = Real.arccos ρ
      simp only [real_inner_self_eq_norm_sq, he, one_pow, mul_one]
    rw [← hFa, ← show F b = Real.arccos (ρ * inner ℝ e (q b)) from rfl, ← hFTC]
    exact intervalIntegral.integral_mono_ae_restrict hab hFac.intervalIntegrable_deriv hspeed hderiv
  let S : Set ℝ := {ρ | Real.arccos (ρ * inner ℝ e (q b)) - Real.arccos ρ ≤
    ∫ t in a..b, ‖deriv q t‖}
  have hS : IsClosed S := isClosed_le
    ((Real.continuous_arccos.comp (continuous_id.mul continuous_const)).sub
      Real.continuous_arccos) continuous_const
  have hone : (1 : ℝ) ∈ closure (Ioo 0 1) := by rw [closure_Ioo zero_ne_one]; simp
  have hlim := (hS.closure_subset_iff.2 (show Ioo 0 1 ⊆ S from fun ρ hρ => hreg ρ hρ)) hone
  simpa only [S, mem_setOf_eq, e, one_mul, Real.arccos_one, sub_zero] using hlim

theorem sq_integral_le_length_mul_integral_sq {f : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hf : IntervalIntegrable f volume a b)
    (hf2 : IntervalIntegrable (fun t => f t ^ 2) volume a b) :
    (∫ t in a..b, f t) ^ 2 ≤ (b - a) * ∫ t in a..b, f t ^ 2 := by
  let L := ∫ t in a..b, f t
  let E := ∫ t in a..b, f t ^ 2
  let c := L / (b - a)
  have hnon := intervalIntegral.integral_nonneg_of_forall (μ := volume) (f := fun t => (f t - c) ^ 2)
    hab.le (fun t => sq_nonneg (f t - c))
  have hs : (fun t => (f t - c) ^ 2) = fun t => (f t ^ 2 - (2 * c) * f t) + c ^ 2 := by
    funext t
    ring
  rw [hs, intervalIntegral.integral_add (hf2.sub (hf.const_mul (2 * c))) intervalIntegrable_const,
    intervalIntegral.integral_sub hf2 (hf.const_mul (2 * c)),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul] at hnon
  change 0 ≤ E - 2 * c * L + (b - a) * c ^ 2 at hnon
  have hpos := sub_pos.mpr hab
  have hrewrite : E - 2 * c * L + (b - a) * c ^ 2 = ((b - a) * E - L ^ 2) / (b - a) := by
    dsimp only [c]
    field_simp [hpos.ne']
    ring
  rw [hrewrite, le_div_iff₀ hpos, zero_mul, sub_nonneg] at hnon
  exact hnon

/-- The projected energy controls the square of the angular separation of the lift endpoints. -/
theorem cover_curve_energy_ge_arc (a : BulkCoefficients) (v : ℝ → Sphere3) {s t : ℝ}
    (hst : s < t) :
    let q (x : ℝ) := Quaternion.linearIsometryEquivTuple.symm (v x : QuaternionCoordinates)
    AbsolutelyContinuousOnInterval q s t →
    IntervalIntegrable (fun x => ‖deriv q x‖) volume s t →
    IntervalIntegrable (fun x => ‖deriv q x‖ ^ 2) volume s t →
    IntervalIntegrable (fun x => (1 / 2 : ℝ) * ‖deriv (fun y => (cover a (v y) : Tensor)) x‖ ^ 2)
      volume s t →
    4 * vacuumRadius a ^ 2 * Real.arccos (inner ℝ (q s) (q t)) ^ 2 ≤
      (t - s) * ∫ x in s..t, (1 / 2 : ℝ) * ‖deriv (fun y => (cover a (v y) : Tensor)) x‖ ^ 2 := by
  intro q hq hspeed hqenergy hQenergy
  have hunit (x : ℝ) : ‖q x‖ = 1 := quaternionTuple_symm_norm_eq_one (v x)
  have hangle := quaternion_curve_arc_le_integral_speed hst.le hq hunit hspeed
  have hangleSq := (sq_le_sq₀ (Real.arccos_nonneg _) ((Real.arccos_nonneg _).trans hangle)).2 hangle
  have hcoef : 0 ≤ 4 * vacuumRadius a ^ 2 := by positivity
  have he :
      (fun x => 4 * vacuumRadius a ^ 2 * ‖deriv q x‖ ^ 2) ≤ᵐ[volume.restrict (Icc s t)]
        fun x => (1 / 2 : ℝ) * ‖deriv (fun y => (cover a (v y) : Tensor)) x‖ ^ 2 := by
    apply (ae_restrict_iff' measurableSet_Icc).2
    filter_upwards [ae_differentiableAt_quaternion_of_ac hq] with x hx hxmem
    exact cover_curve_metric_ge a v ((hx (by simpa only [uIcc_of_le hst.le] using hxmem)).hasDerivAt)
  have heInt := intervalIntegral.integral_mono_ae_restrict hst.le
    (hqenergy.const_mul (4 * vacuumRadius a ^ 2)) hQenergy he
  rw [intervalIntegral.integral_const_mul] at heInt
  calc
    _ ≤ 4 * vacuumRadius a ^ 2 * (∫ x in s..t, ‖deriv q x‖) ^ 2 :=
      mul_le_mul_of_nonneg_left hangleSq hcoef
    _ ≤ 4 * vacuumRadius a ^ 2 * ((t - s) * ∫ x in s..t, ‖deriv q x‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (sq_integral_le_length_mul_integral_sq hst hspeed hqenergy) hcoef
    _ = (t - s) * (4 * vacuumRadius a ^ 2 * ∫ x in s..t, ‖deriv q x‖ ^ 2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left heInt (sub_nonneg.mpr hst.le)

private theorem quaternionWordReal_inv_re_eq_zero {g : QuaternionGroup 2} (hg : IsLightQuaternion g) :
    (quaternionWordReal g⁻¹).re = 0 := by
  rcases hg with rfl | rfl | rfl | rfl
  · rw [show (QuaternionGroup.a 1 : QuaternionGroup 2)⁻¹ = .a 3 by decide, quaternionWordReal_negative_i]
  · rw [show (QuaternionGroup.a 3 : QuaternionGroup 2)⁻¹ = .a 1 by decide, quaternionWordReal_i]
  · rw [show (QuaternionGroup.xa 0 : QuaternionGroup 2)⁻¹ = .xa 2 by decide, quaternionWordReal_negative_j]
  · rw [show (QuaternionGroup.xa 2 : QuaternionGroup 2)⁻¹ = .xa 0 by decide, quaternionWordReal_j]

/-- A lift ending at a light deck translate has projected half energy at least `kappaStar a`. -/
theorem cover_curve_energy_ge_light (a : BulkCoefficients) (v : ℝ → Sphere3)
    {g : QuaternionGroup 2} (hg : IsLightQuaternion g) (hend : v (2 * Real.pi) = g • v 0) :
    let q (x : ℝ) := Quaternion.linearIsometryEquivTuple.symm (v x : QuaternionCoordinates)
    AbsolutelyContinuousOnInterval q 0 (2 * Real.pi) →
    IntervalIntegrable (fun x => ‖deriv q x‖) volume 0 (2 * Real.pi) →
    IntervalIntegrable (fun x => ‖deriv q x‖ ^ 2) volume 0 (2 * Real.pi) →
    IntervalIntegrable (fun x => (1 / 2 : ℝ) * ‖deriv (fun y => (cover a (v y) : Tensor)) x‖ ^ 2)
      volume 0 (2 * Real.pi) →
    kappaStar a ≤ ∫ x in 0..(2 * Real.pi), (1 / 2 : ℝ) * ‖deriv (fun y => (cover a (v y) : Tensor)) x‖ ^ 2 := by
  intro q hq hspeed hqenergy hQenergy
  have hpos : (0 : ℝ) < 2 * Real.pi := by positivity
  have h := cover_curve_energy_ge_arc a v hpos hq hspeed hqenergy hQenergy
  have horth : inner ℝ (q 0) (q (2 * Real.pi)) = 0 := by
    rw [real_inner_comm (q (2 * Real.pi)) (q 0), Quaternion.inner_def]
    change (Quaternion.linearIsometryEquivTuple.symm (v (2 * Real.pi)).val * star (q 0)).re = 0
    rw [hend, quaternionTuple_symm_smul]
    exact quaternionConjugate_re_eq_zero (q 0) (quaternionWordReal_inv_re_eq_zero hg)
  change 4 * vacuumRadius a ^ 2 * Real.arccos (inner ℝ (q 0) (q (2 * Real.pi))) ^ 2 ≤ _ at h
  rw [horth, Real.arccos_zero, sub_zero] at h
  apply (mul_le_mul_iff_right₀ hpos).mp
  calc
    2 * Real.pi * kappaStar a = 4 * vacuumRadius a ^ 2 * (Real.pi / 2) ^ 2 := by
      unfold kappaStar
      ring
    _ ≤ _ := h

/-- A lift ending at the central antipode has projected half energy at least four times `kappaStar a`. -/
theorem cover_curve_energy_ge_antipodal (a : BulkCoefficients) (v : ℝ → Sphere3)
    (hend : v (2 * Real.pi) = (QuaternionGroup.a 2 : QuaternionGroup 2) • v 0) :
    let q (x : ℝ) := Quaternion.linearIsometryEquivTuple.symm (v x : QuaternionCoordinates)
    AbsolutelyContinuousOnInterval q 0 (2 * Real.pi) →
    IntervalIntegrable (fun x => ‖deriv q x‖) volume 0 (2 * Real.pi) →
    IntervalIntegrable (fun x => ‖deriv q x‖ ^ 2) volume 0 (2 * Real.pi) →
    IntervalIntegrable (fun x => (1 / 2 : ℝ) * ‖deriv (fun y => (cover a (v y) : Tensor)) x‖ ^ 2)
      volume 0 (2 * Real.pi) →
    4 * kappaStar a ≤ ∫ x in 0..(2 * Real.pi),
      (1 / 2 : ℝ) * ‖deriv (fun y => (cover a (v y) : Tensor)) x‖ ^ 2 := by
  intro q hq hspeed hqenergy hQenergy
  have hpos : (0 : ℝ) < 2 * Real.pi := by positivity
  have h := cover_curve_energy_ge_arc a v hpos hq hspeed hqenergy hQenergy
  have hneg : q (2 * Real.pi) = -(q 0) := by
    change Quaternion.linearIsometryEquivTuple.symm (v (2 * Real.pi)).val = -(q 0)
    rw [hend, quaternionSphereAction_minusOne_val, map_neg]
  have hinner : inner ℝ (q 0) (q (2 * Real.pi)) = -1 := by
    rw [hneg, inner_neg_right, real_inner_self_eq_norm_sq]
    change -‖Quaternion.linearIsometryEquivTuple.symm (v 0).val‖ ^ 2 = -1
    rw [quaternionTuple_symm_norm_eq_one, one_pow]
  change 4 * vacuumRadius a ^ 2 * Real.arccos (inner ℝ (q 0) (q (2 * Real.pi))) ^ 2 ≤ _ at h
  rw [hinner, Real.arccos_neg_one, sub_zero] at h
  apply (mul_le_mul_iff_right₀ hpos).mp
  calc
    2 * Real.pi * (4 * kappaStar a) = 4 * vacuumRadius a ^ 2 * Real.pi ^ 2 := by
      unfold kappaStar
      ring
    _ ≤ _ := h

end Thesis
