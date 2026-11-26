module

public import Thesis.Foundation.QuaternionFrameMetric
public import Thesis.Foundation.VacuumFundamentalGroup
public import StratificationTheory.Foundation.BanachIntervalWeakRepresentative

/-! Local inverse estimates and Sobolev lifts for the quaternion vacuum cover. -/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped ContDiff Matrix Matrix.Norms.Frobenius Quaternion Topology

namespace Thesis

theorem norm_sub_conjugate_le {q p b : ℍ} (hq : ‖q‖ = 1) (hp : ‖p‖ = 1)
    (hb : ‖b‖ = 1) :
    ‖quaternionConjugate q b - quaternionConjugate p b‖ ≤ 2 * ‖q - p‖ := by
  rw [show quaternionConjugate q b - quaternionConjugate p b =
      (q - p) * b * star q + p * b * star (q - p) by
    simp only [quaternionConjugate, star_sub, sub_mul, mul_sub]
    abel]
  exact (norm_add_le _ _).trans_eq (by
    simp only [norm_mul, Quaternion.norm_star, hq, hp, hb, one_mul, mul_one, two_mul])

private theorem norm_sub_conjugate_eq_commutator {q p : ℍ} (hq : ‖q‖ = 1) (hp : ‖p‖ = 1)
    (b : ℍ) :
    ‖quaternionConjugate q b - quaternionConjugate p b‖ =
      ‖(star q * p) * b - b * (star q * p)‖ := by
  let X := quaternionConjugate q b - quaternionConjugate p b
  have h : star q * X * p = b * (star q * p) - (star q * p) * b := by
    simp only [X, quaternionConjugate, mul_sub, sub_mul]
    congr 1
    · rw [show star q * (q * b * star q) * p = (star q * q) * (b * (star q * p)) by
        simp only [mul_assoc], quaternionUnit_star_mul hq, one_mul]
    · rw [show star q * (p * b * star p) * p = (star q * p) * b * (star p * p) by
        simp only [mul_assoc], quaternionUnit_star_mul hp, mul_one]
  have hnorm := congrArg (fun x : ℍ => ‖x‖) h
  simp only [norm_mul, Quaternion.norm_star, hq, hp, one_mul, mul_one] at hnorm
  calc
    _ = ‖b * (star q * p) - (star q * p) * b‖ := hnorm
    _ = _ := norm_sub_rev _ _

private theorem norm_sq_commutator_first (u : ℍ) :
    ‖u * firstQuaternionUnit - firstQuaternionUnit * u‖ ^ 2 =
      4 * (u.imJ ^ 2 + u.imK ^ 2) := by
  rw [commutator_firstQuaternionUnit, pow_two, ← Quaternion.normSq_eq_norm_mul_self,
    Quaternion.normSq_def']
  simp [secondQuaternionUnit, thirdQuaternionUnit]
  ring

private theorem norm_sq_commutator_second (u : ℍ) :
    ‖u * secondQuaternionUnit - secondQuaternionUnit * u‖ ^ 2 =
      4 * (u.imI ^ 2 + u.imK ^ 2) := by
  rw [commutator_secondQuaternionUnit, pow_two, ← Quaternion.normSq_eq_norm_mul_self,
    Quaternion.normSq_def']
  simp [firstQuaternionUnit, thirdQuaternionUnit]
  ring

private theorem unitQuaternion_sub_sq {q p : ℍ} (hq : ‖q‖ = 1) (hp : ‖p‖ = 1) :
    ‖q - p‖ ^ 2 = 2 - 2 * (star q * p).re := by
  have hnorm : ‖q - p‖ = ‖1 - star q * p‖ := by
    calc
      _ = ‖star q * (q - p)‖ := by simp [norm_mul, hq]
      _ = _ := by rw [mul_sub, quaternionUnit_star_mul hq]
  rw [hnorm, norm_sub_sq_real, norm_one, norm_mul, Quaternion.norm_star, hq, hp,
    real_inner_comm (star q * p) 1, Quaternion.inner_def, star_one, mul_one]
  ring

private theorem normSq_sub_le_sum_director_sq {q p : ℍ} (hq : ‖q‖ = 1) (hp : ‖p‖ = 1)
    (hclose : ‖q - p‖ ≤ 1 / 2) :
    ‖q - p‖ ^ 2 ≤ ‖quaternionConjugate q firstQuaternionUnit - quaternionConjugate p firstQuaternionUnit‖ ^ 2 +
      ‖quaternionConjugate q secondQuaternionUnit - quaternionConjugate p secondQuaternionUnit‖ ^ 2 := by
  let u := star q * p
  have hu : ‖u‖ = 1 := by simp [u, norm_mul, hq, hp]
  have hsum : u.re ^ 2 + u.imI ^ 2 + u.imJ ^ 2 + u.imK ^ 2 = 1 := by
    rw [← Quaternion.normSq_def', Quaternion.normSq_eq_norm_mul_self, hu, one_mul]
  have hqsub : ‖q - p‖ ^ 2 = 2 - 2 * u.re := unitQuaternion_sub_sq hq hp
  have hre : 0 ≤ u.re := by nlinarith [mul_nonneg (norm_nonneg (q - p)) (sub_nonneg.mpr hclose)]
  have hresq : u.re ^ 2 ≤ 1 := by nlinarith [sq_nonneg u.imI, sq_nonneg u.imJ, sq_nonneg u.imK]
  have hre1 : u.re ≤ 1 := (sq_le_sq₀ hre zero_le_one).mp (by simpa using hresq)
  rw [norm_sub_conjugate_eq_commutator hq hp, norm_sub_conjugate_eq_commutator hq hp,
    norm_sq_commutator_first, norm_sq_commutator_second]
  change ‖q - p‖ ^ 2 ≤ 4 * (u.imJ ^ 2 + u.imK ^ 2) + 4 * (u.imI ^ 2 + u.imK ^ 2)
  nlinarith [mul_nonneg hre (sub_nonneg.mpr hre1), sq_nonneg u.imI,
    sq_nonneg u.imJ, sq_nonneg u.imK]

private theorem norm_sub_le_projector_sub {x y : Point} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hclose : ‖x - y‖ ≤ 1) :
    ‖x - y‖ ≤ ‖directorProjector x - directorProjector y‖ := by
  let c := inner ℝ x y
  have hdist : ‖x - y‖ ^ 2 = 2 - 2 * c := by
    rw [norm_sub_sq_real, hx, hy]
    change (1 : ℝ) ^ 2 - 2 * c + 1 ^ 2 = _
    ring
  have hc : 0 ≤ c := by
    nlinarith [mul_nonneg (norm_nonneg (x - y)) (sub_nonneg.mpr hclose)]
  have hc1 : c ≤ 1 := by
    have h := real_inner_le_norm x y
    rwa [hx, hy, one_mul] at h
  have hP : ‖directorProjector x - directorProjector y‖ ^ 2 = 2 - 2 * c ^ 2 := by
    rw [norm_sq_eq_frobenius]
    simp only [frobenius, Matrix.transpose_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub]
    change frobenius (directorProjector x) (directorProjector x) -
        frobenius (directorProjector y) (directorProjector x) -
        (frobenius (directorProjector x) (directorProjector y) -
          frobenius (directorProjector y) (directorProjector y)) = _
    simp only [frobenius_directorProjector, real_inner_comm x y, real_inner_self_eq_norm_sq, hx, hy,
      one_pow]
    change (1 : ℝ) - c ^ 2 - (c ^ 2 - 1) = _
    ring
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  nlinarith [mul_nonneg hc (sub_nonneg.mpr hc1)]

private theorem norm_sq_sub_sq_le (A B : Tensor) :
    ‖A ^ 2 - B ^ 2‖ ≤ (‖A‖ + ‖B‖) * ‖A - B‖ := by
  rw [show A ^ 2 - B ^ 2 = A * (A - B) + (A - B) * B by noncomm_ring]
  calc
    _ ≤ ‖A * (A - B)‖ + ‖(A - B) * B‖ := norm_add_le _ _
    _ ≤ ‖A‖ * ‖A - B‖ + ‖A - B‖ * ‖B‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = _ := by ring

private theorem norm_le_of_smul_norm_le (M : Tensor) {c k d : ℝ} (hc : 0 < c)
    (h : ‖c • M‖ ≤ k * d) : ‖M‖ ≤ (k / c) * d := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc] at h
  apply (mul_le_mul_iff_right₀ hc).mp
  calc
    _ ≤ k * d := h
    _ = _ := by field_simp

private theorem projector_poly_norm_sub_le (A B U V : Tensor) {r σ : ℝ} (hr : 0 < r)
    (hσ : |σ| ≤ r) (hA : ‖A‖ = Real.sqrt 2 * r) (hB : ‖B‖ = Real.sqrt 2 * r)
    (hU : A ^ 2 + σ • A = (2 * r ^ 2) • U) (hV : B ^ 2 + σ • B = (2 * r ^ 2) • V) :
    ‖U - V‖ ≤ ((2 * (Real.sqrt 2 * r) + r) / (2 * r ^ 2)) * ‖A - B‖ := by
  have hEq : (2 * r ^ 2) • (U - V) = (A ^ 2 - B ^ 2) + σ • (A - B) := by
    rw [smul_sub, ← hU, ← hV, smul_sub]
    abel
  have hAB := norm_sq_sub_sq_le A B
  rw [hA, hB, ← two_mul] at hAB
  have hbound : ‖(2 * r ^ 2) • (U - V)‖ ≤ (2 * (Real.sqrt 2 * r) + r) * ‖A - B‖ := by
    rw [hEq, add_mul]
    refine (norm_add_le _ _).trans (add_le_add hAB ?_)
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right hσ (norm_nonneg _)
  exact norm_le_of_smul_norm_le _ (by positivity) hbound

private theorem norms_projector_sub_le (a : BulkCoefficients) (f g : VacuumFrame) :
    let r := vacuumRadius a
    let A := ((vacuumFrameProjection a f).val : Tensor)
    let B := ((vacuumFrameProjection a g).val : Tensor)
    let C := (2 * (Real.sqrt 2 * r) + r) / (2 * r ^ 2)
    ‖directorProjector f.val.1 - directorProjector g.val.1‖ ≤ C * ‖A - B‖ ∧
      ‖directorProjector f.val.2 - directorProjector g.val.2‖ ≤ C * ‖A - B‖ := by
  intro r A B C
  have hr : 0 < r := vacuumRadius_pos a
  have hA : ‖A‖ = Real.sqrt 2 * r := by
    calc
      _ = ‖(vacuumFrameProjection a f).val‖ := rfl
      _ = _ := vacuum_norm (vacuumFrameProjection a f).property
  have hB : ‖B‖ = Real.sqrt 2 * r := by
    calc
      _ = ‖(vacuumFrameProjection a g).val‖ := rfl
      _ = _ := vacuum_norm (vacuumFrameProjection a g).property
  have hf₁ : A ^ 2 + r • A = (2 * r ^ 2) • directorProjector f.val.1 :=
    (directorProj_pair a f).1
  have hg₁ : B ^ 2 + r • B = (2 * r ^ 2) • directorProjector g.val.1 :=
    (directorProj_pair a g).1
  have hf₂ : A ^ 2 + (-r) • A = (2 * r ^ 2) • directorProjector f.val.2 := by
    rw [neg_smul, ← sub_eq_add_neg]
    exact (directorProj_pair a f).2
  have hg₂ : B ^ 2 + (-r) • B = (2 * r ^ 2) • directorProjector g.val.2 := by
    rw [neg_smul, ← sub_eq_add_neg]
    exact (directorProj_pair a g).2
  constructor
  · exact projector_poly_norm_sub_le A B (directorProjector f.val.1) (directorProjector g.val.1)
      (r := r) (σ := r) hr (abs_of_pos hr).le hA hB hf₁ hg₁
  · exact projector_poly_norm_sub_le A B (directorProjector f.val.2) (directorProjector g.val.2)
      (r := r) (σ := -r) hr (by rw [abs_neg, abs_of_pos hr]) hA hB hf₂ hg₂

private theorem pureQuaternion_sub (x y : Point) :
    pureQuaternion (x - y) = pureQuaternion x - pureQuaternion y := by
  ext <;> simp [pureQuaternion]

/-- A uniform local inverse estimate in the original sphere and Frobenius distances. -/
theorem cover_dist_le_uniform (a : BulkCoefficients) (v w : Sphere3)
    (hclose : dist v w ≤ 1 / 2) :
    dist v w ≤ (2 * Real.sqrt 2 + 1) / vacuumRadius a * dist (cover a v) (cover a w) := by
  let q := Quaternion.linearIsometryEquivTuple.symm v.val
  let p := Quaternion.linearIsometryEquivTuple.symm w.val
  let f := quaternionFrame v
  let g := quaternionFrame w
  let r := vacuumRadius a
  let C := (2 * (Real.sqrt 2 * r) + r) / (2 * r ^ 2)
  have hq : ‖q‖ = 1 := quaternionTuple_symm_norm_eq_one v
  have hp : ‖p‖ = 1 := quaternionTuple_symm_norm_eq_one w
  have hdist : dist v w = ‖q - p‖ := by
    change dist v.val w.val = ‖q - p‖
    rw [dist_eq_norm, ← Quaternion.linearIsometryEquivTuple.symm.norm_map (v.val - w.val), map_sub]
  have hn : ‖f.val.1 - g.val.1‖ =
      ‖quaternionConjugate q firstQuaternionUnit - quaternionConjugate p firstQuaternionUnit‖ := by
    change ‖firstFrameVector v.val - firstFrameVector w.val‖ = _
    rw [← norm_pureQuaternion, pureQuaternion_sub, firstFrameVector_pureQuaternion,
      firstFrameVector_pureQuaternion]
  have hm : ‖f.val.2 - g.val.2‖ =
      ‖quaternionConjugate q secondQuaternionUnit - quaternionConjugate p secondQuaternionUnit‖ := by
    change ‖secondFrameVector v.val - secondFrameVector w.val‖ = _
    rw [← norm_pureQuaternion, pureQuaternion_sub, secondFrameVector_pureQuaternion,
      secondFrameVector_pureQuaternion]
  have hqclose : ‖q - p‖ ≤ 1 / 2 := hdist ▸ hclose
  have hnclose : ‖f.val.1 - g.val.1‖ ≤ 1 := by
    rw [hn]
    exact (norm_sub_conjugate_le hq hp norm_firstQuaternionUnit).trans (by linarith only [hqclose])
  have hmclose : ‖f.val.2 - g.val.2‖ ≤ 1 := by
    rw [hm]
    exact (norm_sub_conjugate_le hq hp norm_secondQuaternionUnit).trans (by linarith only [hqclose])
  have hframe : ‖q - p‖ ≤ ‖f.val.1 - g.val.1‖ + ‖f.val.2 - g.val.2‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).mp
    have h := normSq_sub_le_sum_director_sq hq hp hqclose
    rw [← hn, ← hm] at h
    nlinarith only [h, mul_nonneg (norm_nonneg (f.val.1 - g.val.1)) (norm_nonneg (f.val.2 - g.val.2))]
  have hFn := norm_sub_le_projector_sub f.property.1 g.property.1 hnclose
  have hFm := norm_sub_le_projector_sub f.property.2.1 g.property.2.1 hmclose
  obtain ⟨hPn, hPm⟩ := norms_projector_sub_le a f g
  have hFdist : ‖((vacuumFrameProjection a f).val : Tensor) -
      ((vacuumFrameProjection a g).val : Tensor)‖ = dist (cover a v) (cover a w) := by
    rw [cover_eq_quaternionFrameProjection, cover_eq_quaternionFrameProjection, dist_eq_norm]
    rfl
  change ‖directorProjector f.val.1 - directorProjector g.val.1‖ ≤ C * _ at hPn
  change ‖directorProjector f.val.2 - directorProjector g.val.2‖ ≤ C * _ at hPm
  rw [hFdist] at hPn hPm
  calc
    _ = ‖q - p‖ := hdist
    _ ≤ _ := hframe
    _ ≤ C * dist (cover a v) (cover a w) + C * dist (cover a v) (cover a w) :=
      add_le_add (hFn.trans hPn) (hFm.trans hPm)
    _ = _ := by
      dsimp only [C, r]
      field_simp [(vacuumRadius_pos a).ne']
      ring

/-- A continuous lift is absolutely continuous when its projection is. -/
theorem cover_lift_absolutelyContinuous (a : BulkCoefficients)
    {v : ℝ → Sphere3} {Q : ℝ → Tensor} {s t : ℝ}
    (hv : ContinuousOn v (uIcc s t)) (hQ : AbsolutelyContinuousOnInterval Q s t)
    (hcover : EqOn (fun x => (cover a (v x) : Tensor)) Q (uIcc s t)) :
    AbsolutelyContinuousOnInterval
      (fun x => Quaternion.linearIsometryEquivTuple.symm (v x).val) s t := by
  let C := (2 * Real.sqrt 2 + 1) / vacuumRadius a
  have hC : 0 ≤ C := div_nonneg (by positivity) (vacuumRadius_pos a).le
  have hd (x y : ℝ) : dist (Quaternion.linearIsometryEquivTuple.symm (v x).val)
      (Quaternion.linearIsometryEquivTuple.symm (v y).val) = dist (v x) (v y) := by
    rw [Quaternion.linearIsometryEquivTuple.symm.dist_map]
    rfl
  have hUC := isCompact_uIcc.uniformContinuousOn_of_continuous hv
  obtain ⟨η, hη, hnear⟩ := Metric.uniformContinuousOn_iff.mp hUC (1 / 2) (by positivity)
  rw [absolutelyContinuousOnInterval_iff] at hQ ⊢
  intro ε hε
  have hC1 : 0 < C + 1 := by positivity
  obtain ⟨δ, hδ, hQsmall⟩ := hQ (ε / (C + 1)) (div_pos hε hC1)
  refine ⟨min δ η, lt_min hδ hη, fun E hE hsum => ?_⟩
  have hQsum := hQsmall E hE (hsum.trans_le (min_le_left _ _))
  calc
    _ = ∑ i ∈ Finset.range E.1, dist (v (E.2 i).1) (v (E.2 i).2) := by
      apply Finset.sum_congr rfl
      intro i _
      exact hd _ _
    _ ≤ ∑ i ∈ Finset.range E.1, (C + 1) * dist (Q (E.2 i).1) (Q (E.2 i).2) := by
      apply Finset.sum_le_sum
      intro i hi
      obtain ⟨hx, hy⟩ := hE.1 i hi
      have hsingle : dist (E.2 i).1 (E.2 i).2 ≤
          ∑ j ∈ Finset.range E.1, dist (E.2 j).1 (E.2 j).2 :=
        Finset.single_le_sum (f := fun j => dist (E.2 j).1 (E.2 j).2)
          (fun _ _ => dist_nonneg) hi
      have hclose := hnear _ hx _ hy (hsingle.trans_lt (hsum.trans_le (min_le_right _ _)))
      have h := cover_dist_le_uniform a (v (E.2 i).1) (v (E.2 i).2) hclose.le
      have hEq : dist (cover a (v (E.2 i).1)) (cover a (v (E.2 i).2)) =
          dist (Q (E.2 i).1) (Q (E.2 i).2) := by
        change dist ((cover a (v (E.2 i).1)) : Tensor) ((cover a (v (E.2 i).2)) : Tensor) = _
        exact congrArg₂ dist (hcover hx) (hcover hy)
      rw [hEq] at h
      exact h.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) dist_nonneg)
    _ < ε := by
      rw [← Finset.mul_sum]
      exact (lt_div_iff₀' hC1).mp hQsum

/-- The actual vacuum covering lifts a one-dimensional Sobolev trace with the differential bound. -/
theorem cover_lift_sobolev (a : BulkCoefficients)
    {v : ℝ → Sphere3} {Q : ℝ → Tensor} {s t : ℝ} (hst : s < t)
    (hv : ContinuousOn v (Icc s t)) (hQ : AbsolutelyContinuousOnInterval Q s t)
    (hQd : MemLp (deriv Q) 2 (volume.restrict (Ioo s t)))
    (hcover : EqOn (fun x => (cover a (v x) : Tensor)) Q (Icc s t)) :
    let q (x : ℝ) := Quaternion.linearIsometryEquivTuple.symm (v x).val
    AbsolutelyContinuousOnInterval q s t ∧ MemLp (deriv q) 2 (volume.restrict (Ioo s t)) ∧
      ∀ᵐ x ∂volume.restrict (Ioo s t), 8 * vacuumRadius a ^ 2 * ‖deriv q x‖ ^ 2 ≤ ‖deriv Q x‖ ^ 2 := by
  intro q
  have hqAC : AbsolutelyContinuousOnInterval q s t :=
    cover_lift_absolutelyContinuous a (by rwa [uIcc_of_le hst.le]) hQ (by rwa [uIcc_of_le hst.le])
  have hderiv : ∀ᵐ x ∂volume.restrict (Ioo s t),
      8 * vacuumRadius a ^ 2 * ‖deriv q x‖ ^ 2 ≤ ‖deriv Q x‖ ^ 2 := by
    apply (ae_restrict_iff' measurableSet_Ioo).2
    filter_upwards [ae_differentiableAt_quaternion_of_ac hqAC] with x hx hxmem
    have hmem : x ∈ uIcc s t := by
      rw [uIcc_of_le hst.le]
      exact Ioo_subset_Icc_self hxmem
    have hIcc : ∀ᶠ y in 𝓝 x, y ∈ Icc s t := Icc_mem_nhds hxmem.1 hxmem.2
    have heq : (fun y => (cover a (v y) : Tensor)) =ᶠ[𝓝 x] Q := hIcc.mono fun _ hy => hcover hy
    have hm := cover_curve_metric_ge a v (hx hmem).hasDerivAt
    have hn : ‖deriv (fun y => (cover a (v y) : Tensor)) x‖ ^ 2 = ‖deriv Q x‖ ^ 2 :=
      congrArg (fun D : Tensor => ‖D‖ ^ 2) heq.deriv_eq
    calc
      _ = 2 * (4 * vacuumRadius a ^ 2 * ‖deriv q x‖ ^ 2) := by ring
      _ ≤ 2 * ((1 / 2 : ℝ) * ‖deriv (fun y => (cover a (v y) : Tensor)) x‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hm (by norm_num)
      _ = ‖deriv (fun y => (cover a (v y) : Tensor)) x‖ ^ 2 := by ring
      _ = _ := hn
  refine ⟨hqAC, ?_, hderiv⟩
  have hr : 0 < vacuumRadius a := vacuumRadius_pos a
  have hk : 0 < 2 * vacuumRadius a := by positivity
  refine (hQd.norm.const_mul (2 * vacuumRadius a)⁻¹).of_le
    (aestronglyMeasurable_deriv q _) ?_
  filter_upwards [hderiv] with x hx
  rw [Real.norm_of_nonneg (mul_nonneg (inv_nonneg.mpr hk.le) (norm_nonneg _))]
  apply (mul_le_mul_iff_right₀ hk).mp
  rw [← mul_assoc, mul_inv_cancel₀ hk.ne', one_mul]
  apply (sq_le_sq₀ (mul_nonneg hk.le (norm_nonneg _)) (norm_nonneg _)).mp
  nlinarith only [hx, mul_nonneg (sq_nonneg (vacuumRadius a)) (sq_nonneg ‖deriv q x‖)]

/-- The affine parameter from `[0,T]` to `[0,1]`, clamped outside the interval. -/
def vacuumLoopParameter (T x : ℝ) : unitInterval :=
  projIcc 0 1 zero_le_one (x / T)

private theorem continuous_vacuumLoopParameter (T : ℝ) : Continuous (vacuumLoopParameter T) :=
  continuous_projIcc.comp (continuous_id.div_const T)

private theorem vacuumLoopParameter_zero (T : ℝ) : vacuumLoopParameter T 0 = 0 := by
  simp [vacuumLoopParameter]

private theorem vacuumLoopParameter_end {T : ℝ} (hT : 0 < T) : vacuumLoopParameter T T = 1 := by
  simp [vacuumLoopParameter, hT.ne']

/-- A vacuum loop on the parameter interval `[0,T]`, extended constantly at the two ends. -/
def vacuumLoopTensor {a : BulkCoefficients} {A : vacuum a} (γ : Path A A) (T : ℝ) : ℝ → Tensor :=
  fun x => ((γ (vacuumLoopParameter T x)).val : Tensor)

theorem continuous_vacuumLoopTensor {a : BulkCoefficients} {A : vacuum a} (γ : Path A A) (T : ℝ) :
    Continuous (vacuumLoopTensor γ T) :=
  (symmetricTraceless.subtypeL.continuous.comp continuous_subtype_val).comp
    (γ.continuous.comp (continuous_vacuumLoopParameter T))

/-- A continuous loop with square-integrable weak data is its absolutely continuous representative. -/
theorem vacuumLoop_sobolev_of_weakDerivative {a : BulkCoefficients} {A : vacuum a}
    (γ : Path A A) {T : ℝ} (hT : 0 < T) {G : ℝ → Tensor}
    (hγ : MemLp (vacuumLoopTensor γ T) 2 (volume.restrict (Ioo 0 T)))
    (hG : MemLp G 2 (volume.restrict (Ioo 0 T)))
    (hweak : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ioo 0 T →
      (∫ x in Ioo 0 T, deriv φ x • vacuumLoopTensor γ T x) =
        -(∫ x in Ioo 0 T, φ x • G x)) :
    AbsolutelyContinuousOnInterval (vacuumLoopTensor γ T) 0 T ∧
      MemLp (deriv (vacuumLoopTensor γ T)) 2 (volume.restrict (Ioo 0 T)) ∧
      deriv (vacuumLoopTensor γ T) =ᵐ[volume.restrict (Ioo 0 T)] G := by
  let Q := vacuumLoopTensor γ T
  obtain ⟨F, hFAC, hFae, hFinc⟩ :=
    StratificationTheory.banach_interval_weakDerivative_exists_ac_representative hT hγ hG hweak
  have hEq : EqOn F Q (Icc 0 T) := by
    letI : TopologicalSpace Tensor := (inferInstance : PseudoMetricSpace Tensor).toUniformSpace.toTopologicalSpace
    have hFcont : ContinuousOn F (Icc 0 T) := by
      simpa only [uIcc_of_le hT.le] using hFAC.continuousOn
    have hI : Isometry ((↑) : S0 → Tensor) := fun _ _ => rfl
    have hQcont : Continuous Q :=
      (hI.continuous.comp continuous_subtype_val).comp (γ.continuous.comp (continuous_vacuumLoopParameter T))
    have hFae' : F =ᵐ[volume.restrict (Icc 0 T)] Q := by rwa [← restrict_Ioo_eq_restrict_Icc]
    exact Measure.eqOn_Icc_of_ae_eq volume hT.ne hFae' hFcont hQcont.continuousOn
  have hAC : AbsolutelyContinuousOnInterval Q 0 T := by
    rw [absolutelyContinuousOnInterval_iff] at hFAC ⊢
    intro ε hε
    obtain ⟨δ, hδ, hsum⟩ := hFAC ε hε
    refine ⟨δ, hδ, fun E hE hsmall => ?_⟩
    refine (lt_of_eq_of_lt ?_ (hsum E hE hsmall))
    apply Finset.sum_congr rfl
    intro i hi
    have hpair := hE.1 i hi
    rw [uIcc_of_le hT.le] at hpair
    exact congrArg₂ dist (hEq hpair.1).symm (hEq hpair.2).symm
  have hDeriv : deriv Q =ᵐ[volume.restrict (Ioo 0 T)] G := by
    apply (ae_restrict_iff' measurableSet_Ioo).2
    have hgInt := StratificationTheory.intervalIntegrable_of_memLp_two hT.le hG
    filter_upwards [hgInt.ae_hasDerivAt_integral] with x hx hxmem
    have hx' : x ∈ uIcc 0 T := by
      rw [uIcc_of_le hT.le]
      exact Ioo_subset_Icc_self hxmem
    have hIcc : ∀ᶠ y in 𝓝 x, y ∈ Icc 0 T := Icc_mem_nhds hxmem.1 hxmem.2
    have hevent : Q =ᶠ[𝓝 x] fun y => F 0 + ∫ u in 0..y, G u := by
      filter_upwards [hIcc] with y hy
      calc
        _ = F y := (hEq hy).symm
        _ = _ := by
          exact (sub_eq_iff_eq_add.mp (hFinc 0 (left_mem_Icc.mpr hT.le) y hy)).trans (add_comm _ _)
    exact (((hx hx' 0 left_mem_uIcc).const_add (F 0)).congr_of_eventuallyEq hevent).deriv
  exact ⟨hAC, (memLp_congr_ae hDeriv).2 hG, hDeriv⟩

/-- The continuous covering lift of a Sobolev vacuum loop is a Sobolev quaternion curve
with the original monodromy and the pointwise energy bound. -/
theorem vacuumLoop_exists_sobolev_lift (a : BulkCoefficients) (v₀ : Sphere3)
    (γ : Path (vacuumQuaternionProjection a v₀) (vacuumQuaternionProjection a v₀))
    {T : ℝ} (hT : 0 < T) (hγ : AbsolutelyContinuousOnInterval (vacuumLoopTensor γ T) 0 T)
    (hDγ : MemLp (deriv (vacuumLoopTensor γ T)) 2 (volume.restrict (Ioo 0 T))) :
    ∃ v : ℝ → Sphere3, Continuous v ∧ v 0 = v₀ ∧
      (fun x => (cover a (v x) : Tensor)) = vacuumLoopTensor γ T ∧
      let q (x : ℝ) := Quaternion.linearIsometryEquivTuple.symm (v x).val
      q T = q 0 * quaternionWordReal (vacuumFundamentalGroupEquiv a v₀
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ))) ∧
      AbsolutelyContinuousOnInterval q 0 T ∧ MemLp (deriv q) 2 (volume.restrict (Ioo 0 T)) ∧
      ∀ᵐ x ∂volume.restrict (Ioo 0 T),
        8 * vacuumRadius a ^ 2 * ‖deriv q x‖ ^ 2 ≤ ‖deriv (vacuumLoopTensor γ T) x‖ ^ 2 := by
  obtain ⟨Γ, hzero, hproj, hend⟩ := vacuumLoop_exists_lift a v₀ γ
  let v : ℝ → Sphere3 := Γ ∘ vacuumLoopParameter T
  have hv : Continuous v := Γ.continuous.comp (continuous_vacuumLoopParameter T)
  have hv₀ : v 0 = v₀ := by
    change Γ (vacuumLoopParameter T 0) = v₀
    rw [vacuumLoopParameter_zero, hzero]
  have hcover : (fun x => (cover a (v x) : Tensor)) = vacuumLoopTensor γ T := by
    funext x
    have h := congrArg (fun A : vacuum a => (A.val : Tensor)) (hproj (vacuumLoopParameter T x))
    change ((vacuumQuaternionProjection a (v x)).val : Tensor) = vacuumLoopTensor γ T x at h
    rwa [vacuumQuaternionProjection_val] at h
  refine ⟨v, hv, hv₀, hcover, ?_, ?_⟩
  · change Quaternion.linearIsometryEquivTuple.symm (Γ (vacuumLoopParameter T T)).val =
      Quaternion.linearIsometryEquivTuple.symm (v 0).val * _
    rw [vacuumLoopParameter_end hT, hv₀]
    exact hend
  · exact cover_lift_sobolev a hT hv.continuousOn hγ hDγ (fun x _ => congrFun hcover x)

/-- The Sobolev lift of a null-class vacuum loop closes and retains its energy estimate. -/
theorem vacuumLoop_exists_closed_sobolev_lift (a : BulkCoefficients) (v₀ : Sphere3)
    (γ : Path (vacuumQuaternionProjection a v₀) (vacuumQuaternionProjection a v₀))
    {T : ℝ} (hT : 0 < T) (hγ : AbsolutelyContinuousOnInterval (vacuumLoopTensor γ T) 0 T)
    (hDγ : MemLp (deriv (vacuumLoopTensor γ T)) 2 (volume.restrict (Ioo 0 T)))
    (htriv : FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ) = 1) :
    ∃ v : ℝ → Sphere3, Continuous v ∧ v 0 = v₀ ∧ v T = v₀ ∧
      (fun x => (cover a (v x) : Tensor)) = vacuumLoopTensor γ T ∧
      let q (x : ℝ) := Quaternion.linearIsometryEquivTuple.symm (v x).val
      AbsolutelyContinuousOnInterval q 0 T ∧ MemLp (deriv q) 2 (volume.restrict (Ioo 0 T)) ∧
      ∀ᵐ x ∂volume.restrict (Ioo 0 T),
        8 * vacuumRadius a ^ 2 * ‖deriv q x‖ ^ 2 ≤ ‖deriv (vacuumLoopTensor γ T) x‖ ^ 2 := by
  obtain ⟨v, hv, hz, hcover, hend, hSob⟩ := vacuumLoop_exists_sobolev_lift a v₀ γ hT hγ hDγ
  have heq : v T = v₀ := by
    apply Subtype.ext
    apply Quaternion.linearIsometryEquivTuple.symm.injective
    simpa only [htriv, map_one, mul_one, hz] using hend
  exact ⟨v, hv, hz, heq, hcover, hSob⟩

theorem intervalIntegrable_sq_norm_of_memLp_two {E : Type*} [NormedAddCommGroup E]
    {G : ℝ → E} {a b : ℝ} (hab : a ≤ b) (h : MemLp G 2 (volume.restrict (Ioo a b))) :
    IntervalIntegrable (fun s => ‖G s‖ ^ 2) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hab]
  exact h.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)

private theorem isLightQuaternion_inv {g : QuaternionGroup 2} (h : IsLightQuaternion g) :
    IsLightQuaternion g⁻¹ := by
  rcases h with rfl | rfl | rfl | rfl <;> decide

/-- A vacuum loop of either light quaternion class has energy at least `kappaStar a`. -/
theorem vacuumLoop_energy_ge_light (a : BulkCoefficients) (v₀ : Sphere3)
    (γ : Path (vacuumQuaternionProjection a v₀) (vacuumQuaternionProjection a v₀))
    (hγ : AbsolutelyContinuousOnInterval (vacuumLoopTensor γ (2 * Real.pi)) 0 (2 * Real.pi))
    (hDγ : MemLp (deriv (vacuumLoopTensor γ (2 * Real.pi))) 2 (volume.restrict (Ioo 0 (2 * Real.pi))))
    (hlight : IsLightQuaternion (vacuumFundamentalGroupEquiv a v₀
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)))) :
    kappaStar a ≤ ∫ x in 0..(2 * Real.pi), (1 / 2 : ℝ) * ‖deriv (vacuumLoopTensor γ (2 * Real.pi)) x‖ ^ 2 := by
  let g := vacuumFundamentalGroupEquiv a v₀ (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ))
  have hT : 0 < 2 * Real.pi := by positivity
  obtain ⟨v, _, hv₀, hQ, hvT, hvAC, hDq, _⟩ := vacuumLoop_exists_sobolev_lift a v₀ γ hT hγ hDγ
  have hend : v (2 * Real.pi) = g⁻¹ • v 0 := by
    apply Subtype.ext
    apply Quaternion.linearIsometryEquivTuple.symm.injective
    rw [quaternionTuple_symm_smul, inv_inv]
    exact hvT
  have hV : IntervalIntegrable
      (fun x => (1 / 2 : ℝ) * ‖deriv (fun y => (cover a (v y) : Tensor)) x‖ ^ 2)
      volume 0 (2 * Real.pi) := by
    rw [hQ]
    exact (intervalIntegrable_sq_norm_of_memLp_two hT.le hDγ).const_mul (1 / 2)
  have h := cover_curve_energy_ge_light a v (isLightQuaternion_inv hlight) hend hvAC
    (StratificationTheory.intervalIntegrable_of_memLp_two hT.le hDq.norm)
    (intervalIntegrable_sq_norm_of_memLp_two hT.le hDq) hV
  rwa [hQ] at h

/-- A loop with the central quaternion class has energy at least four times `kappaStar a`. -/
theorem vacuumLoop_energy_ge_antipodal (a : BulkCoefficients) (v₀ : Sphere3)
    (γ : Path (vacuumQuaternionProjection a v₀) (vacuumQuaternionProjection a v₀))
    (hγ : AbsolutelyContinuousOnInterval (vacuumLoopTensor γ (2 * Real.pi)) 0 (2 * Real.pi))
    (hDγ : MemLp (deriv (vacuumLoopTensor γ (2 * Real.pi))) 2 (volume.restrict (Ioo 0 (2 * Real.pi))))
    (hclass : vacuumFundamentalGroupEquiv a v₀
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)) = QuaternionGroup.a 2) :
    4 * kappaStar a ≤ ∫ x in 0..(2 * Real.pi), (1 / 2 : ℝ) * ‖deriv (vacuumLoopTensor γ (2 * Real.pi)) x‖ ^ 2 := by
  have hT : 0 < 2 * Real.pi := by positivity
  obtain ⟨v, _, hv₀, hQ, hvT, hvAC, hDq, _⟩ := vacuumLoop_exists_sobolev_lift a v₀ γ hT hγ hDγ
  have hinv : (QuaternionGroup.a 2 : QuaternionGroup 2)⁻¹ = QuaternionGroup.a 2 := by decide
  have hend : v (2 * Real.pi) = (QuaternionGroup.a 2 : QuaternionGroup 2) • v 0 := by
    apply Subtype.ext
    apply Quaternion.linearIsometryEquivTuple.symm.injective
    rw [quaternionTuple_symm_smul, hinv]
    simpa only [hclass] using hvT
  have hV : IntervalIntegrable
      (fun x => (1 / 2 : ℝ) * ‖deriv (fun y => (cover a (v y) : Tensor)) x‖ ^ 2)
      volume 0 (2 * Real.pi) := by
    rw [hQ]
    exact (intervalIntegrable_sq_norm_of_memLp_two hT.le hDγ).const_mul (1 / 2)
  have h := cover_curve_energy_ge_antipodal a v hend hvAC
    (StratificationTheory.intervalIntegrable_of_memLp_two hT.le hDq.norm)
    (intervalIntegrable_sq_norm_of_memLp_two hT.le hDq) hV
  rwa [hQ] at h

end Thesis
