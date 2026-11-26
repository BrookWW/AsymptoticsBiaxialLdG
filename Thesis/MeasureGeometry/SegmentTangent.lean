module

public import Thesis.Definitions
import Thesis.MeasureGeometry.LineDensity
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-! The actual approximate tangent along an interior straight segment. -/

public section

noncomputable section

open Filter MeasureTheory Metric Set
open scoped ENNReal NNReal Matrix Topology RealInnerProductSpace

namespace Thesis.MeasureGeometry

/-- A segment contained in the support fixes the approximate tangent at
every point of its open segment where a tangent is given. -/
theorem matrixAction_eq_of_approxTangent_openSegment {S : Set Point} {p q z : Point}
    (hpq : p ≠ q) (hS : segment ℝ p q ⊆ S) (hz : z ∈ openSegment ℝ p q)
    {P : LineProjection} (hP : IsApproxTangentLine S z P) :
    matrixAction P.val (q - p) = q - p := by
  let d := q - p
  let A : Point →ₗ[ℝ] Point := (1 - P.val).toEuclideanLin
  have hAd : A d = 0 := by
    by_contra hn
    let R := ‖d‖
    have hR : 0 < R := norm_pos_iff.2 (sub_ne_zero.2 hpq.symm)
    have hTwo : 0 < 2 * R := mul_pos (by norm_num) hR
    have hFour : 0 < 4 * R := mul_pos (by norm_num) hR
    let δ := ‖A d‖ / (2 * R)
    have hδ : 0 < δ := div_pos (norm_pos_iff.2 hn) (mul_pos (by norm_num) hR)
    have hδlt : δ * R < ‖A d‖ := by
      have hN : 0 < ‖A d‖ := norm_pos_iff.2 hn
      change (‖A d‖ / (2 * R)) * R < _
      rw [div_mul_eq_mul_div, mul_div_mul_right _ _ hR.ne']
      linarith only [hN]
    rw [openSegment_eq_image' ℝ p q] at hz
    obtain ⟨t, ht, htz⟩ := hz
    let F : ℝ →ᵃ[ℝ] Point := AffineMap.lineMap z (z + d)
    let M (r : ℝ) := (F : ℝ → Point) '' Icc (r / (4 * R)) (r / (2 * R))
    let C (r : ℝ) := (S ∩ ball z r) \ {y : Point | ‖matrixAction (1 - P.val) (y - z)‖ ≤ δ * ‖y - z‖}
    have hMini (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) (2 * R * (1 - t))) (y : Point) (hy : y ∈ M r) :
        y ∈ C r := by
      obtain ⟨s, hs, hsy⟩ := hy
      subst y
      have hs₀ : 0 < s := (div_pos hr.1 hFour).trans_le hs.1
      have hF : F s = z + s • d := by
        change AffineMap.lineMap z (z + d) s = _
        rw [AffineMap.lineMap_apply_module', add_sub_cancel_left, add_comm]
      have hsd : ‖s • d‖ = s * R := by rw [norm_smul, Real.norm_of_nonneg hs₀.le]
      have hHalf := (le_div_iff₀ hTwo).1 hs.2
      have hMemS : F s ∈ S := by
        apply hS
        rw [segment_eq_image']
        refine ⟨t + s, ⟨by linarith only [ht.1, hs₀], ?_⟩, ?_⟩
        · have hR' : r / (2 * R) < 1 - t := (div_lt_iff₀ hTwo).2
              (by simpa only [mul_comm (1 - t) (2 * R)] using hr.2)
          have htS : s < 1 - t := hs.2.trans_lt hR'
          linarith only [htS]
        · change p + (t + s) • d = _
          rw [hF, ← htz, add_smul, add_assoc]
      have hB : F s ∈ ball z r := by
        rw [hF, mem_ball, dist_eq_norm, add_sub_cancel_left, hsd]
        linarith only [hHalf, hr.1]
      have hOut : δ * ‖F s - z‖ < ‖matrixAction (1 - P.val) (F s - z)‖ := by
        rw [hF, add_sub_cancel_left, hsd]
        change δ * (s * R) < ‖A (s • d)‖
        rw [map_smul, norm_smul, Real.norm_of_nonneg hs₀.le]
        calc
          _ = s * (δ * R) := by ring
          _ < _ := mul_lt_mul_of_pos_left hδlt hs₀
      exact ⟨⟨hMemS, hB⟩, hOut.not_ge⟩
    have hMass (r : ℝ) : HausdorffOne (M r) = ENNReal.ofReal (r / 4) := by
      have hEq : (nndist z (z + d) : ℝ) = R := by
        change dist z (z + d) = _
        rw [dist_comm, dist_eq_norm, add_sub_cancel_left]
      change HausdorffOne ((AffineMap.lineMap z (z + d) : ℝ → Point) '' Icc (r / (4 * R)) (r / (2 * R))) = _
      rw [hausdorffMeasure_lineMap_image, hausdorffMeasure_real, Real.volume_Icc]
      change (nndist z (z + d) : ℝ≥0∞) * ENNReal.ofReal (r / (2 * R) - r / (4 * R)) = _
      rw [← ENNReal.ofReal_coe_nnreal,
        hEq, ← ENNReal.ofReal_mul hR.le]
      congr 1
      field_simp
      ring
    have hsmall : 0 < 2 * R * (1 - t) := mul_pos (mul_pos (by norm_num) hR) (sub_pos.2 ht.2)
    have hLower : ∀ᶠ r : ℝ in 𝓝[>] 0, ENNReal.ofReal (1 / 8) ≤ HausdorffOne (C r) / ENNReal.ofReal (2 * r) := by
      filter_upwards [eventually_mem_positive_interval hsmall] with r hr
      calc
        _ = ENNReal.ofReal (r / 4) / ENNReal.ofReal (2 * r) := by
          rw [← ENNReal.ofReal_div_of_pos (mul_pos (show 0 < (2 : ℝ) by norm_num) hr.1)]
          congr 1
          field_simp [hr.1.ne']
          norm_num
        _ ≤ _ := ENNReal.div_le_div_right ((hMass r).symm.le.trans (measure_mono (fun y => hMini r hr y))) _
    exact (ENNReal.ofReal_pos.mpr (show (0 : ℝ) < 1 / 8 by norm_num)).not_ge
      (le_of_tendsto_of_tendsto tendsto_const_nhds (hP.2 δ hδ) hLower)
  change (1 - P.val).toEuclideanLin d = 0 at hAd
  change P.val.toEuclideanLin d = d
  have hM : (1 - P.val).toEuclideanLin = (1 : Tensor).toEuclideanLin - P.val.toEuclideanLin :=
    map_sub Matrix.toEuclideanLin _ _
  rw [hM, LinearMap.sub_apply, Matrix.toEuclideanLin_eq_toLin_orthonormal,
    Matrix.toLin_one, LinearMap.id_apply] at hAd
  exact (sub_eq_zero.mp hAd).symm

/-- A unit vector fixed by a symmetric rank-one matrix determines every
entry of the associated projection. -/
theorem lineProjection_entries_of_fixed_unit (P : LineProjection) {v : Point}
    (hv : ‖v‖ = 1) (hPv : matrixAction P.val v = v) :
    ∀ i j : Fin 3, P.val i j = v i * v j := by
  let T : Point →ₗ[ℝ] Point := P.val.toEuclideanLin
  let L := Submodule.span ℝ ({v} : Set Point)
  have hv₀ : v ≠ 0 := by
    intro h
    rw [h, norm_zero] at hv
    exact zero_ne_one hv
  have hRank : Module.finrank ℝ (LinearMap.range T) = 1 := by
    change Module.finrank ℝ (LinearMap.range P.val.toEuclideanLin) = 1
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, ← Matrix.rank_eq_finrank_range_toLin]
    exact P.property.2.2
  have hL : Module.finrank ℝ L = 1 := finrank_span_singleton hv₀
  have hLe : L ≤ LinearMap.range T := by
    apply Submodule.span_le.2
    rw [singleton_subset_iff]
    exact ⟨v, hPv⟩
  have hRange := Submodule.eq_of_le_of_finrank_le hLe (by rw [hL, hRank])
  have hSymm : T.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    ((Matrix.conjTranspose_eq_transpose_of_trivial P.val).trans P.property.1)
  have hTv (u : Point) : T u = inner ℝ v u • v := by
    have hu : T u ∈ L := hRange.symm ▸ (LinearMap.mem_range_self T u)
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hu
    have hI : inner ℝ v (T u) = inner ℝ v u := by
      rw [← hSymm v u]
      exact congrArg (fun x => inner ℝ x u) hPv
    have hcEq : inner ℝ v (c • v) = c := by
      rw [real_inner_smul_right, real_inner_self_eq_norm_sq, hv]
      ring
    rw [hc] at hcEq
    exact hc.symm.trans (congrArg (· • v) (hcEq.symm.trans hI))
  intro i j
  have h := congrArg (fun x : Point => x i) (hTv (axis j))
  change ((P.val.mulVec (fun k => (axis j) k)) i) = _ at h
  rw [axis, Matrix.mulVec, dotProduct] at h
  simp only [PiLp.smul_apply, smul_eq_mul, EuclideanSpace.inner_single_right, RCLike.conj_to_real, one_mul] at h
  have hLhs : (∑ k : Fin 3, P.val i k * EuclideanSpace.single j (1 : ℝ) k) = P.val i j := by
    classical
    rw [Finset.sum_eq_single j]
    · simp
    · intro k _ hk
      simp [hk]
    · exact fun h => (h (Finset.mem_univ j)).elim
  rw [hLhs] at h
  exact h.trans (mul_comm _ _)

end Thesis.MeasureGeometry
