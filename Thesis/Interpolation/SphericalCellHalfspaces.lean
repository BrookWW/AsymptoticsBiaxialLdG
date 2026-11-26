module

public import Thesis.Interpolation.SphericalCellGeometry

/-! The actual lateral side of a spherical cell is locally a linear interface. -/

public section

open Metric Set

namespace Thesis

/-- Arrange a fixed side coordinate and its free tangential coordinate in
the original order of the square. -/
@[expose] def shellSquareSideParameters (i : Fin 2) (fixed free : ℝ) : ℝ × ℝ :=
  if i = 0 then (fixed, free) else (free, fixed)

private theorem square_normal_nonzero {c : Point} {h : ℝ} {m : ℕ}
    (hc : ∀ i : Fin 3, c i ∈ Icc (0 : ℝ) (1 / 32))
    (hm : (m : ℝ) * h ∈ Icc (1 / 8 : ℝ) (1 / 4))
    {f : TensorGridSquare} (hf : f ∈ cubeBoundarySquares m) :
    ∃ j : Fin 3, j ≠ f.2.val.1 ∧ j ≠ f.2.val.2 ∧ tensorGridVertex c h f.1 j ≠ 0 := by
  obtain ⟨_, _, _, _, j, hj₁, hj₂, hs⟩ := mem_cubeBoundarySquares_iff.mp hf
  refine ⟨j, hj₁, hj₂, ?_⟩
  change c j + (f.1 j : ℝ) * h ≠ 0
  rcases eq_or_eq_neg_of_abs_eq hs with hp | hn
  · have he : (f.1 j : ℝ) = m := by exact_mod_cast hp
    rw [he]
    exact ne_of_gt (by linarith only [(hc j).1, hm.1])
  · have he : (f.1 j : ℝ) = -(m : ℝ) := by exact_mod_cast hn
    rw [he]
    exact ne_of_lt (by linarith only [(hc j).2, hm.1])

/-- At a relative interior point of a lateral side, the actual closed cell
and its interior are given locally by the same linear half-space. -/
theorem sphericalClosedCell_halfspace_near_side {c : Point} {h : ℝ} (hh : 0 < h) (hh' : h ≤ 1 / 2)
    {m : ℕ} (hc : ∀ i : Fin 3, c i ∈ Icc (0 : ℝ) (1 / 32))
    (hm : (m : ℝ) * h ∈ Icc (1 / 8 : ℝ) (1 / 4))
    {f : TensorGridSquare} (hf : f ∈ cubeBoundarySquares m) (i : Fin 2) (upper : Bool)
    {t r : ℝ} (ht : t ∈ Ioo (0 : ℝ) h) (hr : r ∈ Ioo (1 - h) 1) :
    let d := if upper then h else 0
    let p := (shellSquareSideParameters i d t, r)
    let y := sphericalCellPoint c h f p
    ∃ (L : Point →L[ℝ] ℝ) (N : Set Point), L ≠ 0 ∧ IsOpen N ∧ y ∈ N ∧ L y = 0 ∧
      (∀ z ∈ N, z ∈ sphericalClosedCell c h f ↔ 0 ≤ L z) ∧
      (∀ z ∈ N, z ∈ interior (sphericalClosedCell c h f) ↔ 0 < L z) ∧
      ∀ z ∈ N, L z = 0 → ∃ t r : ℝ, t ∈ Ioo 0 h ∧ r ∈ Ioo (1 - h) 1 ∧
        z = sphericalCellPoint c h f (shellSquareSideParameters i d t, r) := by
  intro d p y
  obtain ⟨j, hj₁, hj₂, hj₀⟩ := square_normal_nonzero hc hm hf
  obtain ⟨e, he, hBox, hCell, hImg, _, _⟩ := exists_sphericalCellOpenChart hh' hc hm hf
  let b := tensorGridVertex c h f.1
  let k : Fin 3 := if i = 0 then f.2.val.1 else f.2.val.2
  let s (q : SphericalCellParameter) : ℝ := if i = 0 then q.1.1 else q.1.2
  let u (q : SphericalCellParameter) : ℝ := if i = 0 then q.1.2 else q.1.1
  let A (q : SphericalCellParameter) : Point := tensorGridSquarePoint b f.2 q.1.1 q.1.2
  let L₀ : Point →L[ℝ] ℝ := EuclideanSpace.proj k - ((b k + d) / b j) • EuclideanSpace.proj j
  let L := if upper then -L₀ else L₀
  have hkj : k ≠ j := by
    dsimp only [k]
    split_ifs <;> exact Ne.symm (by assumption)
  have hL₁ : L₀ (EuclideanSpace.single k 1) = 1 := by
    change (EuclideanSpace.single k (1 : ℝ) : Point) k -
      ((b k + d) / b j) * (EuclideanSpace.single k (1 : ℝ) : Point) j = 1
    simp [hkj]
  have hL₀ : L ≠ 0 := by
    intro h
    have h' := congrArg (fun g : Point →L[ℝ] ℝ => g (EuclideanSpace.single k 1)) h
    cases upper <;> simp [L, hL₁] at h'
  have hAj (q : SphericalCellParameter) : A q j = b j := by
    simp [A, tensorGridSquarePoint, PiLp.add_apply, PiLp.smul_apply, hj₁, hj₂]
  have hAk (q : SphericalCellParameter) : A q k = b k + s q := by
    by_cases hi : i = 0
    · simp [A, tensorGridSquarePoint, PiLp.add_apply, PiLp.smul_apply, hi, k, s, f.2.property]
    · simp [A, tensorGridSquarePoint, PiLp.add_apply, PiLp.smul_apply, hi, k, s, Ne.symm f.2.property]
  have hs : Continuous s := by
    by_cases hi : i = 0 <;> simp [s, hi] <;> fun_prop
  have hu : Continuous u := by
    by_cases hi : i = 0 <;> simp [u, hi] <;> fun_prop
  let U : Set SphericalCellParameter := {q | u q ∈ Ioo (0 : ℝ) h} ∩
    {q | q.2 ∈ Ioo (1 - h) 1} ∩ {q | if upper then 0 < s q else s q < h}
  have hU : IsOpen U := by
    refine ((isOpen_Ioo.preimage hu).inter (isOpen_Ioo.preimage continuous_snd)).inter ?_
    cases upper
    · exact isOpen_lt hs continuous_const
    · exact isOpen_lt continuous_const hs
  let N := e.target ∩ e.symm ⁻¹' U
  have hN : IsOpen N := e.continuousOn_symm.isOpen_inter_preimage e.open_target hU
  have hBoxI (q : SphericalCellParameter) :
      q ∈ sphericalCellParameterBox h ↔ s q ∈ Icc 0 h ∧ u q ∈ Icc 0 h ∧ q.2 ∈ Icc (1 - h) 1 := by
    change ((q.1.1 ∈ Icc (0 : ℝ) h ∧ q.1.2 ∈ Icc (0 : ℝ) h) ∧ q.2 ∈ Icc (1 - h) 1) ↔ _
    by_cases hi : i = 0 <;> simp [s, u, hi, and_assoc, and_left_comm]
  have hIntI (q : SphericalCellParameter) :
      q ∈ interior (sphericalCellParameterBox h) ↔ s q ∈ Ioo 0 h ∧ u q ∈ Ioo 0 h ∧ q.2 ∈ Ioo (1 - h) 1 := by
    rw [sphericalCellParameterBox, interior_prod_eq, interior_prod_eq, interior_Icc, interior_Icc]
    by_cases hi : i = 0 <;> simp [s, u, hi, and_assoc, and_left_comm]
  have hsp : s p = d := by by_cases hi : i = 0 <;> simp [p, s, shellSquareSideParameters, hi]
  have hup : u p = t := by by_cases hi : i = 0 <;> simp [p, u, shellSquareSideParameters, hi]
  have hpBox : p ∈ sphericalCellParameterBox h := (hBoxI p).mpr
    ⟨by rw [hsp]; cases upper <;> simp [d, hh.le], hup ▸ Ioo_subset_Icc_self ht, Ioo_subset_Icc_self hr⟩
  have hY : e p = y := congrFun he p
  have hYp : e.symm y = p := by rw [← hY, e.left_inv (hBox hpBox)]
  have hyN : y ∈ N := by
    refine ⟨hY ▸ e.map_source (hBox hpBox), ?_⟩
    change e.symm y ∈ U
    rw [hYp]
    refine ⟨⟨?_, hr⟩, ?_⟩
    · change u p ∈ Ioo (0 : ℝ) h
      rwa [hup]
    · change if upper then 0 < s p else s p < h
      rw [hsp]
      cases upper <;> simp [d, hh]
  have hScale (z : Point) (hz : z ∈ N) :
      let q := e.symm z
      let scale := q.2 / ‖A q‖
      0 < scale ∧ L z = scale * (if upper then d - s q else s q - d) := by
    intro q scale
    have hR : q.2 ∈ Ioo (1 - h) 1 := hz.2.1.2
    have hA₀ : A q ≠ 0 := by
      intro h
      exact hj₀ ((hAj q).symm.trans (congrArg (fun z : Point => z j) h))
    have hScalePos : 0 < scale := div_pos (by linarith only [hR.1, hh']) (norm_pos_iff.mpr hA₀)
    have hZ : scale • A q = z := by
      have ht := e.right_inv hz.1
      rw [he] at ht
      change q.2 • NormedSpace.normalize (A q) = z at ht
      simpa only [NormedSpace.normalize, smul_smul, ← div_eq_mul_inv] using ht
    have hCoord (l : Fin 3) : z l = scale * A q l := by
      rw [← hZ, PiLp.smul_apply, smul_eq_mul]
    have hL : L₀ z = scale * (s q - d) := by
      change z k - (b k + d) / b j * z j = _
      rw [hCoord k, hCoord j, hAk, hAj]
      have hDiv : (b k + d) / b j * b j = b k + d := div_mul_cancel₀ _ hj₀
      rw [show (b k + d) / b j * (scale * b j) = scale * ((b k + d) / b j * b j) by ring, hDiv]
      ring
    refine ⟨hScalePos, ?_⟩
    cases upper
    · simp [L, hL]
    · simp [L, hL]
      ring
  have hYzero : L y = 0 := by
    rw [(hScale y hyN).2, hYp, hsp]
    cases upper <;> simp [d]
  refine ⟨L, N, hL₀, hN, hyN, hYzero, ?_, ?_, ?_⟩
  · intro z hz
    have hQ : e.symm z ∈ U := hz.2
    have hVal := (hImg.symm_apply_mem_iff hz.1).symm
    rw [hVal, hBoxI]
    obtain ⟨hPositive, hSign⟩ := hScale z hz
    rw [hSign, mul_nonneg_iff_of_pos_left hPositive]
    have hUo := hQ.1.1
    have hRo := hQ.1.2
    have hSide := hQ.2
    cases upper <;> simp only [Bool.false_eq_true, if_true, if_false, d, sub_nonneg] at *
    · exact ⟨fun h => h.1.1, fun h => ⟨⟨h, hSide.le⟩, Ioo_subset_Icc_self hUo, Ioo_subset_Icc_self hRo⟩⟩
    · exact ⟨fun h => h.1.2, fun h => ⟨⟨hSide.le, h⟩, Ioo_subset_Icc_self hUo, Ioo_subset_Icc_self hRo⟩⟩
  · intro z hz
    have hQ : e.symm z ∈ U := hz.2
    have hVal := (hImg.interior.symm_apply_mem_iff hz.1).symm
    rw [hVal, hIntI]
    obtain ⟨hPositive, hSign⟩ := hScale z hz
    rw [hSign, mul_pos_iff_of_pos_left hPositive]
    have hUo := hQ.1.1
    have hRo := hQ.1.2
    have hSide := hQ.2
    cases upper <;> simp only [Bool.false_eq_true, if_true, if_false, d, sub_pos] at *
    · exact ⟨fun h => h.1.1, fun h => ⟨⟨h, hSide⟩, hUo, hRo⟩⟩
    · exact ⟨fun h => h.1.2, fun h => ⟨⟨hSide, h⟩, hUo, hRo⟩⟩
  · intro z hz hZero
    let q := e.symm z
    have hQ : q ∈ U := hz.2
    have hT : u q ∈ Ioo (0 : ℝ) h := hQ.1.1
    have hR : q.2 ∈ Ioo (1 - h) 1 := hQ.1.2
    obtain ⟨hp, heq⟩ := hScale z hz
    have hMul : (q.2 / ‖A q‖) * (if upper then d - s q else s q - d) = 0 := heq.symm.trans hZero
    have hsEq : s q = d := by
      have hz' := (mul_eq_zero.mp hMul).resolve_left hp.ne'
      cases upper <;> simp at hz' <;> linarith only [hz']
    have hPoint : (shellSquareSideParameters i d (u q), q.2) = q := by
      apply Prod.ext
      · apply Prod.ext
        · by_cases hi : i = 0
          · simpa [shellSquareSideParameters, hi, s] using hsEq.symm
          · simp [shellSquareSideParameters, u, hi]
        · by_cases hi : i = 0
          · simp [shellSquareSideParameters, u, hi]
          · simpa [shellSquareSideParameters, hi, s] using hsEq.symm
      · rfl
    refine ⟨u q, q.2, hT, hR, ?_⟩
    rw [hPoint, ← he]
    exact (e.right_inv hz.1).symm

/-- An open neighborhood contains a positive step in every prescribed direction. -/
theorem exists_positive_step_mem_open {N : Set Point} (hN : IsOpen N) {y : Point} (hy : y ∈ N) (z : Point) :
    ∃ t : ℝ, 0 < t ∧ y + t • z ∈ N := by
  let F : ℝ → Point := fun t => y + t • z
  have hF : Continuous F := continuous_const.add (continuous_id.smul continuous_const)
  have h₀ : (0 : ℝ) ∈ F ⁻¹' N := by simpa [F] using hy
  obtain ⟨ε, hε, hBall⟩ := Metric.isOpen_iff.mp (hN.preimage hF) 0 h₀
  refine ⟨ε / 2, half_pos hε, hBall ?_⟩
  rw [mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg (half_pos hε).le]
  linarith only [hε]

/-- A nonzero real linear form has a strictly positive value. -/
theorem exists_pos_of_ne_zero_planeForm (L : Point →L[ℝ] ℝ) (hL : L ≠ 0) : ∃ z, 0 < L z := by
  have h := not_forall.mp (show ¬ ∀ z : Point, L z = 0 by
    intro h
    apply hL
    ext z
    rw [h, zero_apply])
  obtain ⟨z, hz⟩ := h
  rcases lt_or_gt_of_ne hz with hlt | hgt
  · exact ⟨-z, by rw [map_neg]; linarith only [hlt]⟩
  · exact ⟨z, hgt⟩

/-- Two nonzero linear half-spaces with disjoint positive sides near a
common interface point have opposite normals. -/
theorem opposite_planeForms_of_disjoint_near {L M : Point →L[ℝ] ℝ} (hL : L ≠ 0) (hM : M ≠ 0)
    {N : Set Point} (hN : IsOpen N) {y : Point} (hy : y ∈ N) (hyL : L y = 0) (hyM : M y = 0)
    (hd : ∀ z ∈ N, ¬ (0 < L z ∧ 0 < M z)) :
    ∃ C > (0 : ℝ), ∀ z : Point, M z = -C * L z := by
  have hDisj (z : Point) : ¬(0 < L z ∧ 0 < M z) := by
    rintro ⟨h1, h2⟩
    obtain ⟨t, ht, hPoint⟩ := exists_positive_step_mem_open hN hy z
    apply hd _ hPoint
    simp only [map_add, map_smul, hyL, hyM, zero_add, smul_eq_mul]
    exact ⟨mul_pos ht h1, mul_pos ht h2⟩
  obtain ⟨p, hp⟩ := exists_pos_of_ne_zero_planeForm L hL
  let u : Point := (L p)⁻¹ • p
  have hu : L u = 1 := by
    change L ((L p)⁻¹ • p) = 1
    rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hp.ne']
  have hKernel {z : Point} (hz : L z = 0) : M z = 0 := by
    by_contra hm
    let v := u + ((1 - M u) / M z) • z
    have hvL : L v = 1 := by
      simp only [v, map_add, map_smul, hu, hz, smul_eq_mul, mul_zero, add_zero]
    have hvM : M v = 1 := by
      simp only [v, map_add, map_smul, smul_eq_mul, div_mul_cancel₀ _ hm]
      ring
    exact hDisj v ⟨by rw [hvL]; norm_num, by rw [hvM]; norm_num⟩
  have hRatio (z : Point) : M z = L z * M u := by
    have h₀ : L (z - (L z) • u) = 0 := by simp only [map_sub, map_smul, hu, smul_eq_mul, mul_one, sub_self]
    have h₁ := hKernel h₀
    simpa only [map_sub, map_smul, smul_eq_mul, sub_eq_zero] using h₁
  have hu₀ : M u ≠ 0 := by
    intro h
    apply hM
    ext z
    rw [hRatio, h, mul_zero, zero_apply]
  have huN : M u ≤ 0 := le_of_not_gt fun h => hDisj u ⟨by rw [hu]; norm_num, h⟩
  refine ⟨-M u, neg_pos.mpr (lt_of_le_of_ne huN hu₀), fun z => ?_⟩
  rw [hRatio, neg_neg, mul_comm]

end Thesis
