module

public import Thesis.Foundation.QuaternionLoopCompetitors

/-! A uniform strict energy gap in the third quaternion class. -/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped Matrix Matrix.Norms.Frobenius NNReal Quaternion Topology

namespace Thesis

private theorem abs_sum_add_abs_diff (x y : ℝ) :
    |x + y| + |x - y| = 2 * max |x| |y| := by
  have h_of_le (a b : ℝ) (h : |a| ≤ |b|) : |a + b| + |a - b| = 2 * |b| := by
    by_cases hb : 0 ≤ b
    · have ha : -b ≤ a ∧ a ≤ b := abs_le.mp ((abs_of_nonneg hb) ▸ h)
      rw [abs_of_nonneg (by linarith only [ha.1] : 0 ≤ a + b),
        abs_of_nonpos (sub_nonpos.mpr ha.2), abs_of_nonneg hb]
      ring
    · have ha : b ≤ a ∧ a ≤ -b := by
        rw [abs_of_neg (lt_of_not_ge hb)] at h
        simpa only [neg_neg] using abs_le.mp h
      rw [abs_of_nonpos (by linarith only [ha.2] : a + b ≤ 0),
        abs_of_nonneg (sub_nonneg.mpr ha.1), abs_of_neg (lt_of_not_ge hb)]
      ring
  rcases le_total |x| |y| with h | h
  · rw [max_eq_right h, h_of_le x y h]
  · rw [max_eq_left h, add_comm x y, abs_sub_comm x y, h_of_le y x h]

private theorem norm_four_directions_l1 (x y : ℝ) :
    |x| + |y| + |(x + y) / Real.sqrt 2| + |(x - y) / Real.sqrt 2| ≤
      (131 / 50 : ℝ) * Real.sqrt (x ^ 2 + y ^ 2) := by
  let u := max |x| |y|
  let v := min |x| |y|
  have hu : 0 ≤ u := (abs_nonneg x).trans (le_max_left _ _)
  have hv : 0 ≤ v := le_min (abs_nonneg _) (abs_nonneg _)
  have hsqrt : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hpos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hroot : Real.sqrt 2 ≤ (10 / 7 : ℝ) := (sq_le_sq₀ hpos.le (by norm_num)).mp (by
    rw [hsqrt]
    norm_num)
  have hratio : 2 / Real.sqrt 2 = Real.sqrt 2 := by
    apply (div_eq_iff hpos.ne').2
    simpa only [pow_two] using hsqrt.symm
  have huv : u ^ 2 + v ^ 2 = x ^ 2 + y ^ 2 := by
    rcases le_total |x| |y| with h | h
    · simp only [u, v, max_eq_right h, min_eq_left h, sq_abs, add_comm]
    · simp only [u, v, max_eq_left h, min_eq_right h, sq_abs]
  have hsum : |x| + |y| = u + v := (max_add_min _ _).symm
  have hL : |x| + |y| + |(x + y) / Real.sqrt 2| + |(x - y) / Real.sqrt 2| =
      (1 + Real.sqrt 2) * u + v := by
    rw [abs_div, abs_div, abs_of_pos hpos, add_assoc (|x| + |y|), ← add_div,
      abs_sum_add_abs_diff, mul_div_right_comm, hratio, hsum]
    ring
  rw [hL]
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  calc
    _ ≤ ((1 + Real.sqrt 2) ^ 2 + 1) * (u ^ 2 + v ^ 2) := by
      nlinarith only [sq_nonneg ((1 + Real.sqrt 2) * v - u)]
    _ ≤ _ := by
      rw [huv]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      nlinarith only [hsqrt, hroot]

private def frameSpeed (α x : ℝ) : ℝ := Real.sqrt (α ^ 2 + x ^ 2)

private theorem frameSpeed_sq (α x : ℝ) : frameSpeed α x ^ 2 = α ^ 2 + x ^ 2 :=
  Real.sq_sqrt (by positivity)

private theorem frameSpeed_nonneg (α x : ℝ) : 0 ≤ frameSpeed α x := Real.sqrt_nonneg _

private theorem frameSpeed_le_abs_add (α x : ℝ) : frameSpeed α x ≤ |α| + |x| := by
  apply (sq_le_sq₀ (frameSpeed_nonneg _ _) (add_nonneg (abs_nonneg _) (abs_nonneg _))).mp
  rw [frameSpeed_sq]
  nlinarith only [sq_abs α, sq_abs x, mul_nonneg (abs_nonneg α) (abs_nonneg x)]

private theorem frame_four_directions_speed (α β γ : ℝ) :
    frameSpeed α β + frameSpeed α γ +
        frameSpeed α ((β + γ) / Real.sqrt 2) + frameSpeed α ((β - γ) / Real.sqrt 2) ≤
      4 * (707 / 1000 : ℝ) * Real.sqrt (4 * α ^ 2 + β ^ 2 + γ ^ 2) := by
  let R := Real.sqrt (β ^ 2 + γ ^ 2)
  let D := Real.sqrt (4 * α ^ 2 + β ^ 2 + γ ^ 2)
  have hR : 0 ≤ R := Real.sqrt_nonneg _
  have hD : 0 ≤ D := Real.sqrt_nonneg _
  have hRsq : R ^ 2 = β ^ 2 + γ ^ 2 := Real.sq_sqrt (by positivity)
  have hDsq : D ^ 2 = 4 * α ^ 2 + β ^ 2 + γ ^ 2 := Real.sq_sqrt (by positivity)
  have hRD : R ≤ D := (sq_le_sq₀ hR hD).mp (by rw [hRsq, hDsq]; nlinarith only [sq_nonneg α])
  change _ ≤ 4 * (707 / 1000 : ℝ) * D
  by_cases ha : |α| ≤ R / 20
  · have hβ := frameSpeed_le_abs_add α β
    have hγ := frameSpeed_le_abs_add α γ
    have hsum := frameSpeed_le_abs_add α ((β + γ) / Real.sqrt 2)
    have hdiff := frameSpeed_le_abs_add α ((β - γ) / Real.sqrt 2)
    have hL : |β| + |γ| + |(β + γ) / Real.sqrt 2| + |(β - γ) / Real.sqrt 2| ≤
        (131 / 50 : ℝ) * R := norm_four_directions_l1 β γ
    linarith only [hβ, hγ, hsum, hdiff, hL, ha, hRD, hR]
  · have hαSq := (sq_le_sq₀ (div_nonneg hR (by norm_num)) (abs_nonneg α)).2
      (le_of_lt (lt_of_not_ge ha))
    rw [div_pow, hRsq, sq_abs] at hαSq
    let x := frameSpeed α β
    let y := frameSpeed α γ
    let z := frameSpeed α ((β + γ) / Real.sqrt 2)
    let w := frameSpeed α ((β - γ) / Real.sqrt 2)
    have hs : ((β + γ) / Real.sqrt 2) ^ 2 + ((β - γ) / Real.sqrt 2) ^ 2 = β ^ 2 + γ ^ 2 := by
      rw [div_pow, div_pow, Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))]
      ring
    have hsum : x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = 4 * α ^ 2 + 2 * (β ^ 2 + γ ^ 2) := by
      simp only [x, y, z, w, frameSpeed_sq]
      linarith only [hs]
    change x + y + z + w ≤ 4 * (707 / 1000 : ℝ) * D
    apply (sq_le_sq₀
      (add_nonneg (add_nonneg (add_nonneg (frameSpeed_nonneg _ _) (frameSpeed_nonneg _ _))
        (frameSpeed_nonneg _ _)) (frameSpeed_nonneg _ _)) (by positivity)).mp
    calc
      _ ≤ 4 * (x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2) := by
        nlinarith only [sq_nonneg (x - y), sq_nonneg (z - w), sq_nonneg (x + y - (z + w))]
      _ ≤ _ := by
        rw [hsum, mul_pow (4 * (707 / 1000 : ℝ)), hDsq]
        nlinarith only [hαSq, sq_nonneg α, sq_nonneg β, sq_nonneg γ]

private def fourQuaternionAxes : Fin 4 → ℍ :=
  ![firstQuaternionUnit, secondQuaternionUnit,
    ⟨0, 1 / Real.sqrt 2, 1 / Real.sqrt 2, 0⟩,
    ⟨0, 1 / Real.sqrt 2, -1 / Real.sqrt 2, 0⟩]

private def fourFrameOffsets (β γ : ℝ) : Fin 4 → ℝ :=
  ![β, γ, (β + γ) / Real.sqrt 2, (β - γ) / Real.sqrt 2]

private theorem norm_fourQuaternionAxes (i : Fin 4) : ‖fourQuaternionAxes i‖ = 1 := by
  apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
  rw [pow_two ‖fourQuaternionAxes i‖, ← Quaternion.normSq_eq_norm_mul_self, Quaternion.normSq_def']
  fin_cases i <;> norm_num [fourQuaternionAxes, firstQuaternionUnit, secondQuaternionUnit, div_pow,
    Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))]

private theorem norm_fourQuaternion_commutator (u : ℍ) (i : Fin 4) :
    ‖u * fourQuaternionAxes i - fourQuaternionAxes i * u‖ =
      frameSpeed (2 * u.imK) (fourFrameOffsets (-2 * u.imJ) (2 * u.imI) i) := by
  apply (sq_eq_sq₀ (norm_nonneg _) (frameSpeed_nonneg _ _)).mp
  rw [pow_two ‖_‖, ← Quaternion.normSq_eq_norm_mul_self, Quaternion.normSq_def', frameSpeed_sq]
  have hsqrt : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hpos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  fin_cases i <;> simp [fourQuaternionAxes, fourFrameOffsets, firstQuaternionUnit,
    secondQuaternionUnit, div_pow, hsqrt] <;> ring_nf
  all_goals
    field_simp [hpos.ne']
    ring_nf
    rw [hsqrt]
    ring

private theorem third_word_conjugate_four_axes {g : QuaternionGroup 2}
    (hg : g = QuaternionGroup.xa 1 ∨ g = QuaternionGroup.xa 3) (i : Fin 4) :
    quaternionConjugate (quaternionWordReal g) (fourQuaternionAxes i) = -fourQuaternionAxes i := by
  rcases hg with rfl | rfl <;> fin_cases i <;> ext <;>
    simp [fourQuaternionAxes, firstQuaternionUnit, secondQuaternionUnit, quaternionConjugate,
      quaternionWordReal_negative_k, quaternionWordReal_k]

private theorem norm_quaternionConjugate_unit {q : ℍ} (hq : ‖q‖ = 1) (b : ℍ) :
    ‖quaternionConjugate q b‖ = ‖b‖ := by
  simp only [quaternionConjugate, norm_mul, Quaternion.norm_star, hq, one_mul, mul_one]

private theorem ac_quaternionConjugate_curve {q : ℝ → ℍ} {s t : ℝ}
    (hunit : ∀ x, ‖q x‖ = 1) (hq : AbsolutelyContinuousOnInterval q s t) {b : ℍ} (hb : ‖b‖ = 1) :
    AbsolutelyContinuousOnInterval (fun x => quaternionConjugate (q x) b) s t := by
  have hLip : LipschitzOnWith (2 : ℝ≥0) (fun z : ℍ => quaternionConjugate z b) {z | ‖z‖ = 1} :=
    LipschitzOnWith.of_dist_le_mul fun _ hp _ hp' => by
      simpa only [dist_eq_norm, NNReal.coe_ofNat] using norm_sub_conjugate_le hp hp' hb
  exact ac_comp_lipschitzOn (f := q) (g := fun z => quaternionConjugate z b) hq hLip
    (fun x _ => hunit x)

private theorem norm_deriv_quaternionConjugate_curve {q : ℝ → ℍ} {x : ℝ}
    (hd : DifferentiableAt ℝ q x) (hunit : ∀ y, ‖q y‖ = 1) (b : ℍ) :
    let u := star (q x) * deriv q x
    ‖deriv (fun y => quaternionConjugate (q y) b) x‖ = ‖u * b - b * u‖ := by
  let u := star (q x) * deriv q x
  have hd' := hasDerivAt_quaternionConjugate hd.hasDerivAt (Eventually.of_forall hunit) b
  change ‖deriv (fun y => quaternionConjugate (q y) b) x‖ = ‖u * b - b * u‖
  exact (congrArg (fun z : ℍ => ‖z‖) hd'.deriv).trans (norm_quaternionConjugate_unit (hunit x) _)

private theorem memLp_deriv_quaternionConjugate_curve {q : ℝ → ℍ} {s t : ℝ} (hst : s ≤ t)
    (hunit : ∀ x, ‖q x‖ = 1) (hq : AbsolutelyContinuousOnInterval q s t)
    (hDq : MemLp (deriv q) 2 (volume.restrict (Ioo s t))) {b : ℍ} (hb : ‖b‖ = 1) :
    MemLp (deriv (fun x => quaternionConjugate (q x) b)) 2 (volume.restrict (Ioo s t)) := by
  refine (hDq.norm.const_mul 2).mono' (aestronglyMeasurable_deriv _ _) ?_
  apply (ae_restrict_iff' measurableSet_Ioo).2
  filter_upwards [ae_differentiableAt_quaternion_of_ac hq] with x hx hxmem
  have hx' : x ∈ uIcc s t := by rw [uIcc_of_le hst]; exact Ioo_subset_Icc_self hxmem
  rw [norm_deriv_quaternionConjugate_curve (hx hx') hunit]
  refine (norm_sub_le _ _).trans_eq ?_
  simp only [norm_mul, Quaternion.norm_star, hunit, hb, mul_one, one_mul, two_mul]

private theorem four_conjugate_lengths_ge_pi {q : ℝ → ℍ} {T : ℝ} (hT : 0 ≤ T)
    (hq : AbsolutelyContinuousOnInterval q 0 T) (hDq : MemLp (deriv q) 2 (volume.restrict (Ioo 0 T)))
    (hunit : ∀ x, ‖q x‖ = 1) {g : QuaternionGroup 2}
    (hg : g = QuaternionGroup.xa 1 ∨ g = QuaternionGroup.xa 3)
    (hend : q T = q 0 * quaternionWordReal g) (i : Fin 4) :
    Real.pi ≤ ∫ x in 0..T, ‖deriv (fun y => quaternionConjugate (q y) (fourQuaternionAxes i)) x‖ := by
  let b := fourQuaternionAxes i
  let f (x : ℝ) := quaternionConjugate (q x) b
  have hb : ‖b‖ = 1 := norm_fourQuaternionAxes i
  have hfunit (x : ℝ) : ‖f x‖ = 1 := (norm_quaternionConjugate_unit (hunit x) b).trans hb
  have hfAC : AbsolutelyContinuousOnInterval f 0 T := ac_quaternionConjugate_curve hunit hq hb
  have hfD : MemLp (deriv f) 2 (volume.restrict (Ioo 0 T)) :=
    memLp_deriv_quaternionConjugate_curve hT hunit hq hDq hb
  have hfend : f T = -f 0 := by
    change quaternionConjugate (q T) b = -quaternionConjugate (q 0) b
    rw [hend, quaternionConjugate_comp, third_word_conjugate_four_axes hg i]
    simp only [quaternionConjugate, mul_neg, neg_mul, b]
  have hangle := quaternion_curve_arc_le_integral_speed hT hfAC hfunit
    (StratificationTheory.intervalIntegrable_of_memLp_two hT hfD.norm)
  rwa [hfend, inner_neg_right, real_inner_self_eq_norm_sq, hfunit, one_pow, Real.arccos_neg_one] at hangle

private theorem cover_four_direction_speeds (a : BulkCoefficients) (v : ℝ → Sphere3) {x : ℝ}
    (hd : DifferentiableAt ℝ (fun y => Quaternion.linearIsometryEquivTuple.symm (v y).val) x) :
    let q (y : ℝ) := Quaternion.linearIsometryEquivTuple.symm (v y).val
    (∑ i : Fin 4, ‖deriv (fun y => quaternionConjugate (q y) (fourQuaternionAxes i)) x‖) ≤
      (4 * (707 / 1000 : ℝ) / (Real.sqrt 2 * vacuumRadius a)) *
        ‖deriv (fun y => (cover a (v y) : Tensor)) x‖ := by
  intro q
  let u := star (q x) * deriv q x
  let α := 2 * u.imK
  let β := -2 * u.imJ
  let γ := 2 * u.imI
  let d := ‖deriv (fun y => (cover a (v y) : Tensor)) x‖
  let r := vacuumRadius a
  have hr : 0 < r := vacuumRadius_pos a
  have hunit (y : ℝ) : ‖q y‖ = 1 := quaternionTuple_symm_norm_eq_one (v y)
  have hA (i : Fin 4) :
      ‖deriv (fun y => quaternionConjugate (q y) (fourQuaternionAxes i)) x‖ =
        frameSpeed α (fourFrameOffsets β γ i) :=
    (norm_deriv_quaternionConjugate_curve hd hunit _).trans (norm_fourQuaternion_commutator u i)
  have hmetric : (1 / 2 : ℝ) * d ^ 2 = r ^ 2 * (4 * α ^ 2 + β ^ 2 + γ ^ 2) := by
    have h := cover_curve_metric a v hd.hasDerivAt
    change (1 / 2 : ℝ) * d ^ 2 = 4 * r ^ 2 * (u.imI ^ 2 + u.imJ ^ 2 + 4 * u.imK ^ 2) at h
    exact h.trans (by dsimp only [α, β, γ]; ring)
  have hscale : Real.sqrt (4 * α ^ 2 + β ^ 2 + γ ^ 2) = d / (Real.sqrt 2 * r) := by
    apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (div_nonneg (norm_nonneg _) (by positivity))).mp
    have hden : (Real.sqrt 2 * r) ^ 2 = 2 * r ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))]
    rw [Real.sq_sqrt (by positivity), div_pow, hden]
    apply (eq_div_iff (by positivity : 2 * r ^ 2 ≠ 0)).2
    calc
      _ = 2 * (r ^ 2 * (4 * α ^ 2 + β ^ 2 + γ ^ 2)) := by ring
      _ = _ := by rw [← hmetric]; ring
  change _ ≤ (4 * (707 / 1000 : ℝ) / (Real.sqrt 2 * r)) * d
  simp_rw [hA]
  rw [Fin.sum_univ_four]
  change frameSpeed α β + frameSpeed α γ +
      frameSpeed α ((β + γ) / Real.sqrt 2) + frameSpeed α ((β - γ) / Real.sqrt 2) ≤ _
  calc
    _ ≤ 4 * (707 / 1000 : ℝ) * Real.sqrt (4 * α ^ 2 + β ^ 2 + γ ^ 2) :=
      frame_four_directions_speed α β γ
    _ = _ := by rw [hscale]; ring

private theorem third_gap_from_length {f : ℝ → ℝ} {r : ℝ} (hr : 0 < r) :
    let T := 2 * Real.pi
    let c : ℝ := 707 / 1000
    IntervalIntegrable f volume 0 T →
    IntervalIntegrable (fun x => f x ^ 2) volume 0 T →
    4 * Real.pi ≤ (4 * c / (Real.sqrt 2 * r)) * (∫ x in 0..T, f x) →
    Real.pi * r ^ 2 / (2 * c ^ 2) ≤ (1 / 2 : ℝ) * ∫ x in 0..T, f x ^ 2 := by
  intro T c hInt hIntSq hL
  have hc : 0 < c := by dsimp only [c]; positivity
  have hT : 0 < T := by dsimp only [T]; positivity
  have hs : 0 < Real.sqrt 2 * r := by positivity
  let L : ℝ := ∫ x in 0..T, f x
  have hL' : Real.pi * (Real.sqrt 2 * r) / c ≤ L := by
    apply (div_le_iff₀' hc).2
    have h := mul_le_mul_of_nonneg_right hL (div_nonneg hs.le (by norm_num : 0 ≤ (4 : ℝ)))
    change (4 * Real.pi) * (Real.sqrt 2 * r / 4) ≤
      (4 * c / (Real.sqrt 2 * r)) * L * (Real.sqrt 2 * r / 4) at h
    calc
      _ = (4 * Real.pi) * (Real.sqrt 2 * r / 4) := by ring
      _ ≤ _ := h
      _ = _ := by field_simp [hs.ne']
  have htarget : 0 ≤ Real.pi * (Real.sqrt 2 * r) / c := by positivity
  have hsquare : (Real.pi * (Real.sqrt 2 * r) / c) ^ 2 ≤ T * ∫ x in 0..T, f x ^ 2 := by
    apply ((sq_le_sq₀ htarget (htarget.trans hL')).2 hL').trans
    simpa only [sub_zero] using sq_integral_le_length_mul_integral_sq hT hInt hIntSq
  have hnorm : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  apply (mul_le_mul_iff_right₀ (show 0 < 2 * T by positivity)).mp
  calc
    _ = (Real.pi * (Real.sqrt 2 * r) / c) ^ 2 := by
      dsimp only [T]
      field_simp [hc.ne']
      ring_nf
      rw [hnorm]
    _ ≤ _ := hsquare
    _ = _ := by ring

/-- The third class has a uniform strict gap with the rational constant `707/1000`. -/
theorem vacuumLoop_energy_ge_third_gap (a : BulkCoefficients) (v₀ : Sphere3)
    (γ : Path (vacuumQuaternionProjection a v₀) (vacuumQuaternionProjection a v₀))
    (hγ : VacuumLoopH1 γ) {g : QuaternionGroup 2}
    (hg : g = QuaternionGroup.xa 1 ∨ g = QuaternionGroup.xa 3)
    (hclass : vacuumFundamentalGroupEquiv a v₀
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)) = g) :
    Real.pi * vacuumRadius a ^ 2 / (2 * (707 / 1000 : ℝ) ^ 2) ≤ vacuumLoopEnergy γ := by
  let T := 2 * Real.pi
  have hT : 0 < T := by dsimp only [T]; positivity
  obtain ⟨v, _, _, hcover, hend, hqAC, hDq, _⟩ :=
    vacuumLoop_exists_sobolev_lift a v₀ γ hT hγ.1 hγ.2
  let q (x : ℝ) := Quaternion.linearIsometryEquivTuple.symm (v x).val
  let Q := vacuumLoopTensor γ T
  let speed (x : ℝ) := ‖deriv Q x‖
  let s (i : Fin 4) (x : ℝ) :=
    ‖deriv (fun y => quaternionConjugate (q y) (fourQuaternionAxes i)) x‖
  let C : ℝ := 4 * (707 / 1000 : ℝ) / (Real.sqrt 2 * vacuumRadius a)
  have hunit (x : ℝ) : ‖q x‖ = 1 := quaternionTuple_symm_norm_eq_one (v x)
  have hqT : q T = q 0 * quaternionWordReal g := by simpa only [hclass] using hend
  have hL (i : Fin 4) : Real.pi ≤ ∫ x in 0..T, s i x :=
    four_conjugate_lengths_ge_pi hT.le hqAC hDq hunit hg hqT i
  have hInt (i : Fin 4) : IntervalIntegrable (s i) volume 0 T :=
    StratificationTheory.intervalIntegrable_of_memLp_two hT.le
      (memLp_deriv_quaternionConjugate_curve hT.le hunit hqAC hDq (norm_fourQuaternionAxes i)).norm
  have hQInt : IntervalIntegrable speed volume 0 T :=
    StratificationTheory.intervalIntegrable_of_memLp_two hT.le hγ.2.norm
  have hPt : (fun x => ∑ i : Fin 4, s i x) ≤ᵐ[volume.restrict (Icc 0 T)] fun x => C * speed x := by
    apply (ae_restrict_iff' measurableSet_Icc).2
    filter_upwards [ae_differentiableAt_quaternion_of_ac hqAC] with x hx hxmem
    have hmem : x ∈ uIcc 0 T := by rwa [uIcc_of_le hT.le]
    have h := cover_four_direction_speeds a v (hx hmem)
    dsimp only at h
    rw [hcover] at h
    exact h
  have hSInt : IntervalIntegrable (fun x => ∑ i : Fin 4, s i x) volume 0 T := by
    have heq : (∑ i : Fin 4, s i) = fun x => ∑ i : Fin 4, s i x := by
      funext x
      exact Finset.sum_apply x Finset.univ s
    rw [← heq]
    exact IntervalIntegrable.sum Finset.univ (fun i _ => hInt i)
  have hcompare := intervalIntegral.integral_mono_ae_restrict hT.le hSInt (hQInt.const_mul C) hPt
  have hbound : 4 * Real.pi ≤ C * ∫ x in 0..T, speed x := calc
    _ = ∑ _i : Fin 4, Real.pi := by simp
    _ ≤ ∑ i : Fin 4, ∫ x in 0..T, s i x := Finset.sum_le_sum (fun i _ => hL i)
    _ = ∫ x in 0..T, ∑ i : Fin 4, s i x := (intervalIntegral.integral_finsetSum (fun i _ => hInt i)).symm
    _ ≤ _ := by simpa only [intervalIntegral.integral_const_mul] using hcompare
  have hIntSq : IntervalIntegrable (fun x => speed x ^ 2) volume 0 T :=
    intervalIntegrable_sq_norm_of_memLp_two hT.le hγ.2
  have hgap := third_gap_from_length (vacuumRadius_pos a) hQInt hIntSq hbound
  simpa only [vacuumLoopEnergy, intervalIntegral.integral_const_mul] using hgap

/-- The infimum of actual Sobolev vacuum loop energies with an ordered class at the given base. -/
def vacuumClassCost (a : BulkCoefficients) (v : Sphere3) (g : QuaternionGroup 2) : ℝ :=
  sInf (vacuumClassEnergies a v g)

theorem vacuumClassCost_one (a : BulkCoefficients) (v : Sphere3) :
    vacuumClassCost a v 1 = 0 := (vacuumClassEnergies_isLeast_one a v).csInf_eq

theorem vacuumClassCost_light (a : BulkCoefficients) (v : Sphere3)
    {g : QuaternionGroup 2} (hg : IsLightQuaternion g) :
    vacuumClassCost a v g = kappaStar a := (vacuumClassEnergies_isLeast_light a v hg).csInf_eq

theorem vacuumClassCost_antipodal (a : BulkCoefficients) (v : Sphere3) :
    vacuumClassCost a v (QuaternionGroup.a 2) = 4 * kappaStar a :=
  (vacuumClassEnergies_isLeast_antipodal a v).csInf_eq

theorem vacuumClassCost_third_gap (a : BulkCoefficients) (v : Sphere3)
    {g : QuaternionGroup 2} (hg : g = QuaternionGroup.xa 1 ∨ g = QuaternionGroup.xa 3) :
    Real.pi * vacuumRadius a ^ 2 / (2 * (707 / 1000 : ℝ) ^ 2) ≤ vacuumClassCost a v g ∧
      vacuumClassCost a v g ≤ 4 * kappaStar a := by
  have hn : 4 * kappaStar a ∈ vacuumClassEnergies a v g :=
    exists_vacuumLoop_third_class_competitor a v hg
  have hbound : ∀ E ∈ vacuumClassEnergies a v g,
      Real.pi * vacuumRadius a ^ 2 / (2 * (707 / 1000 : ℝ) ^ 2) ≤ E := by
    intro E hE
    obtain ⟨γ, hclass, hγ, henergy⟩ := hE
    rw [← henergy]
    exact vacuumLoop_energy_ge_third_gap a v γ hγ hg hclass
  exact ⟨le_csInf ⟨_, hn⟩ hbound, csInf_le ⟨_, hbound⟩ hn⟩

theorem two_kappaStar_lt_third_gap (a : BulkCoefficients) :
    2 * kappaStar a < Real.pi * vacuumRadius a ^ 2 / (2 * (707 / 1000 : ℝ) ^ 2) := by
  apply (lt_div_iff₀ (by norm_num : 0 < 2 * (707 / 1000 : ℝ) ^ 2)).2
  have hpos : 0 < Real.pi * vacuumRadius a ^ 2 :=
    mul_pos Real.pi_pos (sq_pos_of_pos (vacuumRadius_pos a))
  calc
    _ = (2 * (707 / 1000 : ℝ) ^ 2) * (Real.pi * vacuumRadius a ^ 2) := by
      unfold kappaStar
      ring
    _ < _ := by
      simpa only [one_mul] using
        mul_lt_mul_of_pos_right (by norm_num : 2 * (707 / 1000 : ℝ) ^ 2 < 1) hpos

theorem vacuumClassCost_third_strict (a : BulkCoefficients) (v : Sphere3)
    {g : QuaternionGroup 2} (hg : g = QuaternionGroup.xa 1 ∨ g = QuaternionGroup.xa 3) :
    2 * kappaStar a < vacuumClassCost a v g :=
  (two_kappaStar_lt_third_gap a).trans_le (vacuumClassCost_third_gap a v hg).1

end Thesis
