module

public import Thesis.Variational.EllipticPatchGeometry
public import Thesis.Variational.LocalEllipticTangentialGradient
public import Thesis.Upstream.LocalSobolevGradientTransport

/-! The full weak second gradient on the flat side of a smooth boundary chart. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set
open scoped BigOperators ContDiff ENNReal RealInnerProductSpace

namespace Thesis

/-- The common quadratic size of an ambient gradient and a forcing field. -/
@[expose] def ambientPoissonL2Size {n q : ℕ} (D : Domain n → HarmonicMaps.Gradient n q)
    (f : Domain n → Ambient q) : ℝ :=
  Real.sqrt ((∫ x, hsNormSq (D x)) + ∫ x, ‖f x‖^2)

theorem ambientPoissonL2Size_nonneg {n q : ℕ} (D : Domain n → HarmonicMaps.Gradient n q)
    (f : Domain n → Ambient q) : 0 ≤ ambientPoissonL2Size D f :=
  Real.sqrt_nonneg _

theorem ambientPoissonL2Size_sq {n q : ℕ} (D : Domain n → HarmonicMaps.Gradient n q)
    (f : Domain n → Ambient q) :
    (ambientPoissonL2Size D f)^2 = (∫ x, hsNormSq (D x)) + ∫ x, ‖f x‖^2 :=
  Real.sq_sqrt (add_nonneg (integral_nonneg fun _ => hsNormSq_nonneg _)
    (integral_nonneg fun _ => sq_nonneg _))

theorem ambient_lpNorm_grad_column_le_poisson_size {n q : ℕ} {D : Domain n → HarmonicMaps.Gradient n q}
    (f : Domain n → Ambient q) (hD : ∀ j, MemLp (fun x => D x j) 2 volume)
    (V : Set (Domain n)) (j : Fin n) :
    lpNorm (fun x => D x j) 2 (volume.restrict V) ≤ ambientPoissonL2Size D f := by
  refine (ambient_lpNorm_two_mono_measure (hD j) Measure.restrict_le_self).trans ?_
  apply (sq_le_sq₀ lpNorm_nonneg (ambientPoissonL2Size_nonneg _ _)).1
  rw [ambient_lpNorm_two_sq (hD j),ambientPoissonL2Size_sq]
  refine (integral_mono
    ((memLp_two_iff_integrable_sq_norm (hD j).1).mp (hD j))
    (integrable_hsNormSq_of_memLp_columns hD) ?_).trans
      (le_add_of_nonneg_right (integral_nonneg fun _ => sq_nonneg _))
  intro x
  simp only [hsNormSq]
  exact Finset.single_le_sum (f := fun i : Fin n => ‖D x i‖^2)
    (fun _ _ => sq_nonneg _) (Finset.mem_univ j)

theorem ambient_lpNorm_force_le_poisson_size {n q : ℕ} (D : Domain n → HarmonicMaps.Gradient n q)
    {f : Domain n → Ambient q} (hf : MemLp f 2 volume) (V : Set (Domain n)) :
    lpNorm f 2 (volume.restrict V) ≤ ambientPoissonL2Size D f := by
  refine (ambient_lpNorm_two_mono_measure hf Measure.restrict_le_self).trans ?_
  apply (sq_le_sq₀ lpNorm_nonneg (ambientPoissonL2Size_nonneg _ _)).1
  rw [ambient_lpNorm_two_sq hf,ambientPoissonL2Size_sq]
  exact le_add_of_nonneg_left (integral_nonneg fun _ => hsNormSq_nonneg _)

theorem ambient_lpNorm_le_mul_poisson_size_of_sq {n q : ℕ}
    {D : Domain n → HarmonicMaps.Gradient n q} {f g : Domain n → Ambient q}
    {V : Set (Domain n)} (hg : MemLp g 2 (volume.restrict V)) {C : ℝ} (hC : 0 ≤ C)
    (h : (∫ x in V, ‖g x‖^2) ≤ C*((∫ x, hsNormSq (D x)) + ∫ x, ‖f x‖^2)) :
    lpNorm g 2 (volume.restrict V) ≤ Real.sqrt C*ambientPoissonL2Size D f := by
  apply (sq_le_sq₀ lpNorm_nonneg (mul_nonneg (Real.sqrt_nonneg _) (ambientPoissonL2Size_nonneg _ _))).1
  rw [ambient_lpNorm_two_sq hg,mul_pow,Real.sq_sqrt hC,ambientPoissonL2Size_sq]
  exact h

theorem exists_ambient_gradientMetric_chart_coercivity {n q : ℕ}
    (F : Domain n ≃ₜ Domain n) (hF : ContDiff ℝ ∞ (F : Domain n → Domain n))
    (hInv : ContDiff ℝ ∞ (F.symm : Domain n → Domain n))
    {K : Set (Domain n)} (hK : IsCompact K) :
    ∃ ell : ℝ, 0 < ell ∧ ∀ x ∈ K, ∀ y : AmbientGradientHilbert n q,
      ell*‖y‖^2 ≤ inner ℝ (ambientGradientMetric n q (fderiv ℝ F.symm (F x)) y) y := by
  let B (x : Domain n) := ambientGradientPrecompose n q (fderiv ℝ F x)
  have hB : Continuous B := (ambientGradientPrecompose n q).continuous.comp
    (hF.continuous_fderiv (by simp))
  obtain ⟨M,hM⟩ := hK.exists_bound_of_continuousOn hB.continuousOn
  let J := max M 1
  have hJp : 0 < J := zero_lt_one.trans_le (le_max_right _ _)
  refine ⟨J⁻¹^2, by positivity,?_⟩
  intro x hx y
  let K' := fderiv ℝ F.symm (F x)
  let z := ambientGradientPrecompose n q K' y
  have hId : B x z = y := by
    dsimp only [B,z,K']
    rw [ambientGradientPrecompose_comp,fderiv_symm_comp_fderiv_homeomorph F hF hInv,
      ambientGradientPrecompose_id]
  have hN : ‖y‖ ≤ J*‖z‖ := by
    rw [← hId]
    exact ((B x).le_opNorm z).trans
      (mul_le_mul_of_nonneg_right ((hM x hx).trans (le_max_left _ _)) (norm_nonneg _))
  have hSq : ‖y‖^2 ≤ J^2*‖z‖^2 := by
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) hN 2
  rw [inner_ambientGradientMetric,real_inner_self_eq_norm_sq]
  change J⁻¹^2*‖y‖^2 ≤ ‖z‖^2
  calc
    _ ≤ J⁻¹^2*(J^2*‖z‖^2) := mul_le_mul_of_nonneg_left hSq (sq_nonneg _)
    _ = _ := by rw [← mul_assoc,← mul_pow,inv_mul_cancel₀ hJp.ne',one_pow,one_mul]

theorem memLp_ambient_coordinate_operator_of_compact_gradient {n q : ℕ}
    {A : Domain n → AmbientGradientHilbert n q →L[ℝ] AmbientGradientHilbert n q}
    (hA : Continuous A) {D : Domain n → HarmonicMaps.Gradient n q}
    (hD : ∀ j, MemLp (fun x => D x j) 2 volume) {K : Set (Domain n)} (hK : IsCompact K)
    (hSupp : ∀ x ∉ K, D x = 0) :
    MemLp (fun x => A x (packAmbientGradient (D x))) 2 volume := by
  let v (x : Domain n) := packAmbientGradient (D x)
  have hv := memLp_packAmbientGradient hD
  obtain ⟨M,hM⟩ := hK.exists_bound_of_continuousOn hA.continuousOn
  let C := max M 0
  have hC : 0 ≤ C := le_max_right _ _
  have hMeas : AEStronglyMeasurable (fun x => A x (v x)) volume :=
    (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      (hA.aestronglyMeasurable.prodMk hv.1)
  apply (hv.norm.const_mul C).mono' hMeas
  refine Eventually.of_forall fun x => ?_
  by_cases hx : x ∈ K
  · exact ((A x).le_opNorm (v x)).trans <|
      mul_le_mul_of_nonneg_right ((hM x hx).trans (le_max_left _ _)) (norm_nonneg _)
  · have hV : v x = 0 := by dsimp only [v]; rw [hSupp x hx]; rfl
    rw [hV,map_zero,norm_zero]
    exact mul_nonneg hC (norm_nonneg _)

/-- The local full weak graph for an equation in the metric of a smooth
boundary chart. The chart and radius determine the bound before the data. -/
theorem exists_flatBoundary_secondWeakColumns {q : ℕ}
    (F : Point ≃ₜ Point) (hF : ContDiff ℝ ∞ (F : Point → Point))
    (hInv : ContDiff ℝ ∞ (F.symm : Point → Point)) {R : ℝ} (hR : 0 < R) :
    let V := ball (0 : Point) R ∩ upperCoordinateHalfSpace.val
    let W : OpenDomain 3 := ⟨ball 0 (R/4) ∩ upperCoordinateHalfSpace.val,
      isOpen_ball.inter upperCoordinateHalfSpace.property⟩
    let A (x : Point) := ambientGradientMetric 3 q (fderiv ℝ F.symm (F x))
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {u f : Point → Ambient q} {D : Point → HarmonicMaps.Gradient 3 q},
        MemW12 (⟨univ,isOpen_univ⟩ : OpenDomain 3) u D →
        MemLp f 2 volume →
        MemLp (fun x => A x (packAmbientGradient (D x))) 2 volume →
        HasWeakPackedDivergenceEq V (fun x => A x (packAmbientGradient (D x))) f →
        (∀ x ∈ ball (0 : Point) R, x ∉ upperCoordinateHalfSpace.val → u x = 0 ∧ D x = 0) →
        ∃ H : Point → Fin 3 → HarmonicMaps.Gradient 3 q,
          ∀ j, MemW12 W (fun x => D x j) (fun x => H x j) ∧
            ∀ i, lpNorm (fun x => H x j i) 2 (volume.restrict W.val) ≤ C*ambientPoissonL2Size D f := by
  dsimp only
  let S := upperCoordinateHalfSpace
  let V := ball (0 : Point) R ∩ S.val
  let W : OpenDomain 3 := ⟨ball 0 (R/4) ∩ S.val,isOpen_ball.inter S.property⟩
  letI : IsFiniteMeasure ((volume : Measure Point).restrict W.val) :=
    isFiniteMeasure_restrict.mpr (ne_top_of_le_ne_top measure_ball_ne_top
      (measure_mono (show W.val ⊆ ball (0 : Point) (R/4) from inter_subset_left)))
  let K (x : Point) := fderiv ℝ F.symm (F x)
  let A (x : Point) := ambientGradientMetric 3 q (K x)
  let a (x : Point) (i j : Fin 3) := ambientGradientMetricEntry (K x) i j
  have hK : ContDiff ℝ ∞ K := (hInv.fderiv_right (by simp)).comp hF
  have hA : ContDiff ℝ ∞ A := contDiff_ambientGradientMetric.comp hK
  have ha (i j : Fin 3) : ContDiff ℝ ∞ fun x => a x i j :=
    (contDiff_ambientGradientMetricEntry i j).comp hK
  have hDiag (x : Point) : a x 2 2 ≠ 0 :=
    (ambientGradientMetricEntry_diag_pos_of_rightInverse (K x) (fderiv ℝ F x)
      (fderiv_symm_comp_fderiv_homeomorph F hF hInv x) 2).ne'
  have hInvA : ContDiff ℝ ∞ fun x => (a x 2 2)⁻¹ := (ha 2 2).inv hDiag
  have hWS : W.val ⊆ closedBall (0 : Point) (R/4) := inter_subset_left.trans ball_subset_closedBall
  have hCompact := isCompact_closedBall (0 : Point) (R/4)
  obtain ⟨A₀,hA₀,haB⟩ := exists_uniform_abs_bound_on_compact hCompact
    (fun ij : Fin 3 × Fin 3 => fun x => a x ij.1 ij.2) (fun ij => (ha ij.1 ij.2).continuous)
  obtain ⟨A₁,hA₁,haD⟩ := exists_uniform_abs_bound_on_compact hCompact
    (fun ijk : (Fin 3 × Fin 3) × Fin 3 =>
      coordinateDerivative (fun x => a x ijk.1.1 ijk.1.2) (ha ijk.1.1 ijk.1.2) ijk.2)
    (fun ijk => (((ha ijk.1.1 ijk.1.2).continuous_fderiv (by simp)).clm_apply continuous_const))
  obtain ⟨B₀,hB₀⟩ := hCompact.exists_bound_of_continuousOn hInvA.continuous.continuousOn
  obtain ⟨B₁,hB₁⟩ := hCompact.exists_bound_of_continuousOn
    (((hInvA.continuous_fderiv (by simp)).clm_apply continuous_const :
      Continuous (coordinateDerivative (fun x => (a x 2 2)⁻¹) hInvA 2))).continuousOn
  let M := max (max A₀ A₁) (max B₀ B₁)
  have hM : 0 ≤ M := hA₀.trans ((le_max_left _ _).trans (le_max_left _ _))
  obtain ⟨ell,hell,hEll⟩ := exists_ambient_gradientMetric_chart_coercivity (q := q) F hF hInv
    (isCompact_closedBall (0 : Point) R)
  obtain ⟨C,hC,hTang⟩ := exists_local_second_weak_column_invariant_direction hR hell
    S upperCoordinateHalfSpace_convex (upperCoordinateHalfSpace_inter_ball_nonempty hR) A hA hEll
  obtain ⟨L,hL,hFull⟩ := exists_second_weakColumns_of_tangential_and_divergence (q := q) W (2 : Fin 3)
    a ha (fun x _ => hDiag x) hInvA M hM
    (fun i j x hx => (haB (i,j) x (hWS hx)).trans ((le_max_left _ _).trans (le_max_left _ _)))
    (fun i j k x hx => (haD ((i,j),k) x (hWS hx)).trans ((le_max_right _ _).trans (le_max_left _ _)))
    (fun x hx => ((Real.norm_eq_abs _).symm ▸ hB₀ x (hWS hx)).trans
      ((le_max_left _ _).trans (le_max_right _ _)))
    (fun x hx => ((Real.norm_eq_abs _).symm ▸ hB₁ x (hWS hx)).trans
      ((le_max_right _ _).trans (le_max_right _ _)))
  let B := max 1 (Real.sqrt C)
  have hB : 1 ≤ B := le_max_left _ _
  refine ⟨L*B, by nlinarith only [hL,hB,mul_nonneg (sub_nonneg.mpr hL) (sub_nonneg.mpr hB)],?_⟩
  intro u f D hu hf hFlux hWeak hZero
  let E := ambientPoissonL2Size D f
  have hE : 0 ≤ E := ambientPoissonL2Size_nonneg _ _
  have hBE : E ≤ B*E := le_mul_of_one_le_left hE hB
  have hU : W.val ⊆ V := inter_subset_inter_left _ (ball_subset_ball (by linarith only [hR]))
  have hRestrict : (volume : Measure Point).restrict W.val ≤ volume.restrict univ :=
    Measure.restrict_mono_set _ (subset_univ _)
  have huW : MemW12 W u D :=
    ⟨hu.1.mono (subset_univ _),hu.2.1.mono_measure hRestrict,fun j => (hu.2.2 j).mono_measure hRestrict⟩
  have hD (j : Fin 3) : MemLp (fun x => D x j) 2 volume := by
    simpa only [Measure.restrict_univ] using hu.2.2 j
  have hfW : MemLp f 2 (volume.restrict W.val) := hf.mono_measure Measure.restrict_le_self
  have heq : HasWeakPackedDivergenceEq W.val (fun x => A x (packAmbientGradient (D x))) f :=
    hWeak.mono hU
  have hSame (x : Point) : A x (packAmbientGradient (D x)) =
      packAmbientGradient (fun i => ∑ j, a x i j • D x j) := by
    apply PiLp.ext
    intro i
    rw [packAmbientGradient_apply,ambientGradientMetric_apply_column]
    simp only [packAmbientGradient_apply,a]
  have hEq' : HasWeakPackedDivergenceEq W.val
      (fun x => packAmbientGradient (fun i => ∑ j, a x i j • D x j)) f := by
    rw [← show (fun x => A x (packAmbientGradient (D x))) =
      (fun x => packAmbientGradient (fun i => ∑ j, a x i j • D x j)) from funext hSame]
    exact heq
  have hT (i : {i : Fin 3 // i ≠ 2}) :
      ∃ T : Point → HarmonicMaps.Gradient 3 q, ∀ j,
        MemLp (fun x => T x j) 2 (volume.restrict W.val) ∧
        lpNorm (fun x => T x j) 2 (volume.restrict W.val) ≤ B*E ∧
        IsWeakAmbientCoordinatePartial W.val i.val (fun x => D x j) (fun x => T x j) := by
    obtain ⟨T,hT⟩ := hTang hu hf hFlux hWeak hZero i.val (upperCoordinateHalfSpace_invariant i.property)
    refine ⟨T,fun j => ⟨(hT j).1,?_ ,(hT j).2.2⟩⟩
    exact (ambient_lpNorm_le_mul_poisson_size_of_sq (hT j).1 hC (hT j).2.1).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hE)
  choose T hT using hT
  obtain ⟨G,hG⟩ := hFull huW hfW hEq' (B*E) (mul_nonneg (zero_le_one.trans hB) hE)
    (fun j => (ambient_lpNorm_grad_column_le_poisson_size f hD W.val j).trans hBE)
    ((ambient_lpNorm_force_le_poisson_size D hf W.val).trans hBE) T hT
  exact ⟨G,fun j => ⟨(hG j).1,fun i => by simpa only [mul_assoc] using (hG j).2 i⟩⟩

end Thesis
