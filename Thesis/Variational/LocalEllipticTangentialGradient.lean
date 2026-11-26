module

public import Thesis.Variational.LocalDifferenceQuotientTest
public import Thesis.Upstream.AmbientMetricWeakEquation
public import Thesis.Upstream.WeakDifferenceQuotientLimit
import Mathlib.Analysis.Calculus.BumpFunction.Basic

/-! The actual second weak columns in the directions preserving the boundary side. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set
open scoped BigOperators ContDiff ENNReal NNReal Topology RealInnerProductSpace

namespace Thesis

private theorem exists_cutoff_coordinate_square_bound {n : ℕ}
    {χ : Domain n → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) :
    ∃ H : ℝ, ∀ x, ∑ j : Fin n, (2*(fderiv ℝ χ x (EuclideanSpace.single j 1)))^2 ≤ H^2 := by
  have hK := hcχ.fderiv ℝ
  obtain ⟨M,hM⟩ := hK.exists_bound_of_continuousOn (hχ.continuous_fderiv (by simp)).continuousOn
  let L := max M 0
  have hL : 0 ≤ L := le_max_right _ _
  have hN (x : Domain n) : ‖fderiv ℝ χ x‖ ≤ L := by
    by_cases hx : x ∈ tsupport (fderiv ℝ χ)
    · exact (hM x hx).trans (le_max_left _ _)
    · rw [image_eq_zero_of_notMem_tsupport hx,norm_zero]
      exact hL
  refine ⟨2*((n : ℝ)+1)*L,fun x => ?_⟩
  calc
    _ ≤ ∑ _j : Fin n, (2*L)^2 := by
      apply Finset.sum_le_sum
      intro j _
      have hDj : |(fderiv ℝ χ x) (EuclideanSpace.single j 1)| ≤ L := by
        have ht := ((fderiv ℝ χ x).le_opNorm (EuclideanSpace.single j 1)).trans
          (by rw [PiLp.norm_single,norm_one,mul_one])
        exact (by simpa only [Real.norm_eq_abs] using ht : |(fderiv ℝ χ x) (EuclideanSpace.single j 1)| ≤ ‖fderiv ℝ χ x‖).trans (hN x)
      have habs : |2*(fderiv ℝ χ x (EuclideanSpace.single j 1))| ≤ 2*L := by
        rw [abs_mul,abs_of_nonneg (by norm_num : 0 ≤ (2 : ℝ))]
        exact mul_le_mul_of_nonneg_left hDj (by norm_num)
      exact (sq_le_sq).2 (habs.trans_eq (abs_of_nonneg (by positivity)).symm)
    _ = (n : ℝ)*(2*L)^2 := by simp [nsmul_eq_mul]
    _ ≤ _ := by
      have hn : (n : ℝ) ≤ ((n : ℝ)+1)^2 := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
      have h := mul_le_mul_of_nonneg_right hn (sq_nonneg (2*L))
      nlinarith only [h]

private theorem norm_coefficient_differenceQuotient_le {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A : Domain n → E} {K : Set (Domain n)} {L : ℝ≥0} (hL : LipschitzOnWith L A K)
    {x : Domain n} (hx : x ∈ K) (i : Fin n) {h : ℝ} (hh : 0 < h)
    (hy : x+h • EuclideanSpace.single i 1 ∈ K) :
    ‖ambientDifferenceQuotient i h A x‖ ≤ L := by
  have hd : dist (x+h • EuclideanSpace.single i 1) x = h := by
    rw [dist_eq_norm,add_sub_cancel_left,norm_smul_euclideanAxis_eq_abs,abs_of_pos hh]
  have he := hL.dist_le_mul _ hy _ hx
  rw [hd,dist_eq_norm] at he
  rw [ambientDifferenceQuotient,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hh.le)]
  exact (mul_le_mul_of_nonneg_left he (inv_nonneg.mpr hh.le)).trans_eq
    (by rw [mul_left_comm,inv_mul_cancel₀ hh.ne',mul_one])

/-- A tangential direction preserving the side has a weak second derivative
on each measurable subset of the smaller ball, including across the wall. -/
theorem exists_local_second_weak_column_invariant_direction_on_subset {n q : ℕ}
    {a : Domain n} {R ell : ℝ} (hR : 0 < R) (hell : 0 < ell)
    (S : OpenDomain n) (hConvex : Convex ℝ S.val) (hn : (ball a R ∩ S.val).Nonempty)
    (A : Domain n → AmbientGradientHilbert n q →L[ℝ] AmbientGradientHilbert n q)
    (hA : ContDiff ℝ ∞ A)
    (hEll : ∀ x ∈ closedBall a R, ∀ y : AmbientGradientHilbert n q,
      ell*‖y‖^2 ≤ inner ℝ (A x y) y) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {u f : Domain n → Ambient q} {D : Domain n → HarmonicMaps.Gradient n q},
      MemW12 (⟨univ,isOpen_univ⟩ : OpenDomain n) u D →
      MemLp f 2 volume →
      MemLp (fun x => A x (packAmbientGradient (D x))) 2 volume →
      HasWeakPackedDivergenceEq (ball a R ∩ S.val) (fun x => A x (packAmbientGradient (D x))) f →
      (∀ x ∈ ball a R, x ∉ S.val → u x = 0 ∧ D x = 0) →
      ∀ i : Fin n, (∀ x : Domain n, ∀ t : ℝ,
        x+t • EuclideanSpace.single i 1 ∈ S.val ↔ x ∈ S.val) →
      ∀ W : Set (Domain n), MeasurableSet W → W ⊆ ball a (R/4) →
      ∃ E : Domain n → HarmonicMaps.Gradient n q,
        ∀ j : Fin n, MemLp (fun x => E x j) 2 (volume.restrict W) ∧
          (∫ x in W, ‖E x j‖^2) ≤
            C*((∫ x, hsNormSq (D x)) + ∫ x, ‖f x‖^2) ∧
          IsWeakAmbientCoordinatePartial W i (fun x => D x j) (fun x => E x j) := by
  let b : ContDiffBump a := ⟨R/4,R/2,by positivity,by linarith only [hR]⟩
  let χ : Domain n → ℝ := b
  have hχ : ContDiff ℝ ∞ χ := b.contDiff
  have hcχ : HasCompactSupport χ := b.hasCompactSupport
  have hχSupp : tsupport χ ⊆ closedBall a (R/2) := b.tsupport_eq.le
  have hχB (x : Domain n) : |χ x| ≤ 1 := by
    rw [abs_of_nonneg (b.nonneg' x)]
    exact b.le_one
  have hχ1 (x : Domain n) (hx : x ∈ ball a (R/4)) : χ x = 1 :=
    b.one_of_mem_closedBall (ball_subset_closedBall hx)
  obtain ⟨H,hχD⟩ := exists_cutoff_coordinate_square_bound hχ hcχ
  obtain ⟨M,hM⟩ := (isCompact_closedBall a R).exists_bound_of_continuousOn hA.continuous.continuousOn
  obtain ⟨L₀,hL₀⟩ := (isCompact_closedBall a R).exists_bound_of_continuousOn
    (hA.continuous_fderiv (by simp)).continuousOn
  let L : ℝ≥0 := ⟨max L₀ 0,le_max_right _ _⟩
  have hLA : LipschitzOnWith L A (closedBall a R) :=
    (convex_closedBall a R).lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
      (fun x _ => (hA.differentiable (by simp)) x)
      (fun x hx => (hL₀ x hx).trans (le_max_left _ _))
  obtain ⟨C,hC,hEstimate⟩ := cutoff_differenceQuotient_gradient_bound (n := n) (q := q) ell M (L : ℝ) H hell
  refine ⟨C,hC,?_⟩
  intro u f D hu hf hFlux hWeak hZero i hStay W hW hWB
  let V : OpenDomain n := ⟨ball a R ∩ S.val,isOpen_ball.inter S.property⟩
  letI : IsFiniteMeasure ((volume : Measure (Domain n)).restrict W) :=
    isFiniteMeasure_restrict.mpr (ne_top_of_le_ne_top measure_ball_ne_top
      (measure_mono hWB))
  have hFluxMain (h : ℝ) (hp : 0 < h) (hsmall : h < R/2) :
      (∫ x, ‖χ x • ambientDifferenceQuotient i h (fun y => packAmbientGradient (D y)) x‖^2) ≤
        C*((∫ x, hsNormSq (D x)) + ∫ x, ‖f x‖^2) := by
    have habs : |h| < R/2 := by rwa [abs_of_pos hp]
    let v := ambientDifferenceQuotient i (-h) (differenceQuotientTestValue χ i h u)
    let G (x : Domain n) (j : Fin n) :=
      ambientDifferenceQuotient i (-h) (fun y => differenceQuotientTestColumns χ i h u D y j) x
    obtain ⟨hv,hOff⟩ := zeroBoundary_differenceQuotient_test_in_ball_part
      hR S hConvex hn hχ hcχ hχSupp hu hZero i h habs hStay
    have hI₁ : V.val.indicator v = v := indicator_eq_self.mpr
      (fun x hx => of_not_not fun h => hx (hOff x h).1)
    have hI₂ : V.val.indicator G = G := indicator_eq_self.mpr
      (fun x hx => of_not_not fun h => hx (hOff x h).2)
    have hPair := HasWeakPackedDivergenceEq.of_zeroBoundary_test hWeak hFlux hf hv
    rw [hI₁,hI₂] at hPair
    have hPair' :
        (∫ x, inner ℝ (A x (packAmbientGradient (D x)))
            (ambientDifferenceQuotient i (-h)
              (fun y => packAmbientGradient (differenceQuotientTestColumns χ i h u D y)) x)) =
          -(∫ x, inner ℝ (f x) (v x)) := by
      simpa only [G,packAmbientGradient_differenceQuotient] using hPair
    have hBig (x : Domain n) (hx : χ x ≠ 0) :
        x ∈ closedBall a (R/2) ∧ x+h • EuclideanSpace.single i 1 ∈ ball a R := by
      have hS : x ∈ tsupport χ := subset_closure hx
      exact ⟨hχSupp hS,mem_ball_add_scaled_axis (hχSupp hS) i habs⟩
    apply hEstimate hu hf A hFlux χ hχ hcχ hχB hχD i h hp.ne' ?_ ?_ hPair'
    · intro x hx
      obtain ⟨hx₁,hx₂⟩ := hBig x hx
      have hx₁' : x ∈ closedBall a R := closedBall_subset_closedBall (half_le_self hR.le) hx₁
      have hx₂' := ball_subset_closedBall hx₂
      exact ⟨hM _ hx₂',norm_coefficient_differenceQuotient_le hLA hx₁' i hp hx₂'⟩
    · intro x hx
      exact hEll _ (ball_subset_closedBall (hBig x hx).2)
  let t (k : ℕ) := (R/4)*(1/((k : ℝ)+1))
  have htl : Tendsto t atTop (𝓝 0) := by
    simpa only [t,mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (R/4)
  have htP (k : ℕ) : 0 < t k := by dsimp only [t]; positivity
  have htSmall (k : ℕ) : t k < R/2 := by
    refine (mul_le_of_le_one_right (by positivity : 0 ≤ R/4) ?_).trans_lt (by linarith only [hR])
    exact (div_le_one (by positivity : 0 < (k : ℝ)+1)).mpr (by linarith only [Nat.cast_nonneg (α := ℝ) k])
  have hD (j : Fin n) : MemLp (fun x => D x j) 2 (volume : Measure (Domain n)) := by
    simpa only [Measure.restrict_univ] using hu.2.2 j
  have hPack : MemLp (fun x => packAmbientGradient (D x)) 2 (volume : Measure (Domain n)) :=
    memLp_packAmbientGradient hD
  have hV (k : ℕ) : MemLp
      (fun x => χ x • ambientDifferenceQuotient i (t k) (fun y => packAmbientGradient (D y)) x)
        2 (volume : Measure (Domain n)) :=
    (memLp_ambientDifferenceQuotient hPack i (t k)).smul (r := (2 : ℝ≥0∞))
      (b.continuous.memLp_top_of_hasCompactSupport hcχ volume)
  let N := C*((∫ x, hsNormSq (D x)) + ∫ x, ‖f x‖^2)
  have hN : 0 ≤ N := mul_nonneg hC (add_nonneg (integral_nonneg fun _ => hsNormSq_nonneg _)
    (integral_nonneg fun _ => sq_nonneg _))
  have hSq (j : Fin n) (k : ℕ) : (∫ x in W, ‖ambientDifferenceQuotient i (t k) (fun y => D y j) x‖^2) ≤ N := by
    let qj := ambientDifferenceQuotient i (t k) (fun y => D y j)
    let Q (x : Domain n) := χ x • ambientDifferenceQuotient i (t k) (fun y => packAmbientGradient (D y)) x
    have hjLp := memLp_ambientDifferenceQuotient (hD j) i (t k)
    have hi := (memLp_two_iff_integrable_sq_norm (hV k).1).mp (hV k)
    calc
      _ ≤ ∫ x in W, ‖Q x‖^2 := by
        apply integral_mono_ae ((memLp_two_iff_integrable_sq_norm hjLp.1).mp hjLp).integrableOn hi.integrableOn
        filter_upwards [ae_restrict_mem (μ := volume) hW] with x hx
        apply pow_le_pow_left₀ (norm_nonneg _)
        have he : Q x = packAmbientGradient (fun l => ambientDifferenceQuotient i (t k) (fun y => D y l) x) := by
          dsimp only [Q]
          rw [hχ1 x (hWB hx),one_smul,← packAmbientGradient_differenceQuotient]
        change ‖qj x‖ ≤ ‖Q x‖
        rw [he]
        simpa only [packAmbientGradient_apply,qj] using
          PiLp.norm_apply_le (packAmbientGradient
            (fun l => ambientDifferenceQuotient i (t k) (fun y => D y l) x)) j
      _ ≤ ∫ x, ‖Q x‖^2 := setIntegral_le_integral hi (Eventually.of_forall fun _ => sq_nonneg _)
      _ ≤ _ := hFluxMain (t k) (htP k) (htSmall k)
  have hExists (j : Fin n) :
      ∃ g : Domain n → Ambient q, MemLp g 2 (volume.restrict W) ∧
        (∫ x in W, ‖g x‖^2) ≤ N ∧ IsWeakAmbientCoordinatePartial W i (fun x => D x j) g := by
    obtain ⟨g,hg,hgN,hgW⟩ :=
      exists_weakAmbientCoordinatePartial_of_differenceQuotient_bound (hD j) i htl
        (fun k => (htP k).ne') (Real.sqrt_nonneg N)
        (fun k => (hSq j k).trans_eq (Real.sq_sqrt hN).symm)
    exact ⟨g,hg,hgN.trans_eq (Real.sq_sqrt hN),hgW⟩
  choose G hG using hExists
  exact ⟨fun x j => G j x,fun j => hG j⟩

/-- The tangential difference estimate gives a weak derivative of every
original first derivative column on the smaller ball part. The same theorem
applies to a whole interior ball by taking the side to be the entire space. -/
theorem exists_local_second_weak_column_invariant_direction {n q : ℕ}
    {a : Domain n} {R ell : ℝ} (hR : 0 < R) (hell : 0 < ell)
    (S : OpenDomain n) (hConvex : Convex ℝ S.val) (hn : (ball a R ∩ S.val).Nonempty)
    (A : Domain n → AmbientGradientHilbert n q →L[ℝ] AmbientGradientHilbert n q)
    (hA : ContDiff ℝ ∞ A)
    (hEll : ∀ x ∈ closedBall a R, ∀ y : AmbientGradientHilbert n q,
      ell*‖y‖^2 ≤ inner ℝ (A x y) y) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {u f : Domain n → Ambient q} {D : Domain n → HarmonicMaps.Gradient n q},
      MemW12 (⟨univ,isOpen_univ⟩ : OpenDomain n) u D →
      MemLp f 2 volume →
      MemLp (fun x => A x (packAmbientGradient (D x))) 2 volume →
      HasWeakPackedDivergenceEq (ball a R ∩ S.val) (fun x => A x (packAmbientGradient (D x))) f →
      (∀ x ∈ ball a R, x ∉ S.val → u x = 0 ∧ D x = 0) →
      ∀ i : Fin n, (∀ x : Domain n, ∀ t : ℝ,
        x+t • EuclideanSpace.single i 1 ∈ S.val ↔ x ∈ S.val) →
      ∃ E : Domain n → HarmonicMaps.Gradient n q,
        ∀ j : Fin n, MemLp (fun x => E x j) 2 (volume.restrict (ball a (R/4) ∩ S.val)) ∧
          (∫ x in ball a (R/4) ∩ S.val, ‖E x j‖^2) ≤
            C*((∫ x, hsNormSq (D x)) + ∫ x, ‖f x‖^2) ∧
          IsWeakAmbientCoordinatePartial (ball a (R/4) ∩ S.val) i (fun x => D x j) (fun x => E x j) := by
  obtain ⟨C,hC,hEstimate⟩ :=
    exists_local_second_weak_column_invariant_direction_on_subset hR hell S hConvex hn A hA hEll
  refine ⟨C,hC,?_⟩
  intro u f D hu hf hFlux hWeak hZero i hStay
  exact hEstimate hu hf hFlux hWeak hZero i hStay _
    (isOpen_ball.inter S.property).measurableSet inter_subset_left

end Thesis
