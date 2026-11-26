module

public import Thesis.MeasureGeometry.HausdorffTwoNullCover
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Small integral cost of smooth cutoffs that remove a compact surface-null seam. -/

public section

noncomputable section

open Filter Function MeasureTheory Metric Set Topology
open scoped ContDiff ENNReal NNReal

namespace Thesis

private theorem one_sub_prod_one_sub_le_sum {ι : Type*} (I : Finset ι) {a : ι → ℝ}
    (ha : ∀ i ∈ I, 0 ≤ a i ∧ a i ≤ 1) :
    1 - (∏ i ∈ I, (1 - a i)) ≤ ∑ i ∈ I, a i := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | insert i I hi hI =>
      have hRest := hI (fun j hj => ha j (Finset.mem_insert_of_mem hj))
      have hAi := ha i (Finset.mem_insert_self _ _)
      have hP : (∏ j ∈ I, (1 - a j)) ≤ 1 :=
        Finset.prod_le_one (fun j hj => sub_nonneg.mpr (ha j (Finset.mem_insert_of_mem hj)).2)
          (fun j hj => sub_le_self _ (ha j (Finset.mem_insert_of_mem hj)).1)
      have hE := mul_le_of_le_one_left (sub_nonneg.mpr hP) (sub_le_self 1 hAi.1)
      rw [Finset.prod_insert hi, Finset.sum_insert hi]
      linarith only [hRest,hE]

private theorem coordDeriv_cutoff_prod_le {ι : Type*} (I : Finset ι)
    {a : ι → Point → ℝ} (ha : ∀ i, ContDiff ℝ ∞ (a i))
    (hRange : ∀ i x, 0 ≤ a i x ∧ a i x ≤ 1) (x : Point) (k : Fin 3) :
    ‖coordDeriv k (fun y => ∏ i ∈ I, (1 - a i y)) x‖ ≤ ∑ i ∈ I, ‖coordDeriv k (a i) x‖ := by
  classical
  let g (i : ι) (y : Point) := 1 - a i y
  have hG (i : ι) : HasFDerivAt (g i) (- fderiv ℝ (a i) x) x :=
    ((ha i).differentiable (by simp) x).hasFDerivAt.const_sub 1
  have hD := (HasFDerivAt.finsetProd (u := I) (fun i _ => hG i)).fderiv
  change ‖(fderiv ℝ (∏ i ∈ I, g i ·) x) (axis k)‖ ≤ _
  rw [hD, sum_apply]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  let b := ∏ j ∈ I.erase i, g j x
  have hb₀ : 0 ≤ b := Finset.prod_nonneg fun j _ => sub_nonneg.mpr (hRange j x).2
  have hb₁ : b ≤ 1 := Finset.prod_le_one
    (fun j _ => sub_nonneg.mpr (hRange j x).2) (fun j _ => sub_le_self _ (hRange j x).1)
  change ‖b * (- fderiv ℝ (a i) x (axis k))‖ ≤ ‖coordDeriv k (a i) x‖
  rw [norm_mul, norm_neg, Real.norm_of_nonneg hb₀]
  exact mul_le_of_le_one_left (norm_nonneg _) hb₁

private theorem norm_integral_bound_of_ball_support {f : Point → ℝ} {c : Point} {r M : ℝ}
    (hf : Continuous f) (hSupport : tsupport f ⊆ closedBall c r) (hM : ∀ x, ‖f x‖ ≤ M) :
    Integrable f ∧ ∫ x, ‖f x‖ ≤ M * volume.real (closedBall c r) := by
  have hK : HasCompactSupport f :=
    (isCompact_closedBall _ _).of_isClosed_subset (isClosed_tsupport _) hSupport
  have hInt : Integrable f := hf.integrable_of_hasCompactSupport hK
  refine ⟨hInt,?_⟩
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := closedBall c r) (f := fun x => ‖f x‖)
    (fun x hx => by rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hSupport h)),norm_zero])]
  have hB : IntegrableOn (fun _ : Point => M) (closedBall c r) volume :=
    integrableOn_const (isCompact_closedBall _ _).measure_lt_top.ne
  calc
    _ ≤ ∫ _ in closedBall c r, M := setIntegral_mono_on hInt.norm.integrableOn hB
      measurableSet_closedBall (fun x _ => hM x)
    _ = _ := by rw [setIntegral_const, smul_eq_mul, mul_comm]

private theorem closedBall_volume_double (c : Point) {r : ℝ} (hr : 0 < r) :
    volume.real (closedBall c (2 * r)) =
      (8 * volume.real (ball (0 : Point) 1)) * r ^ 3 := by
  rw [measureReal_def, Measure.addHaar_closedBall volume c (show 0 ≤ 2*r by positivity),
    ENNReal.toReal_mul, finrank_euclideanSpace_fin,
    ENNReal.toReal_ofReal (by positivity)]
  simp only [measureReal_def]
  ring

/-- The product of ordinary smooth cutoffs that remove a compact
surface-null seam has arbitrarily small (L^1) changes in both its value
and its actual coordinate derivatives. All changes occur within the
prescribed open neighborhood of the seam. -/
theorem exists_cutoff_excluding_hausdorffTwo_null
    {K O : Set Point} (hK : IsCompact K) (h0 : Measure.euclideanHausdorffMeasure 2 K = 0)
    (hO : IsOpen O) (hKO : K ⊆ O) {η : ℝ} (hη : 0 < η) :
    ∃ χ : Point → ℝ, ContDiff ℝ ∞ χ ∧ (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧
      (∀ x ∈ K, χ =ᶠ[𝓝 x] (0 : Point → ℝ)) ∧ (∀ x ∉ O, χ x = 1) ∧
      Integrable (fun x => χ x - 1) ∧ (∫ x, ‖χ x - 1‖) ≤ η ∧
      ∀ j : Fin 3, Integrable (coordDeriv j χ) ∧ (∫ x, ‖coordDeriv j χ x‖) ≤ η := by
  classical
  obtain ⟨δ,hδ,hδO⟩ := hK.exists_thickening_subset_open hO hKO
  let ξ : ContDiffBump (0 : Point) := ⟨1,2,by norm_num,by norm_num⟩
  have hξ : ContDiff ℝ ∞ (ξ : Point → ℝ) := ξ.contDiff
  obtain ⟨L,hLip⟩ := ContDiff.lipschitzWith_of_hasCompactSupport ξ.hasCompactSupport hξ (by simp)
  let V : ℝ := 8 * volume.real (ball (0 : Point) 1)
  have hV : 0 ≤ V := by unfold V; positivity
  let C : ℝ := 1 + V + V * L
  have hC : 0 < C := by positivity
  obtain ⟨ι,I,c,r,hData,hCover,hBudget⟩ :=
    IsCompact.exists_finite_ball_cover_sq_of_hausdorffTwo_zero hK h0 (lt_min zero_lt_one (half_pos hδ))
      (div_pos hη hC)
  let A := (I : Set ι)
  let a (i : A) (x : Point) := ξ ((r i.val)⁻¹ • (x - c i.val))
  have hr (i : A) : 0 < r i.val := (hData i.val i.property).2.1
  have hr₁ (i : A) : r i.val ≤ 1 :=
    (hData i.val i.property).2.2.le.trans (min_le_left _ _)
  have hOut (i : A) : closedBall (c i.val) (2 * r i.val) ⊆ O := by
    intro x hx
    apply hδO
    exact mem_thickening_iff.2 ⟨c i.val,(hData i.val i.property).1,
      (mem_closedBall.mp hx).trans_lt (by
        have h := (hData i.val i.property).2.2.trans_le (min_le_right _ _)
        linarith only [h])⟩
  have hNorm (i : A) (x : Point) :
      dist ((r i.val)⁻¹ • (x - c i.val)) 0 = (r i.val)⁻¹ * dist x (c i.val) := by
    rw [dist_zero_right, norm_smul, dist_eq_norm, Real.norm_of_nonneg (inv_nonneg.mpr (hr i).le)]
  have haC (i : A) : ContDiff ℝ ∞ (a i) := hξ.comp ((contDiff_id.sub contDiff_const).const_smul _)
  have haRange (i : A) (x : Point) : 0 ≤ a i x ∧ a i x ≤ 1 := ⟨ξ.nonneg,ξ.le_one⟩
  have haOne (i : A) (x : Point) (hx : x ∈ ball (c i.val) (r i.val)) : a i x = 1 := by
    apply ξ.one_of_mem_closedBall
    change dist ((r i.val)⁻¹ • (x - c i.val)) 0 ≤ 1
    rw [hNorm]
    exact (mul_le_mul_of_nonneg_left (mem_ball.mp hx).le (inv_nonneg.mpr (hr i).le)).trans_eq
      (inv_mul_cancel₀ (hr i).ne')
  have haSupport (i : A) : tsupport (a i) ⊆ closedBall (c i.val) (2 * r i.val) := by
    apply closure_minimal _ isClosed_closedBall
    intro x hx
    have hs : ((r i.val)⁻¹ • (x - c i.val)) ∈ ball (0 : Point) 2 := by
      exact ξ.support_eq ▸ hx
    apply mem_closedBall.2
    have h := mem_ball.mp hs
    rw [hNorm, ← div_eq_inv_mul] at h
    exact ((div_lt_iff₀ (hr i)).1 h).le
  have haL (i : A) : LipschitzWith (L * Real.toNNReal (r i.val)⁻¹) (a i) := by
    apply hLip.comp
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm, ← smul_sub, sub_sub_sub_cancel_right, norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr (hr i).le), Real.coe_toNNReal _ (inv_nonneg.mpr (hr i).le),
      ← dist_eq_norm]
  have hDerB (i : A) (j : Fin 3) (x : Point) : ‖coordDeriv j (a i) x‖ ≤ (L : ℝ) * (r i.val)⁻¹ := by
    have hAxis : ‖axis j‖ = 1 := by simp [axis]
    refine ((fderiv ℝ (a i) x).le_opNorm _).trans ?_
    rw [hAxis,mul_one, ← Real.coe_toNNReal _ (inv_nonneg.mpr (hr i).le), ← NNReal.coe_mul]
    exact norm_fderiv_le_of_lipschitz ℝ (haL i)
  let χ (x : Point) := ∏ i : A, (1 - a i x)
  have hχ : ContDiff ℝ ∞ χ := contDiff_prod fun i _ => contDiff_const.sub (haC i)
  have hχRange (x : Point) : 0 ≤ χ x ∧ χ x ≤ 1 :=
    ⟨Finset.prod_nonneg fun i _ => sub_nonneg.mpr (haRange i x).2,
      Finset.prod_le_one (fun i _ => sub_nonneg.mpr (haRange i x).2)
        (fun i _ => sub_le_self _ (haRange i x).1)⟩
  have hχZero (x : Point) (hx : x ∈ K) : χ =ᶠ[𝓝 x] (0 : Point → ℝ) := by
    obtain ⟨i,hi,hxI⟩ := mem_iUnion₂.mp (hCover hx)
    let n : A := ⟨i,hi⟩
    filter_upwards [isOpen_ball.mem_nhds hxI] with y hy
    change (∏ j : A, (1 - a j y)) = 0
    exact Finset.prod_eq_zero (Finset.mem_univ n) (by rw [haOne n y hy, sub_self])
  let K' : Set Point := ⋃ i : A, closedBall (c i.val) (2 * r i.val)
  have hK' : IsCompact K' := isCompact_iUnion (fun _ => isCompact_closedBall _ _)
  have hK'O : K' ⊆ O := iUnion_subset hOut
  have hχOne (x : Point) (hx : x ∉ K') : χ x = 1 := by
    apply Finset.prod_eq_one
    intro i _
    have hZ : a i x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (mem_iUnion.2 ⟨i,haSupport i h⟩))
    rw [hZ,sub_zero]
  have hSupp : tsupport (fun x => χ x - 1) ⊆ K' := by
    apply closure_minimal _ hK'.isClosed
    intro x hx
    by_contra hn
    exact hx (by change χ x - 1 = 0; rw [hχOne x hn,sub_self])
  have hχI : Integrable (fun x => χ x - 1) :=
    (hχ.continuous.sub continuous_const).integrable_of_hasCompactSupport
      (hK'.of_isClosed_subset (isClosed_tsupport _) hSupp)
  have hSum : (∑ i : A, r i.val ^ 2) < η / C := by
    change ∑ i ∈ I.attach, r i.val ^ 2 < η / C
    exact (Finset.sum_attach I (fun i : ι => r i ^ 2)).trans_lt hBudget
  have hSumC : C * (∑ i : A, r i.val ^ 2) ≤ η :=
    ((lt_div_iff₀ hC).1 hSum).le.trans_eq' (mul_comm _ _)
  have hBudget' {Q : ℝ} (hQ : Q ≤ C) : Q * (∑ i : A, r i.val ^ 2) ≤ η :=
    (mul_le_mul_of_nonneg_right hQ (Finset.sum_nonneg fun _ _ => sq_nonneg _)).trans hSumC
  refine ⟨χ,hχ,hχRange,hχZero,fun x hx => hχOne x (fun h => hx (hK'O h)),hχI,?_,?_⟩
  · have hA (i : A) := norm_integral_bound_of_ball_support (haC i).continuous (haSupport i)
      (M := 1) (fun x => by rw [Real.norm_of_nonneg (haRange i x).1]; exact (haRange i x).2)
    calc
      _ ≤ ∫ x, ∑ i : A, ‖a i x‖ := integral_mono hχI.norm
        (integrable_finsetSum _ fun i _ => (hA i).1.norm) fun x => by
          rw [norm_sub_rev, Real.norm_of_nonneg (sub_nonneg.mpr (hχRange x).2)]
          have h := one_sub_prod_one_sub_le_sum Finset.univ (fun i _ => haRange i x)
          simpa only [χ, Real.norm_of_nonneg (haRange _ x).1] using h
      _ = ∑ i : A, ∫ x, ‖a i x‖ := integral_finsetSum _ fun i _ => (hA i).1.norm
      _ ≤ ∑ i : A, V * r i.val ^ 2 := Finset.sum_le_sum fun i _ => by
        have hi := (hA i).2
        rw [one_mul,closedBall_volume_double _ (hr i)] at hi
        exact hi.trans (mul_le_mul_of_nonneg_left
          (by rw [pow_succ]; exact mul_le_of_le_one_right (sq_nonneg _) (hr₁ i)) hV)
      _ ≤ _ := by
        rw [← Finset.mul_sum]
        exact hBudget' (by dsimp only [C]; linarith only [mul_nonneg hV L.coe_nonneg])
  · intro j
    have hCj : Continuous (coordDeriv j χ) :=
      (hχ.continuous_fderiv (by simp)).clm_apply continuous_const
    have hSj : tsupport (coordDeriv j χ) ⊆ K' := by
      apply closure_minimal _ hK'.isClosed
      intro x hx
      by_contra hOut
      have hN : ∀ᶠ y in 𝓝 x, y ∉ K' := hK'.isClosed.isOpen_compl.mem_nhds hOut
      have hE : χ =ᶠ[𝓝 x] (fun _ : Point => (1 : ℝ)) := hN.mono hχOne
      have hZ : fderiv ℝ (fun _ : Point => (1 : ℝ)) x = 0 := (hasFDerivAt_const 1 x).fderiv
      exact hx (by unfold coordDeriv; rw [hE.fderiv_eq, hZ, zero_apply])
    have hJ : Integrable (coordDeriv j χ) :=
      hCj.integrable_of_hasCompactSupport (hK'.of_isClosed_subset (isClosed_tsupport _) hSj)
    have hA (i : A) := norm_integral_bound_of_ball_support
      (((haC i).continuous_fderiv (by simp)).clm_apply
        (continuous_const : Continuous (fun _ : Point => axis j)))
      ((tsupport_fderiv_apply_subset ℝ (axis j)).trans (haSupport i)) (hDerB i j)
    refine ⟨hJ,?_⟩
    calc
      _ ≤ ∫ x, ∑ i : A, ‖coordDeriv j (a i) x‖ := integral_mono hJ.norm
        (integrable_finsetSum _ fun i _ => (hA i).1.norm)
        (fun x => coordDeriv_cutoff_prod_le Finset.univ haC haRange x j)
      _ = ∑ i : A, ∫ x, ‖coordDeriv j (a i) x‖ := integral_finsetSum _ fun i _ => (hA i).1.norm
      _ ≤ ∑ i : A, (V * L) * r i.val ^ 2 := Finset.sum_le_sum fun i _ => by
        refine (hA i).2.trans_eq ?_
        rw [closedBall_volume_double _ (hr i)]
        change (L : ℝ) * (r i.val)⁻¹ * (V * r i.val ^ 3) = _
        field_simp [(hr i).ne']
      _ ≤ _ := by
        rw [← Finset.mul_sum]
        exact hBudget' (by dsimp only [C]; linarith only [hV])

end Thesis
