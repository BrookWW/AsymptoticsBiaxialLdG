/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license, reproduced in SupportingAnalysis/Apache-2.0.txt.
The graph lift and its supporting estimates adapt TauCeti commit
aa3cfad1274c06cff25f2b58848498b3c3f68d0f, AreaFormula/Basic.lean,
AreaFormula/Lipschitz.lean, and InnerProductSpace/NormDet.lean.
-/
module

public import SupportingAnalysis.Basics
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.Jacobian

/-! Bounded Borel bi-Lipschitz charts of Euclidean countably rectifiable sets. -/

public section

open MeasureTheory Measure Metric Set Filter Function Module Bornology
open scoped ENNReal NNReal Topology MeasureTheory

set_option autoImplicit false

namespace SupportingAnalysis

variable {U V : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [FiniteDimensional ℝ U] [MeasurableSpace U] [BorelSpace U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V]

omit [MeasurableSpace U] [BorelSpace U] [MeasurableSpace V] [BorelSpace V] in
private theorem continuous_normDet :
    Continuous (fun A : U →L[ℝ] V => A.normDet) := by
  let b := stdOrthonormalBasis ℝ U
  have h (A : U →L[ℝ] V) : A.normDet = √(Matrix.gram ℝ fun i => A (b i)).det := by
    have hsq := (A : U →ₗ[ℝ] V).normDet_sq_eq_det_gram b
    simp only [RCLike.ofReal_real_eq_id, id] at hsq
    exact (hsq ▸ Real.sqrt_sq A.normDet_nonneg).symm
  simp_rw [h]
  refine Continuous.sqrt (Continuous.matrix_det (continuous_matrix fun i j => ?_))
  simp only [Matrix.gram_apply]
  fun_prop

omit [InnerProductSpace ℝ U] [FiniteDimensional ℝ U] [InnerProductSpace ℝ V] in
private theorem euclideanHausdorffMeasure_image_le_of_lipschitzOn {f : U → V}
    {s : Set U} {K : ℝ≥0} (hf : LipschitzOnWith K f s) (d : ℕ) :
    μHE[d] (f '' s) ≤ (K : ℝ≥0∞) ^ d * μHE[d] s := by
  simp only [euclideanHausdorffMeasure_def, Measure.smul_apply, nnreal_smul_coe_apply]
  rw [mul_left_comm, ← ENNReal.rpow_natCast]
  exact mul_le_mul_right (hf.hausdorffMeasure_image_le d.cast_nonneg) _

private theorem euclideanHausdorffMeasure_image_le_of_approximation [FiniteDimensional ℝ V] {f : U → V}
    {A : U →L[ℝ] V} {s : Set U} {δ K : ℝ≥0}
    (hf : ApproximatesLinearOn f A s δ) (hA : AntilipschitzWith K A) :
    μHE[finrank ℝ U] (f '' s) ≤
      ((1 + δ * K) ^ finrank ℝ U : ℝ≥0) * (ENNReal.ofReal A.normDet * volume s) := by
  let g : V → V := f ∘ invFun A
  have hg (x : U) : g (A x) = f x := by
    exact congrArg f (leftInverse_invFun hA.injective x)
  have himage : f '' s = g '' (A '' s) := by rw [image_image]; simp only [hg]
  have hlip : LipschitzOnWith (1 + δ * K) g (A '' s) := by
    refine LipschitzOnWith.of_dist_le_mul ?_
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    have hxy : ‖x - y‖ ≤ K * ‖A x - A y‖ := by
      simpa [dist_eq_norm] using hA.le_mul_dist x y
    rw [hg, hg, dist_eq_norm, dist_eq_norm, NNReal.coe_add, NNReal.coe_one, NNReal.coe_mul]
    calc ‖f x - f y‖ = ‖(A x - A y) + (f x - f y - A (x - y))‖ := by rw [map_sub]; abel_nf
      _ ≤ ‖A x - A y‖ + ‖f x - f y - A (x - y)‖ := norm_add_le _ _
      _ ≤ ‖A x - A y‖ + δ * (K * ‖A x - A y‖) := by
        gcongr
        exact (hf x hx y hy).trans (by gcongr)
      _ = (1 + δ * K) * ‖A x - A y‖ := by ring
  rw [himage, ENNReal.coe_pow,
    ← (A : U →ₗ[ℝ] V).euclideanHausdorffMeasure_image_eq_normDet_mul_volume]
  exact euclideanHausdorffMeasure_image_le_of_lipschitzOn hlip _

private theorem euclideanHausdorffMeasure_image_le_of_uniform_normDet
    [FiniteDimensional ℝ V] {g : U → V} {s : Set U} (hs : MeasurableSet s) (hne : s.Nonempty)
    {A : U → U →L[ℝ] V} {ε : ℝ≥0} (hε : 0 < ε) {τ : ℝ}
    (hDiff : ∀ x ∈ s, HasFDerivWithinAt g (A x) s x)
    (hAnti : ∀ x ∈ s, AntilipschitzWith ε⁻¹ (A x))
    (hDet : ∀ x ∈ s, (A x).normDet ≤ τ) :
    μHE[finrank ℝ U] (g '' s) ≤
      (((2 : ℝ≥0∞) ^ finrank ℝ U) * ENNReal.ofReal τ) * volume s := by
  obtain ⟨t, T, hDisj, hMeas, hcover, hApprox, hT⟩ :=
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt g s A hDiff (fun _ => ε)
      (fun _ => hε.ne')
  let C : ℝ≥0∞ := ((2 : ℝ≥0∞) ^ finrank ℝ U) * ENNReal.ofReal τ
  have hPiece (n : ℕ) : μHE[finrank ℝ U] (g '' (s ∩ t n)) ≤ C * volume (s ∩ t n) := by
    obtain ⟨y, hy, hTy⟩ := hT hne n
    have hApprox' : ApproximatesLinearOn g (A y) (s ∩ t n) ε := hTy ▸ hApprox n
    refine (euclideanHausdorffMeasure_image_le_of_approximation hApprox' (hAnti y hy)).trans ?_
    rw [mul_inv_cancel₀ hε.ne', one_add_one_eq_two, ENNReal.coe_pow, ENNReal.coe_ofNat, ← mul_assoc]
    exact mul_le_mul_left (mul_le_mul_right (ENNReal.ofReal_le_ofReal (hDet y hy)) _) _
  have hUnion : s = ⋃ n, s ∩ t n := by
    rw [← inter_iUnion]
    exact (inter_eq_left.mpr hcover).symm
  calc
    _ ≤ ∑' n, μHE[finrank ℝ U] (g '' (s ∩ t n)) := by
      conv_lhs => rw [hUnion, image_iUnion]
      exact measure_iUnion_le _
    _ ≤ ∑' n, C * volume (s ∩ t n) := ENNReal.tsum_le_tsum hPiece
    _ = C * volume s := by
      rw [ENNReal.tsum_mul_left, ← measure_iUnion
        (fun i j hij => (hDisj hij).mono inter_subset_right inter_subset_right)
        (fun n => hs.inter (hMeas n)), ← hUnion]

omit [MeasurableSpace U] [BorelSpace U] [MeasurableSpace V] [BorelSpace V] in
private theorem exists_uniform_small_normDet [FiniteDimensional ℝ V]
    {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    (ι₁ : V →L[ℝ] W) (ι₂ : U →L[ℝ] W) (K : ℝ) {τ : ℝ} (hτ : 0 < τ) :
    ∃ ε > (0 : ℝ), ∀ A : U →L[ℝ] V, ‖A‖ ≤ K → A.normDet = 0 →
      (ι₁ ∘L A + ε • ι₂).normDet ≤ τ := by
  let D (a : ℝ × (U →L[ℝ] V)) := ι₁ ∘L a.2 + a.1 • ι₂
  let S := Icc (0 : ℝ) 1 ×ˢ closedBall (0 : U →L[ℝ] V) K
  have hD : Continuous D :=
    (continuous_const.clm_comp continuous_snd).add (continuous_fst.smul continuous_const)
  have hS : IsCompact S := isCompact_Icc.prod (isCompact_closedBall _ _)
  have hu := hS.uniformContinuousOn_of_continuous (continuous_normDet.comp hD).continuousOn
  obtain ⟨η, hη, hUC⟩ := Metric.uniformContinuousOn_iff.mp hu τ hτ
  let ε := min 1 (η / 2)
  have hε : 0 < ε := lt_min zero_lt_one (half_pos hη)
  refine ⟨ε, hε, fun A hA hZero => ?_⟩
  have hA' : A ∈ closedBall (0 : U →L[ℝ] V) K :=
    mem_closedBall_zero_iff.mpr hA
  have h1 : (ε, A) ∈ S := ⟨⟨hε.le, min_le_left _ _⟩, hA'⟩
  have h0 : ((0 : ℝ), A) ∈ S := ⟨⟨le_rfl, zero_le_one⟩, hA'⟩
  have hDist : dist (ε, A) ((0 : ℝ), A) < η := by
    rw [Prod.dist_eq, dist_self, Real.dist_eq, sub_zero, abs_of_pos hε, max_eq_left hε.le]
    exact (min_le_right _ _).trans_lt (half_lt_self hη)
  have h := hUC _ h1 _ h0 hDist
  have hZeroD : (D (0, A)).normDet = 0 := by
    change ((ι₁ ∘L A + (0 : ℝ) • ι₂ : U →L[ℝ] W) : U →ₗ[ℝ] W).normDet = 0
    simp [LinearMap.normDet_comp, hZero]
  change dist (D (ε, A)).normDet (D (0, A)).normDet < τ at h
  rw [hZeroD, Real.dist_eq, sub_zero, abs_of_nonneg (D (ε, A)).normDet_nonneg] at h
  exact h.le

private theorem euclideanHausdorffMeasure_image_eq_zero_of_rank_deficient
    [FiniteDimensional ℝ V] {f : U → V} {s : Set U} {K : ℝ≥0}
    (hf : LipschitzWith K f) (hs : MeasurableSet s) (hfin : (volume : Measure U) s < ⊤)
    (hDiff : ∀ x ∈ s, DifferentiableAt ℝ f x)
    (hRank : ∀ x ∈ s, (fderiv ℝ f x).normDet = 0) :
    μHE[finrank ℝ U] (f '' s) = 0 := by
  classical
  by_cases hne : s.Nonempty
  · let ι₁ : V →L[ℝ] WithLp 2 (V × U) :=
      (WithLp.prodContinuousLinearEquiv 2 ℝ V U).symm.toContinuousLinearMap ∘L
        ContinuousLinearMap.inl ℝ V U
    let ι₂ : U →L[ℝ] WithLp 2 (V × U) :=
      (WithLp.prodContinuousLinearEquiv 2 ℝ V U).symm.toContinuousLinearMap ∘L
        ContinuousLinearMap.inr ℝ V U
    have hArea (τ : ℝ) (hτ : 0 < τ) :
        μHE[finrank ℝ U] (f '' s) ≤ ENNReal.ofReal τ * (2 ^ finrank ℝ U * volume s) := by
      obtain ⟨ε, hε, hsmall⟩ := exists_uniform_small_normDet ι₁ ι₂ (K : ℝ) hτ
      let g (x : U) := ι₁ (f x) + ε • ι₂ x
      let D (x : U) : U →L[ℝ] WithLp 2 (V × U) := ι₁ ∘L fderiv ℝ f x + ε • ι₂
      have hg (x : U) (hx : x ∈ s) : HasFDerivWithinAt g (D x) s x :=
        ((ι₁.hasFDerivAt.comp x (hDiff x hx).hasFDerivAt).add
          (ι₂.hasFDerivAt.const_smul ε)).hasFDerivWithinAt
      let ε₀ := Real.toNNReal ε
      have hε₀ : 0 < ε₀ := Real.toNNReal_pos.mpr hε
      have hε₀coe : (ε₀ : ℝ) = ε := Real.coe_toNNReal _ hε.le
      have hAnti (x : U) : AntilipschitzWith ε₀⁻¹ (D x) := by
        apply AntilipschitzWith.of_le_mul_dist
        intro y z
        rw [dist_eq_norm, dist_eq_norm, ← map_sub]
        have h := WithLp.norm_snd_le V (D x (y - z))
        have hSnd : (D x (y - z)).snd = ε • (y - z) := by simp [D, ι₁, ι₂]
        rw [hSnd, norm_smul, Real.norm_eq_abs, abs_of_pos hε] at h
        rw [NNReal.coe_inv, hε₀coe]
        rw [inv_mul_eq_div]
        exact (le_div_iff₀ hε).mpr (by simpa only [mul_comm] using h)
      have hBound := euclideanHausdorffMeasure_image_le_of_uniform_normDet hs hne hε₀ hg
        (fun x _ => hAnti x)
        (fun x hx => hsmall (fderiv ℝ f x) (norm_fderiv_le_of_lipschitz ℝ hf) (hRank x hx))
      let proj : WithLp 2 (V × U) → V := WithLp.fst
      have hp : LipschitzWith 1 proj := LipschitzWith.of_edist_le WithLp.edist_fst_le
      have hfg (x : U) : proj (g x) = f x := by simp [proj, g, ι₁, ι₂]
      have himage : f '' s = proj '' (g '' s) := by rw [image_image]; simp only [hfg]
      calc
        _ ≤ μHE[finrank ℝ U] (g '' s) := by
          rw [himage]
          simpa using euclideanHausdorffMeasure_image_le_of_lipschitzOn hp.lipschitzOnWith (finrank ℝ U)
        _ ≤ _ := hBound
        _ = ENNReal.ofReal τ * (2 ^ finrank ℝ U * volume s) := by ac_rfl
    have hfac : (2 : ℝ≥0∞) ^ finrank ℝ U * volume s ≠ ⊤ :=
      ENNReal.mul_ne_top (by finiteness) hfin.ne
    have hlim : Tendsto (fun τ : ℝ => ENNReal.ofReal τ * (2 ^ finrank ℝ U * volume s))
        (𝓝[>] 0) (𝓝 0) := by
      simpa only [ENNReal.ofReal_zero, zero_mul] using ENNReal.Tendsto.mul_const
        ((ENNReal.continuous_ofReal.continuousAt (x := (0 : ℝ))).tendsto.mono_left
          nhdsWithin_le_nhds) (Or.inr hfac)
    exact le_antisymm (ge_of_tendsto hlim (eventually_nhdsWithin_of_forall hArea)) bot_le
  · simp [not_nonempty_iff_eq_empty.mp hne]

private theorem hausdorffMeasure_zero_iff_euclidean {m d : ℕ} (s : Set (E m)) :
    μH[(d : ℝ)] s = 0 ↔ μHE[d] s = 0 := by
  rw [euclideanHausdorffMeasure_def, Measure.smul_apply, nnreal_smul_coe_apply, mul_eq_zero]
  have h := addHaarScalarFactor_volume_hausdorffMeasure_ne_zero d
  simp only [ENNReal.coe_eq_zero, h, false_or]

private theorem exists_regular_bilipschitz_cover_of_lipschitz {m d : ℕ} {f : E d → E m} {K : ℝ≥0}
    (hf : LipschitzWith K f) :
    ∃ A : ℕ → Set (E d), (∀ n, MeasurableSet (A n)) ∧ (∀ n, IsBounded (A n)) ∧
      (∀ n, ∃ L : ℝ≥0, AntilipschitzWith L ((A n).restrict f)) ∧
      (∀ n x, x ∈ A n → DifferentiableAt ℝ f x ∧ Function.Injective (fderiv ℝ f x)) ∧
      μH[(d : ℝ)] (range f \ ⋃ n, f '' A n) = 0 := by
  classical
  let J (x : E d) := (fderiv ℝ f x).normDet
  let G := {x | DifferentiableAt ℝ f x ∧ J x ≠ 0}
  have hMeasJ : Measurable J := continuous_normDet.measurable.comp (measurable_fderiv ℝ f)
  have hG : MeasurableSet G :=
    (measurableSet_of_differentiableAt ℝ f).inter (measurableSet_eq_fun hMeasJ measurable_const).compl
  have hInj (x : E d) (hx : x ∈ G) : Function.Injective (fderiv ℝ f x) :=
    ((LinearMap.normDet_ne_zero_tfae (fderiv ℝ f x).toLinearMap).out 0 4).mp hx.2
  have hGood (x : E d) (hx : x ∈ G) : DifferentiableAt ℝ f x ∧ Function.Injective (fderiv ℝ f x) :=
    ⟨hx.1, hInj x hx⟩
  have hBad : μHE[d] (f '' Gᶜ) = 0 := by
    let N := {x | ¬ DifferentiableAt ℝ f x}
    let R (k : ℕ) := {x | DifferentiableAt ℝ f x ∧ J x = 0} ∩ closedBall (0 : E d) k
    have hN : (volume : Measure (E d)) N = 0 :=
      ae_iff.mp (hf.ae_differentiableAt (μ := volume))
    have hN' : μHE[d] (f '' N) = 0 := by
      refine le_antisymm (le_trans (euclideanHausdorffMeasure_image_le_of_lipschitzOn
        hf.lipschitzOnWith d) ?_) bot_le
      rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume, hN, mul_zero]
    have hR (k : ℕ) : μHE[d] (f '' R k) = 0 := by
      have hRmeas : MeasurableSet (R k) :=
        ((measurableSet_of_differentiableAt ℝ f).inter (measurableSet_eq_fun hMeasJ measurable_const)).inter
          measurableSet_closedBall
      have hRfin : (volume : Measure (E d)) (R k) < ⊤ :=
        (measure_mono (show R k ⊆ closedBall 0 (k : ℝ) from inter_subset_right)).trans_lt
          measure_closedBall_lt_top
      simpa only [finrank_euclideanSpace_fin] using
        euclideanHausdorffMeasure_image_eq_zero_of_rank_deficient hf hRmeas hRfin
          (fun x hx => hx.1.1) (fun x hx => hx.1.2)
    apply measure_mono_null _ (measure_union_null hN' (measure_iUnion_null hR))
    rintro y ⟨x, hx, rfl⟩
    by_cases hd : DifferentiableAt ℝ f x
    · have hJ : J x = 0 := by
        by_contra h
        exact hx ⟨hd, h⟩
      obtain ⟨k, hk⟩ := exists_nat_ge ‖x‖
      have hmem : x ∈ R k := ⟨⟨hd, hJ⟩, by simpa only [mem_closedBall, dist_zero_right] using hk⟩
      exact Or.inr (mem_iUnion.mpr ⟨k, mem_image_of_mem f hmem⟩)
    · exact Or.inl (mem_image_of_mem f hd)
  have hK (T : E d →L[ℝ] E m) : ∃ L : ℝ≥0, 0 < L ∧
      (Function.Injective T → AntilipschitzWith L T) := by
    by_cases h : Function.Injective T
    · obtain ⟨L, hL, hAnti⟩ := T.toLinearMap.injective_iff_antilipschitz.mp h
      exact ⟨L, hL, fun _ => hAnti⟩
    · exact ⟨1, zero_lt_one, fun h' => (h h').elim⟩
  choose L hL hAntiL using hK
  let e (T : E d →L[ℝ] E m) : ℝ≥0 := (L T)⁻¹ / 2
  have he (T : E d →L[ℝ] E m) : 0 < e T := div_pos (inv_pos.mpr (hL T)) (by norm_num)
  obtain ⟨t, T, _, ht, hcover, hApprox, hT⟩ :=
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt f G (fderiv ℝ f)
      (fun x hx => hx.1.hasFDerivAt.hasFDerivWithinAt) e (fun A => (he A).ne')
  let P (i j : ℕ) := (G ∩ t i) ∩ closedBall (0 : E d) j
  let A (n : ℕ) := P (Nat.unpair n).1 (Nat.unpair n).2
  have hSub (n : ℕ) : A n ⊆ G := inter_subset_left.trans inter_subset_left
  have hAcov : G ⊆ ⋃ n, A n := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover hx)
    obtain ⟨j, hj⟩ := exists_nat_ge ‖x‖
    refine mem_iUnion.mpr ⟨Nat.pair i j, ?_⟩
    simpa only [A, P, Nat.unpair_pair, mem_inter_iff, mem_closedBall, dist_zero_right] using
      show (x ∈ G ∧ x ∈ t i) ∧ ‖x‖ ≤ (j : ℝ) from ⟨⟨hx, hi⟩, hj⟩
  refine ⟨A, fun n => (hG.inter (ht _)).inter measurableSet_closedBall,
    fun n => isBounded_closedBall.subset (show A n ⊆ closedBall _ _ from inter_subset_right),
    ?_, fun n x hx => hGood x (hSub n hx), ?_⟩
  · intro n
    by_cases hne : (A n).Nonempty
    · obtain ⟨x, hx⟩ := hne
      obtain ⟨y, hy, hTy⟩ := hT ⟨x, hSub n hx⟩ (Nat.unpair n).1
      let B := T (Nat.unpair n).1
      have hInjB : Function.Injective B := by
        dsimp [B]
        rw [hTy]
        exact hInj y hy
      have hAntiB : AntilipschitzWith (L B) B := hAntiL B hInjB
      have hsmall : e B < (L B)⁻¹ := by
        change (L B)⁻¹ / 2 < (L B)⁻¹
        exact half_lt_self (inv_pos.mpr (hL B))
      have ha : ApproximatesLinearOn f B (A n) (e B) :=
        (hApprox (Nat.unpair n).1).mono_set inter_subset_left
      refine ⟨((L B)⁻¹ - e B)⁻¹, ?_⟩
      simpa only [Set.restrict_apply, add_sub_cancel] using!
        (hAntiB.restrict (A n)).add_lipschitzWith ha.lipschitz_sub hsmall
    · have hempty : A n = ∅ := not_nonempty_iff_eq_empty.mp hne
      rw [hempty]
      exact ⟨1, AntilipschitzWith.of_subsingleton⟩
  · apply measure_mono_null _ ((hausdorffMeasure_zero_iff_euclidean _).mpr hBad)
    rintro y ⟨⟨x, rfl⟩, hnot⟩
    refine ⟨x, fun hx => ?_, rfl⟩
    obtain ⟨n, hn⟩ := mem_iUnion.mp (hAcov hx)
    exact hnot (mem_iUnion.mpr ⟨n, mem_image_of_mem f hn⟩)

/-- A countably rectifiable set admits bounded Borel bi-Lipschitz charts whose global
Lipschitz parametrizations have injective derivatives at every point of the chart domains. -/
theorem CountablyRectifiable.exists_regular_bilipschitz_cover {m d : ℕ} {S : Set (E m)}
    (h : CountablyRectifiable d S) :
    ∃ (A : ℕ → Set (E d)) (f : ℕ → E d → E m),
      (∀ n, MeasurableSet (A n)) ∧ (∀ n, IsBounded (A n)) ∧
      (∀ n, ∃ K L : ℝ≥0, LipschitzWith K (f n) ∧ AntilipschitzWith L ((A n).restrict (f n))) ∧
      (∀ n x, x ∈ A n → DifferentiableAt ℝ (f n) x ∧ Function.Injective (fderiv ℝ (f n) x)) ∧
      μH[(d : ℝ)] (S \ ⋃ n, f n '' A n) = 0 := by
  classical
  obtain ⟨f, hf, hS⟩ := h
  choose K hK using hf
  choose B hBmeas hBbound hAnti hReg hNull using
    fun n => exists_regular_bilipschitz_cover_of_lipschitz (hK n)
  refine ⟨fun n => B (Nat.unpair n).1 (Nat.unpair n).2,
    fun n => f (Nat.unpair n).1, fun n => hBmeas _ _, fun n => hBbound _ _, ?_, ?_, ?_⟩
  · intro n
    obtain ⟨L, hL⟩ := hAnti (Nat.unpair n).1 (Nat.unpair n).2
    exact ⟨_, L, hK _, hL⟩
  · exact fun n x hx => hReg _ _ x hx
  · rw [Set.iUnion_unpair (fun i j => f i '' B i j)]
    have hsub : S \ (⋃ i, ⋃ j, f i '' B i j) ⊆
        (S \ ⋃ i, range (f i)) ∪ ⋃ i, (range (f i) \ ⋃ j, f i '' B i j) := by
      intro x hx
      by_cases hMem : x ∈ ⋃ i, range (f i)
      · obtain ⟨i, hi⟩ := mem_iUnion.mp hMem
        exact Or.inr (mem_iUnion.mpr ⟨i, hi, fun hj => hx.2 (mem_iUnion.mpr ⟨i, hj⟩)⟩)
      · exact Or.inl ⟨hx.1, hMem⟩
    exact measure_mono_null hsub (measure_union_null hS (measure_iUnion_null hNull))

end SupportingAnalysis
