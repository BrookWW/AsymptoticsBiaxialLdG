module

public import Thesis.Variational.GlobalLimit
import Thesis.Variational.BoundaryEnergy
import Thesis.Variational.H10FractionalEmbedding
import Thesis.Variational.NonexpansiveSmoothing
import Thesis.Variational.WholeWallEnergy
import Thesis.Upstream.Rellich
import StratificationTheory.Compactness.StrongGradientEnergy
import StratificationTheory.Compactness.WeakGradientClosure
import HolderToCK.Analysis.Poisson.PotentialRegularityMollification
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

/-! The nonexpansive weak chain rule with the original smooth Dirichlet trace. -/

public section

noncomputable section

open Filter MeasureTheory Set Topology
open scoped ContDiff ENNReal NNReal Matrix.Norms.Frobenius

namespace Thesis

variable {Ω : Set Point}

local instance nonexpansiveContinuousENorm : ContinuousENorm S0 :=
  @SeminormedAddGroup.toContinuousENorm S0 inferInstance

local instance nonexpansiveENormedS0 : ENormedAddMonoid S0 :=
  NormedAddGroup.toENormedAddMonoid

private theorem smooth_memH1 (hΩ : IsOpen Ω) (hBound : Bornology.IsBounded Ω)
    {f : Point → S0} (hf : ContDiff ℝ ∞ f) : MemH1 Ω f (ClassicalGradient f) :=
  memH1Loc_of_contDiffOn isOpen_univ (hf.of_le (by simp)).contDiffOn Ω hΩ
    ⟨hBound.isCompact_closure, subset_univ _⟩

private theorem classicalGradient_add_of_smooth {f g : Point → S0}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    ClassicalGradient (f + g) = ClassicalGradient f + ClassicalGradient g := by
  funext x j
  simp only [ClassicalGradient, coordDeriv, fderiv_add (hf.differentiable (by simp) x)
    (hg.differentiable (by simp) x), add_apply, Pi.add_apply]

private def approximationError (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

private theorem approximationError_pos (n : ℕ) : 0 < approximationError n := by
  unfold approximationError
  positivity

private theorem approximationError_tendsto :
    Tendsto approximationError atTop (𝓝 0) :=
  HolderToCK.compactDataApproximationScale_tendsto

private theorem smooth_lift_approximation (hΩ : IsOpen Ω) (hBound : Bornology.IsBounded Ω)
    {u B : Point → S0} {D : Point → Gradient}
    (hu : MemH1 Ω u D) (hB : ContDiff ℝ ∞ B)
    (hTr : SameTrace Ω u B D (ClassicalGradient B)) :
    ∃ φ : ℕ → Point → S0, (∀ n, ContDiff ℝ ∞ (φ n)) ∧
      (∀ n, HasCompactSupport (φ n)) ∧ (∀ n, tsupport (φ n) ⊆ Ω) ∧
      StrongH1 Ω (fun n => B + φ n) (fun n => ClassicalGradient (B + φ n)) u D := by
  have hApprox n := hTr.2 (ENNReal.ofReal (approximationError n))
    (ENNReal.ofReal_pos.mpr (approximationError_pos n))
  choose φ hφ hCompact hSupport hClose using hApprox
  refine ⟨φ, hφ, hCompact, hSupport, fun n => smooth_memH1 hΩ hBound (hB.add (hφ n)), hu, ?_⟩
  have hEq (n : ℕ) :
      h1Deviation Ω (B + φ n) u (ClassicalGradient (B + φ n)) D =
        h1Deviation Ω (u - B) (φ n) (D - ClassicalGradient B) (ClassicalGradient (φ n)) := by
    unfold h1Deviation
    rw [classicalGradient_add_of_smooth hB (hφ n)]
    congr 1
    funext x
    have hMap : (B + φ n) x - u x = -((u - B) x - φ n x) := by
      simp only [Pi.sub_apply, Pi.add_apply]
      abel
    have hCol (j : Fin 3) :
        (ClassicalGradient B + ClassicalGradient (φ n)) x j - D x j =
          -((D - ClassicalGradient B) x j - ClassicalGradient (φ n) x j) := by
      simp only [Pi.sub_apply, Pi.add_apply]
      abel
    simp only [hMap, hCol, norm_neg]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal approximationError_tendsto)
    (fun _ => zero_le) (fun n => by rw [hEq]; exact (hClose n).le)

private theorem strongH1_map_limit
    {u : ℕ → Point → S0} {D : ℕ → Point → Gradient} {v : Point → S0} {G : Point → Gradient}
    (h : StrongH1 Ω u D v G) :
    Tendsto (fun n => eLpNorm (u n - v) 2 (volume.restrict Ω)) atTop (𝓝 0) := by
  have hLe (n : ℕ) : eLpNorm (u n - v) 2 (volume.restrict Ω) ^ 2 ≤
      h1Deviation Ω (u n) v (D n) G := by
    rw [eLpNorm_two_sq_eq_tensor_lintegral]
    exact lintegral_mono fun x => ENNReal.ofReal_le_ofReal
      (le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => sq_nonneg _))
  refine tendsto_order.2 ⟨fun _ hc => (not_lt_of_ge zero_le hc).elim, fun c hc => ?_⟩
  have hε : ∀ᶠ n in atTop, h1Deviation Ω (u n) v (D n) G < c ^ 2 :=
    (tendsto_order.1 h.2.2).2 _ (ENNReal.pow_pos hc _)
  exact hε.mono fun n hn => lt_of_not_ge fun hge =>
    (not_lt_of_ge (pow_le_pow_left' hge 2)) ((hLe n).trans_lt hn)

private theorem eLpNorm_le_uniform {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] {μ : Measure X} [IsFiniteMeasure μ]
    {f : X → E} {a : ℝ} (ha : 0 ≤ a) (hf : ∀ᵐ x ∂μ, ‖f x‖ ≤ a) :
    eLpNorm f 2 μ ≤ ENNReal.ofReal a * μ univ ^ (1 / (2 : ℝ)) := by
  calc
    _ ≤ eLpNorm (fun _ : X => a) 2 μ :=
      eLpNorm_mono_ae_real (hf.mono fun _ hx => by simpa only [Real.norm_eq_abs, abs_of_nonneg ha] using hx)
    _ = _ := by
      rw [eLpNorm_const' a (by norm_num) (by norm_num)]
      simp [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg ha]

private theorem tendsto_approximationError_mul_measure {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] :
    Tendsto (fun n => ENNReal.ofReal (approximationError n) * μ univ ^ (1 / (2 : ℝ))) atTop (𝓝 0) := by
  have h : Tendsto (fun n => ENNReal.ofReal (approximationError n)) atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal approximationError_tendsto
  have hFinite : μ univ ^ (1 / (2 : ℝ)) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) (measure_ne_top _ _)
  simpa only [zero_mul] using ENNReal.Tendsto.mul_const h (Or.inr hFinite)

private theorem pointwise_column_bound_of_weak
    (hΩ : IsOpen Ω) {J D : ℕ → Point → S0} {G A : Point → S0}
    (hJ : ∀ n, MemLp (J n) 2 (volume.restrict Ω)) (hD : ∀ n, MemLp (D n) 2 (volume.restrict Ω))
    (hG : MemLp G 2 (volume.restrict Ω)) (hA : MemLp A 2 (volume.restrict Ω))
    (hWeak : WeakL2FrobeniusConvergence Ω J G)
    (hDconv : Tendsto (fun n => eLpNorm (D n - A) 2 (volume.restrict Ω)) atTop (𝓝 0))
    (hLe : ∀ n x, ‖J n x‖ ≤ ‖D n x‖) :
    ∀ᵐ x ∂volume.restrict Ω, ‖G x‖ ≤ ‖A x‖ := by
  let μ := volume.restrict Ω
  have hSq {g : Point → S0} (hg : MemLp g 2 μ) :
      Integrable (fun x => ‖g x‖ ^ 2) μ := by
    exact (memLp_two_iff_integrable_sq_norm hg.1).mp hg
  have hSqLe : (fun x => ‖G x‖ ^ 2) ≤ᵐ[μ] fun x => ‖A x‖ ^ 2 := by
    refine ae_le_of_forall_setIntegral_le (hSq hG) (hSq hA) fun s hs _ => ?_
    let V := s ∩ Ω
    let ν := volume.restrict V
    have hν : μ.restrict s = ν := Measure.restrict_restrict hs
    have hV : MeasurableSet V := hs.inter hΩ.measurableSet
    have hWeak' := (weakL2FrobeniusConvergence_iff_upstream V J G).mp
      (hWeak.mono hV inter_subset_right)
    have hGLp : MemLp (frobeniusField G) 2 ν :=
      ((frobeniusCoordinateEquiv_memLp_iff μ 2 G).mpr hG).mono_measure (Measure.restrict_mono inter_subset_right le_rfl)
    let w := hGLp.toLp (frobeniusField G)
    have hPair (g : Point → S0) :
        (∫ x, inner ℝ (frobeniusCoordinateEquiv (g x)) (w x) ∂ν) =
          ∫ x, inner ℝ (frobeniusCoordinateEquiv (g x)) (frobeniusCoordinateEquiv (G x)) ∂ν := by
      apply integral_congr_ae
      filter_upwards [hGLp.coeFn_toLp] with x hx
      rw [hx]
    have hPairConv := hWeak' w
    change Tendsto (fun n => ∫ x, inner ℝ (frobeniusCoordinateEquiv (J n x)) (w x) ∂ν)
      atTop (𝓝 (∫ x, inner ℝ (frobeniusCoordinateEquiv (G x)) (w x) ∂ν)) at hPairConv
    simp only [hPair, real_inner_self_eq_norm_sq, LinearIsometryEquiv.norm_map] at hPairConv
    have hRight := tendsto_setIntegral_of_L1' _ (hSq hA).aestronglyMeasurable
      (Eventually.of_forall fun n => hSq (hD n)) (tendsto_eLpNorm_diff_norm_sq_zero hD hA hDconv) s
    rw [hν] at hRight ⊢
    have hStep (n : ℕ) :
        (2 : ℝ) * (∫ x, inner ℝ (frobeniusCoordinateEquiv (J n x))
           (frobeniusCoordinateEquiv (G x)) ∂ν) ≤
          (∫ x, ‖D n x‖ ^ 2 ∂ν) + ∫ x, ‖G x‖ ^ 2 ∂ν := by
      have hj : MemLp (frobeniusField (J n)) 2 ν :=
        ((frobeniusCoordinateEquiv_memLp_iff μ 2 (J n)).mpr (hJ n)).mono_measure
          (Measure.restrict_mono inter_subset_right le_rfl)
      have hInt : Integrable (fun x => inner ℝ (frobeniusField (J n) x) (frobeniusField G x)) ν := by
        refine (L2.integrable_inner (𝕜 := ℝ) (hj.toLp _) w).congr ?_
        filter_upwards [hj.coeFn_toLp, hGLp.coeFn_toLp] with x hx hy
        rw [hx, hy]
      have hID : Integrable (fun x => ‖D n x‖ ^ 2) ν := by rw [← hν]; exact (hSq (hD n)).restrict
      have hIG : Integrable (fun x => ‖G x‖ ^ 2) ν := by rw [← hν]; exact (hSq hG).restrict
      rw [← integral_const_mul, ← integral_add hID hIG]
      apply integral_mono ((hInt.const_mul 2)) (hID.add hIG)
      intro x
      have hc := (le_abs_self _).trans (abs_real_inner_le_norm
        (frobeniusCoordinateEquiv (J n x)) (frobeniusCoordinateEquiv (G x)))
      simp only [LinearIsometryEquiv.norm_map] at hc
      dsimp only [Pi.add_apply]
      have h := mul_le_mul_of_nonneg_right (hLe n x) (norm_nonneg (G x))
      nlinarith only [hc, h, sq_nonneg (‖D n x‖ - ‖G x‖)]
    have hLimit := le_of_tendsto_of_tendsto (hPairConv.const_mul 2)
      (hRight.add tendsto_const_nhds) (Eventually.of_forall hStep)
    linarith
  filter_upwards [hSqLe] with x hx
  exact le_of_sq_le_sq hx (norm_nonneg _)

private theorem smooth_nonexpansive_value_limit
    [IsFiniteMeasure (volume.restrict Ω)] {F : S0 → S0} (hF : LipschitzWith 1 F)
    {u : Point → S0} (hu : MemLp u 2 (volume.restrict Ω))
    {f : ℕ → S0 → S0} (hf : ∀ n, ContDiff ℝ ∞ (f n))
    (hfApprox : ∀ n x, dist (f n x) (F x) ≤ approximationError n)
    {U : ℕ → Point → S0} (hU : ∀ n, ContDiff ℝ ∞ (U n))
    (hUconv : Tendsto (fun n => eLpNorm (U n - u) 2 (volume.restrict Ω)) atTop (𝓝 0)) :
    MemLp (F ∘ u) 2 (volume.restrict Ω) ∧ Tendsto
      (fun n => eLpNorm ((f n ∘ U n) - (F ∘ u)) 2 (volume.restrict Ω)) atTop (𝓝 0) := by
  let μ := volume.restrict Ω
  let V (n : ℕ) := f n ∘ U n
  let v := F ∘ u
  have hVmem : MemLp v 2 μ := by
    refine (hu.norm.add (memLp_const ‖F 0‖)).mono' (hF.continuous.comp_aestronglyMeasurable hu.1)
      (Eventually.of_forall fun x => ?_)
    calc
      ‖F (u x)‖ ≤ ‖F (u x) - F 0‖ + ‖F 0‖ := by simpa only [sub_add_cancel] using norm_add_le (F (u x) - F 0) (F 0)
      _ ≤ ‖u x‖ + ‖F 0‖ := by
        have h := hF.dist_le_mul (u x) (0 : S0)
        rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm, sub_zero] at h
        gcongr
  have hStrong : Tendsto (fun n => eLpNorm (V n - v) 2 μ) atTop (𝓝 0) := by
    have hBound (n : ℕ) : eLpNorm (V n - v) 2 μ ≤
        ENNReal.ofReal (approximationError n) * μ univ ^ (1 / (2 : ℝ)) +
        eLpNorm (U n - u) 2 μ := by
      let M := f n ∘ U n - F ∘ U n
      let N := F ∘ U n - F ∘ u
      have hM : AEStronglyMeasurable M μ := ((hf n).continuous.comp (hU n).continuous).aestronglyMeasurable.sub
        (hF.continuous.comp (hU n).continuous).aestronglyMeasurable
      have hN : AEStronglyMeasurable N μ :=
        (hF.continuous.comp (hU n).continuous).aestronglyMeasurable.sub hVmem.1
      have hEq : V n - v = M + N := by
        funext x
        simp only [M, N, V, v, Pi.add_apply, Pi.sub_apply, Function.comp_apply]
        abel
      rw [hEq]
      have hA : ∀ᵐ x ∂μ, ‖M x‖ ≤ approximationError n := Eventually.of_forall fun x => by
        have h := hfApprox n (U n x)
        rw [dist_eq_norm] at h
        exact h
      have hB : ∀ᵐ x ∂μ, ‖N x‖ ≤ ‖(U n - u) x‖ := Eventually.of_forall fun x => by
        have h := hF.dist_le_mul (U n x) (u x)
        rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm] at h
        exact h
      have hSum : eLpNorm (M + N) 2 μ ≤ eLpNorm M 2 μ + eLpNorm N 2 μ :=
        eLpNorm_add_le hM hN (by norm_num)
      exact hSum.trans (add_le_add (eLpNorm_le_uniform (approximationError_pos n).le hA)
        (eLpNorm_mono_ae hB))
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa only [add_zero] using (tendsto_approximationError_mul_measure μ).add hUconv)
      (fun _ => zero_le) hBound
  exact ⟨hVmem, hStrong⟩

private theorem exists_weak_nonexpansive_graph
    (hΩ : IsSmoothDomain Ω)
    {U V : ℕ → Point → S0} {Dₙ J : ℕ → Point → Gradient}
    {u v : Point → S0} {D : Point → Gradient}
    (hApprox : StrongH1 Ω U Dₙ u D) (hVSob : ∀ n, MemH1 Ω (V n) (J n))
    (hJLe : ∀ n x j, ‖J n x j‖ ≤ ‖Dₙ n x j‖)
    (hv : MemLp v 2 (volume.restrict Ω))
    (hStrong : Tendsto (fun n => eLpNorm (V n - v) 2 (volume.restrict Ω)) atTop (𝓝 0)) :
    ∃ (κ : ℕ → ℕ) (G : Point → Gradient), StrictMono κ ∧ MemH1 Ω v G ∧
      WeakL2FrobeniusConvergence Ω (fun n => V (κ n)) v ∧
      (∀ j, WeakL2FrobeniusConvergence Ω (fun n x => J (κ n) x j) (fun x => G x j)) ∧
      (∀ᵐ x ∂volume.restrict Ω, ∀ j, ‖G x j‖ ≤ ‖D x j‖) := by
  let μ := volume.restrict Ω
  let O : HarmonicMaps.OpenDomain 3 := ⟨Ω, hΩ.1.1⟩
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr hΩ.1.2.2.measure_lt_top.ne
  have hUdom (n : ℕ) : HarmonicMaps.MemW12 O (frobeniusField (U n)) (frobeniusGradient (Dₙ n)) :=
    (memH1_iff_memW12 O _ _).mp (hApprox.1 n)
  have huDom : HarmonicMaps.MemW12 O (frobeniusField u) (frobeniusGradient D) :=
    (memH1_iff_memW12 O _ _).mp hApprox.2.1
  have hVdom (n : ℕ) : HarmonicMaps.MemW12 O (frobeniusField (V n)) (frobeniusGradient (J n)) :=
    (memH1_iff_memW12 O _ _).mp (hVSob n)
  have hGradStrong (j : Fin 3) : Tendsto (fun n => eLpNorm
      (fun x => frobeniusGradient (Dₙ n) x j - frobeniusGradient D x j) 2 μ) atTop (𝓝 0) := by
    apply (hApprox.tendsto_eLpNorm_gradient_column j).congr
    intro n
    apply eLpNorm_congr_norm_ae
    exact Eventually.of_forall fun x => by
      change ‖Dₙ n x j - D x j‖ = ‖frobeniusCoordinateEquiv (Dₙ n x j) - frobeniusCoordinateEquiv (D x j)‖
      rw [← map_sub, LinearIsometryEquiv.norm_map]
  have hEnergyT := StratificationTheory.Compactness.integral_hsNormSq_tendsto_of_strong_columns
    (fun n => (hUdom n).2.2) huDom.2.2 hGradStrong
  obtain ⟨C, hC⟩ := (Metric.isBounded_range_of_tendsto _ hEnergyT).exists_norm_le
  let C₀ : ℝ≥0 := ⟨max C 0, le_max_right _ _⟩
  have hEnergyJ (n : ℕ) : HarmonicMaps.dirichletEnergy (frobeniusGradient (J n)) Ω ≤ C₀ := by
    calc
      _ ≤ HarmonicMaps.dirichletEnergy (frobeniusGradient (Dₙ n)) Ω := by
        apply lintegral_mono
        intro x
        apply ENNReal.ofReal_le_ofReal
        exact Finset.sum_le_sum fun j _ => by
          simpa only [frobeniusGradient, LinearIsometryEquiv.norm_map] using
            pow_le_pow_left₀ (norm_nonneg _) (hJLe n x j) 2
      _ = ENNReal.ofReal (∫ x in Ω, HarmonicMaps.hsNormSq (frobeniusGradient (Dₙ n) x)) :=
        HarmonicMaps.dirichletEnergy_eq_ofReal_integral
          (HarmonicMaps.integrable_hsNormSq_of_memLp_columns (hUdom n).2.2)
      _ ≤ C₀ := by
        rw [← ENNReal.ofReal_coe_nnreal]
        apply ENNReal.ofReal_le_ofReal
        exact (le_abs_self _).trans ((hC _ (mem_range_self n)).trans (le_max_left _ _))
  obtain ⟨κ, W, hκ, hWLp, _, hW⟩ := ambient_weak_gradient_subsequence Ω
    (fun n => frobeniusGradient (J n)) (fun n => (hVdom n).2.2) C₀ hEnergyJ
  let G (x : Point) (j : Fin 3) := frobeniusCoordinateEquiv.symm (W x j)
  have hWp (x : Point) (j : Fin 3) : frobeniusCoordinateEquiv (G x j) = W x j :=
    frobeniusCoordinateEquiv.apply_symm_apply _
  have hVconv : Tendsto (fun n => eLpNorm (frobeniusField (V (κ n)) - frobeniusField v) 2 μ) atTop (𝓝 0) := by
    apply (hStrong.comp hκ.tendsto_atTop).congr
    intro n
    have hEq : frobeniusField (V (κ n)) - frobeniusField v = frobeniusField (V (κ n) - v) := by
      funext x
      exact (frobeniusCoordinateEquiv.map_sub _ _).symm
    rw [hEq, eLpNorm_frobeniusField]
    rfl
  have hvNative := (frobeniusCoordinateEquiv_memLp_iff μ 2 v).mpr hv
  have hvSob : MemH1 Ω v G := by
    apply (memH1_iff_memW12 O v G).mpr
    have hClose := StratificationTheory.Compactness.memW12_of_strong_map_weak_gradient_limit
      (fun n => hVdom (κ n)) hvNative hWLp hVconv hW
    have hGW : frobeniusGradient G = W := by funext x j; exact hWp x j
    simpa only [hGW] using hClose
  have hWeakJ (j : Fin 3) : WeakL2FrobeniusConvergence Ω (fun n x => J (κ n) x j) (fun x => G x j) :=
    (weakL2FrobeniusConvergence_iff_upstream Ω _ _).mpr (by simpa only [hWp] using hW j)
  have hWeakV : WeakL2FrobeniusConvergence Ω (fun n => V (κ n)) v :=
    (weakL2FrobeniusConvergence_iff_upstream Ω _ _).mpr fun w =>
      StratificationTheory.Compactness.tendsto_integral_inner_of_L2_convergence
        (fun n => (hVdom (κ n)).2.1) hvNative (Lp.memLp w) hVconv
  refine ⟨κ, G, hκ, hvSob, hWeakV, hWeakJ, ?_⟩
  rw [ae_all_iff]
  intro j
  exact pointwise_column_bound_of_weak hΩ.1.1
    (fun n => (hVSob (κ n)).2.1 j) (fun n => (hApprox.1 (κ n)).2.1 j)
    (hvSob.2.1 j) (hApprox.2.1.2.1 j) (hWeakJ j)
    ((hApprox.tendsto_eLpNorm_gradient_column j).comp hκ.tendsto_atTop)
    (fun n x => hJLe (κ n) x j)

private theorem trace_eq_of_smooth_uniform_boundary_limit
    (T : SobolevTraceOperator Ω) [IsFiniteMeasure (frontierSurfaceMeasure Ω)]
    {V : ℕ → Point → S0} {v B : Point → S0} {G : Point → Gradient}
    (hV : ∀ n, ContDiff ℝ ∞ (V n)) (hB : ContDiff ℝ ∞ B)
    (hVSob : ∀ n, MemH1 Ω (V n) (ClassicalGradient (V n)))
    (hvSob : MemH1 Ω v G) (hBSob : MemH1 Ω B (ClassicalGradient B))
    (hWeakV : WeakL2FrobeniusConvergence Ω V v)
    (hWeakJ : ∀ j, WeakL2FrobeniusConvergence Ω
      (fun n x => ClassicalGradient (V n) x j) (fun x => G x j))
    (κ : ℕ → ℕ) (hκ : StrictMono κ)
    (hBdy : ∀ n, ∀ᵐ x : frontier Ω ∂frontierSurfaceMeasure Ω,
      dist (V n x) (B x) ≤ approximationError (κ n)) :
    T.trace hvSob = T.trace hBSob := by
  let σ := frontierSurfaceMeasure Ω
  let t := T.trace hBSob
  have hTraceNorm (n : ℕ) :
      eLpNorm ((T.trace (hVSob n) : frontier Ω → HarmonicMaps.Ambient 5) -
        (t : frontier Ω → HarmonicMaps.Ambient 5)) 2 σ ≤
        ENNReal.ofReal (approximationError (κ n)) * σ univ ^ (1 / (2 : ℝ)) := by
    apply eLpNorm_le_uniform (approximationError_pos (κ n)).le
    filter_upwards [T.smooth (hV n) (hVSob n), T.smooth hB hBSob, hBdy n] with x h₁ h₂ h₃
    change ‖(T.trace (hVSob n) : frontier Ω → HarmonicMaps.Ambient 5) x - t x‖ ≤ _
    rw [h₁, show t x = frobeniusCoordinateEquiv (B x) from h₂,
      ← map_sub, LinearIsometryEquiv.norm_map, ← dist_eq_norm]
    exact h₃
  have hNormConv : Tendsto (fun n => eLpNorm
      ((T.trace (hVSob n) : frontier Ω → HarmonicMaps.Ambient 5) -
        (t : frontier Ω → HarmonicMaps.Ambient 5)) 2 σ) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      ((tendsto_approximationError_mul_measure σ).comp hκ.tendsto_atTop)
      (fun _ => zero_le) hTraceNorm
  have hLp : Tendsto (fun n => T.trace (hVSob n)) atTop (𝓝 t) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).2 hNormConv
  let w := T.trace hvSob - t
  have h₁ := T.tendsto_inner_trace hVSob hvSob hWeakV hWeakJ w
  have h₂ := hLp.inner (𝕜 := ℝ) (tendsto_const_nhds (x := w))
  apply sub_eq_zero.mp
  apply (inner_self_eq_zero (𝕜 := ℝ)).mp
  rw [inner_sub_left, sub_eq_zero]
  exact tendsto_nhds_unique h₁ h₂

/-- A given bounded trace operator also supplies the nonexpansive chain rule
with preservation of its original smooth boundary datum. -/
theorem SobolevTraceOperator.nonexpansiveSobolevTraceComposition
    (T : SobolevTraceOperator Ω) (hΩ : IsSmoothDomain Ω) : NonexpansiveSobolevTraceComposition Ω := by
  intro F hF b u D hu hTr hb
  let μ := volume.restrict Ω
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr hΩ.1.2.2.measure_lt_top.ne
  letI : IsFiniteMeasure (frontierSurfaceMeasure Ω) := ⟨by
    rw [← isometry_subtype_coe.euclideanHausdorffMeasure_image]
    rw [image_univ, Subtype.range_coe_subtype, setOf_mem_eq]
    exact hΩ.frontier_euclideanHausdorffMeasure_lt_top⟩
  obtain ⟨B, hB, hBb, hUB⟩ := hTr
  obtain ⟨φ, hφ, _, hφΩ, hApprox⟩ := smooth_lift_approximation hΩ.1.1 hΩ.1.2.2 hu hB hUB
  obtain ⟨f, hf, hfLip, hfApprox⟩ := exists_smooth_nonexpansive_approximation hF
  let U (n : ℕ) := B + φ n
  let Dₙ (n : ℕ) := ClassicalGradient (U n)
  let V (n : ℕ) := f n ∘ U n
  let J (n : ℕ) := ClassicalGradient (V n)
  let v := F ∘ u
  have hU (n : ℕ) : ContDiff ℝ ∞ (U n) := hB.add (hφ n)
  have hV (n : ℕ) : ContDiff ℝ ∞ (V n) := (hf n).comp (hU n)
  have hVSob (n : ℕ) : MemH1 Ω (V n) (J n) := smooth_memH1 hΩ.1.1 hΩ.1.2.2 (hV n)
  have hJLe (n : ℕ) (x : Point) (j : Fin 3) : ‖J n x j‖ ≤ ‖Dₙ n x j‖ := by
    have hChain := fderiv_comp x ((hf n).differentiable (by simp) (U n x))
      ((hU n).differentiable (by simp) x)
    have hCol : J n x j = fderiv ℝ (f n) (U n x) (Dₙ n x j) :=
      congrArg (fun L : Point →L[ℝ] S0 => L (axis j)) hChain
    rw [hCol]
    let z := Dₙ n x j
    let L (t : ℝ) := U n x + t • z
    have hL : HasDerivAt L z 0 := by
      have h := ((hasDerivAt_id (0 : ℝ)).smul_const z).const_add (U n x)
      rw [one_smul] at h
      with_unfolding_all exact h
    have hLip : LipschitzWith ‖z‖₊ L := LipschitzWith.of_dist_le_mul fun t s => by
      rw [show L t = U n x + t • z from rfl, show L s = U n x + s • z from rfl,
        dist_add_left, dist_eq_norm]
      have hEq : t • z - s • z = (t - s) • z := (sub_smul t s z).symm
      rw [hEq, norm_smul, ← dist_eq_norm, coe_nnnorm, mul_comm]
    have hZero : L 0 = U n x := by simp [L]
    have hDer := ((hf n).differentiable (by simp) (L 0)).hasFDerivAt.comp_hasDerivAt 0 hL
    rw [hZero] at hDer
    have hn := hDer.le_of_lipschitz ((hfLip n).comp hLip)
    rw [one_mul, coe_nnnorm] at hn
    with_unfolding_all exact hn
  obtain ⟨hv, hStrong⟩ := smooth_nonexpansive_value_limit hF hu.1 hf hfApprox hU (strongH1_map_limit hApprox)
  obtain ⟨κ, G, hκ, hvSob, hWeakV, hWeakJ, hLe⟩ :=
    exists_weak_nonexpansive_graph hΩ hApprox hVSob hJLe hv hStrong
  let hBSob := smooth_memH1 hΩ.1.1 hΩ.1.2.2 hB
  have hTrace := trace_eq_of_smooth_uniform_boundary_limit T
    (fun n => hV (κ n)) hB (fun n => hVSob (κ n)) hvSob hBSob hWeakV hWeakJ κ hκ (by
      intro n
      filter_upwards [hb] with x hx
      have hφx : φ (κ n) x = 0 := by
        by_contra hn
        exact Set.disjoint_left.mp (disjoint_frontier_iff_isOpen.mpr hΩ.1.1) x.property
          (hφΩ (κ n) (subset_closure hn))
      have hFx : F (B x) = B x := by rw [hBb, hx]
      simpa only [V, U, Function.comp_apply, Pi.add_apply, hφx, add_zero, hFx, approximationError]
        using hfApprox (κ n) (B x))
  exact ⟨G, hvSob, ⟨B, hB, hBb, (T.trace_eq_iff_sameTrace hvSob hBSob).mp hTrace⟩, hLe⟩

end Thesis
