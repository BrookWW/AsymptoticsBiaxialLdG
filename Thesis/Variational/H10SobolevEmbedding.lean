module

public import Thesis.Variational.H10FractionalEmbedding
import Thesis.Upstream.Rellich
import Thesis.Variational.GlobalComparison
import HarmonicMaps.Analysis.RadialIntegrability
import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! The three-dimensional Sobolev embedding on the actual Dirichlet graph. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Set Topology
open scoped BigOperators ContDiff ENNReal NNReal Matrix.Norms.Frobenius

namespace Thesis

local instance h10SobolevContinuousENorm : ContinuousENorm S0 :=
  @SeminormedAddGroup.toContinuousENorm S0 inferInstance

private theorem frobeniusField_fderiv_norm_sq_le (φ : Point → S0) (hφ : ContDiff ℝ ∞ φ) (x : Point) :
    ‖fderiv ℝ (frobeniusField φ) x‖ ^ 2 ≤ ∑ j : Fin 3, ‖coordDeriv j φ x‖ ^ 2 := by
  let J := fderiv ℝ (frobeniusField φ) x
  let D (j : Fin 3) := frobeniusCoordinateEquiv (coordDeriv j φ x)
  have hCol (j : Fin 3) : J (EuclideanSpace.single j 1) = D j := by
    let L := frobeniusCoordinateEquiv.toContinuousLinearEquiv.toContinuousLinearMap
    have hChain := (L.hasFDerivAt.comp x ((hφ.differentiable (by simp) x).hasFDerivAt)).fderiv
    exact congrArg (fun l : Point →L[ℝ] Ambient 5 => l (axis j)) hChain
  have hS : hsNormSq D = ∑ j : Fin 3, ‖coordDeriv j φ x‖ ^ 2 := by
    simp only [hsNormSq,D,LinearIsometryEquiv.norm_map]
  have hNorm : ‖J‖ ≤ Real.sqrt (hsNormSq D) := by
    apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
    intro v
    have hb : ∑ j : Fin 3, v j • EuclideanSpace.single j 1 = v := by
      simpa only [EuclideanSpace.basisFun_repr,EuclideanSpace.basisFun_apply] using
        (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr v
    have he : J v = ∑ j : Fin 3, v j • D j := by
      conv_lhs => rw [← hb]
      simp only [map_sum,map_smul,hCol]
    rw [he]
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).1
    rw [mul_pow,Real.sq_sqrt (hsNormSq_nonneg _)]
    simpa only [mul_comm] using norm_sq_sum_gradient_le D v
  rw [← hS]
  exact (pow_le_pow_left₀ (norm_nonneg _) hNorm 2).trans_eq (Real.sq_sqrt (hsNormSq_nonneg _))

private theorem smoothGraph_eLpNorm_six_bound
    {U : Set Point} (hU : MeasurableSet U) (p : H1Graph U) (φ : Point → S0)
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (hSupp : tsupport φ ⊆ U)
    (hGraph : ∀ j, (p.2 j : Point → S0) =ᵐ[volume.restrict U] coordDeriv j φ) :
    eLpNorm φ 6 (volume.restrict U) ≤
      (SNormLESNormFDerivOfEqConst (Ambient 5) (volume : Measure Point) (2 : ℝ) : ℝ≥0∞) *
        ENNReal.ofReal (Real.sqrt 3) * ENNReal.ofReal ‖p‖ := by
  let g := frobeniusField φ
  let C : ℝ≥0∞ := SNormLESNormFDerivOfEqConst (Ambient 5) (volume : Measure Point) (2 : ℝ)
  have hg : ContDiff ℝ ∞ g := frobeniusCoordinateEquiv.contDiff.comp hφ
  have hgc : HasCompactSupport g := hφc.comp_left (map_zero frobeniusCoordinateEquiv)
  have hFin : Module.finrank ℝ Point = 3 := by simp [Point]
  have hGNS := eLpNorm_le_eLpNorm_fderiv_of_eq (μ := (volume : Measure Point))
    (p := (2 : ℝ≥0)) (p' := (6 : ℝ≥0)) (hg.of_le (by simp)) hgc (by norm_num)
    (by rw [hFin]; decide) (by rw [hFin]; norm_num)
  have hTwo : eLpNorm (fderiv ℝ g) 2 volume ^ 2 =
      ∫⁻ x : Point, ENNReal.ofReal (‖fderiv ℝ g x‖ ^ 2) := by
    calc
      _ = ∫⁻ x : Point, ‖fderiv ℝ g x‖ₑ ^ 2 := by
        simpa only [ENNReal.rpow_two,NNReal.coe_two,ENNReal.coe_two] using
          (eLpNorm_nnreal_pow_eq_lintegral (f := fderiv ℝ g) (μ := volume) (p := (2 : ℝ≥0)) (by norm_num))
      _ = _ := lintegral_congr (fun x => by rw [ENNReal.ofReal_pow (norm_nonneg _),ofReal_norm])
  have hDeriv : eLpNorm (fderiv ℝ g) 2 volume ≤ ENNReal.ofReal (Real.sqrt 3) * ENNReal.ofReal ‖p‖ := by
    apply (ENNReal.pow_le_pow_left_iff (by decide : (2 : ℕ) ≠ 0)).mp
    have hSq : eLpNorm (fderiv ℝ g) 2 volume ^ 2 ≤ 3 * ENNReal.ofReal (‖p‖ ^ 2) := by
      rw [hTwo]
      apply (lintegral_mono (fun x =>
        ENNReal.ofReal_le_ofReal (frobeniusField_fderiv_norm_sq_le φ hφ x))).trans
      exact lintegral_smooth_gradient_le_norm_graph hU p φ hφ hSupp hGraph
    calc
      _ ≤ 3 * ENNReal.ofReal (‖p‖^2) := hSq
      _ = _ := by
        rw [mul_pow, ← ENNReal.ofReal_pow (Real.sqrt_nonneg 3), Real.sq_sqrt (by norm_num),
          ← ENNReal.ofReal_pow (norm_nonneg _)]
        norm_num
  calc
    _ ≤ eLpNorm φ 6 volume := eLpNorm_mono_measure _ Measure.restrict_le_self
    _ = eLpNorm g 6 volume := (eLpNorm_frobeniusField φ 6 volume).symm
    _ ≤ C * eLpNorm (fderiv ℝ g) 2 volume := by exact_mod_cast hGNS
    _ ≤ _ := (mul_le_mul_right hDeriv C).trans_eq (mul_assoc _ _ _).symm

private theorem eLpNorm_six_pow_eq_enorm {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    (μ : Measure X) (f : X → E) :
    eLpNorm f 6 μ ^ (6 : ℕ) = ∫⁻ x, ‖f x‖ₑ ^ (6 : ℕ) ∂μ := by
  simp only [← ENNReal.rpow_natCast]
  exact eLpNorm_nnreal_pow_eq_lintegral (f := f) (μ := μ) (p := (6 : ℝ≥0)) (by norm_num)

/-- The original values in the zero-trace graph satisfy the actual
three-dimensional (L^6) Sobolev bound. -/
theorem exists_h10_sobolevL6_bound :
    ∃ C : ℝ≥0, ∀ {U : Set Point}, MeasurableSet U → ∀ v : H10 U,
      MemLp (h10Value v) 6 (volume.restrict U) ∧
        eLpNorm (h10Value v) 6 (volume.restrict U) ≤ (C : ℝ≥0∞) * ENNReal.ofReal ‖v‖ := by
  let C₀ : ℝ≥0 := SNormLESNormFDerivOfEqConst (Ambient 5) (volume : Measure Point) (2 : ℝ)
  let C := C₀ * Real.toNNReal (Real.sqrt 3)
  refine ⟨C,?_⟩
  intro U hU v
  let μ := volume.restrict U
  obtain ⟨p,f,hp,hData⟩ := v.exists_smooth_graph_approximation
  have hProj : Tendsto (fun n => (p n).1) atTop (𝓝 v.val.1) :=
    continuous_fst.continuousAt.tendsto.comp hp
  obtain ⟨κ,hκ,hAE⟩ := (tendstoInMeasure_of_tendsto_Lp hProj).exists_seq_tendsto_ae
  have hfAE : ∀ᵐ x ∂μ, Tendsto (fun n => f (κ n) x) atTop (𝓝 (h10Value v x)) := by
    filter_upwards [hAE,ae_all_iff.2 (fun n => (hData n).2.2.2.1)] with x hx hxs
    exact hx.congr (fun n => hxs (κ n))
  have hC (n : ℕ) :
      eLpNorm (f n) 6 μ ≤ (C : ℝ≥0∞) * ENNReal.ofReal ‖p n‖ := by
    have h := smoothGraph_eLpNorm_six_bound hU (p n) (f n) (hData n).1 (hData n).2.1
      (hData n).2.2.1 (hData n).2.2.2.2
    have hSqrt : (Real.toNNReal (Real.sqrt 3) : ℝ≥0∞) = ENNReal.ofReal (Real.sqrt 3) := by
      rw [← ENNReal.ofReal_coe_nnreal, Real.coe_toNNReal _ (Real.sqrt_nonneg _)]
    simpa only [C,ENNReal.coe_mul,hSqrt] using h
  have hMeas : AEStronglyMeasurable (h10Value v) μ := (Lp.memLp v.val.1).aestronglyMeasurable
  let A (n : ℕ) (x : Point) := ‖f (κ n) x‖ₑ ^ (6 : ℕ)
  have hA (n : ℕ) : AEMeasurable (A n) μ := ((hData (κ n)).1.continuous.enorm.measurable.pow_const _).aemeasurable
  have hCont : Continuous (fun t : S0 => ‖t‖ₑ ^ (6 : ℕ)) := by
    rw [show (fun t : S0 => ‖t‖ₑ ^ (6 : ℕ)) = (fun s : ℝ≥0∞ => s ^ (6 : ℝ)) ∘ (fun t : S0 => ‖t‖ₑ)
      from funext fun _ => (ENNReal.rpow_natCast _ 6).symm]
    have hPow : Continuous (fun r : ℝ≥0∞ => r ^ (6 : ℝ)) := ENNReal.continuous_rpow_const
    exact hPow.comp continuous_enorm
  have hInt : eLpNorm (h10Value v) 6 μ ^ (6 : ℕ) ≤
      (((C : ℝ≥0∞) * ENNReal.ofReal ‖v‖) ^ (6 : ℕ)) := by
    rw [eLpNorm_six_pow_eq_enorm]
    have hAe : (fun x => ‖h10Value v x‖ₑ ^ (6 : ℕ)) =ᵐ[μ]
        (fun x => liminf (fun n => A n x) atTop) :=
      hfAE.mono fun x hx => ((hCont.tendsto _).comp hx).liminf_eq.symm
    rw [lintegral_congr_ae hAe]
    refine (lintegral_liminf_le' hA).trans ?_
    have hUp (n : ℕ) : (∫⁻ x, A n x ∂μ) ≤ ((C : ℝ≥0∞) * ENNReal.ofReal ‖p (κ n)‖) ^ (6 : ℕ) := by
      rw [← eLpNorm_six_pow_eq_enorm]
      exact pow_le_pow_left' (hC (κ n)) 6
    have hNorm := (hp.comp hκ.tendsto_atTop).norm
    have hReal := ENNReal.tendsto_ofReal hNorm
    have hProd := ENNReal.Tendsto.const_mul (a := (C : ℝ≥0∞)) hReal (Or.inr ENNReal.coe_ne_top)
    have hPow : Tendsto (fun n => ((C : ℝ≥0∞) * ENNReal.ofReal ‖p (κ n)‖) ^ (6 : ℕ))
        atTop (𝓝 ((((C : ℝ≥0∞) * ENNReal.ofReal ‖v‖)) ^ (6 : ℕ))) := by
      simp_rw [← ENNReal.rpow_natCast]
      have hCpow : Continuous (fun r : ℝ≥0∞ => r ^ (6 : ℝ)) := ENNReal.continuous_rpow_const
      exact (hCpow.tendsto _).comp hProd
    exact (liminf_le_liminf (Eventually.of_forall hUp)).trans_eq hPow.liminf_eq
  have hBound := (ENNReal.pow_le_pow_left_iff (by decide : (6 : ℕ) ≠ 0)).mp hInt
  exact ⟨⟨hMeas,hBound.trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top ENNReal.ofReal_lt_top)⟩, hBound⟩

/-- One compact smooth approximation converges in the critical L⁶ value
norm and in all the original L² graph coordinates. -/
theorem H10.exists_smooth_approximation_L6 {U : Set Point} (hU : IsOpen U) (v : H10 U) :
    ∃ f : ℕ → Point → S0,
      (∀ n, ContDiff ℝ ∞ (f n) ∧ HasCompactSupport (f n) ∧ tsupport (f n) ⊆ U ∧
        MemH1 U (f n) (ClassicalGradient (f n))) ∧
      Tendsto (fun n => eLpNorm (f n - h10Value v) 2 (volume.restrict U)) atTop (𝓝 0) ∧
      Tendsto (fun n => eLpNorm (f n - h10Value v) 6 (volume.restrict U)) atTop (𝓝 0) ∧
      ∀ j, Tendsto (fun n => eLpNorm (fun x => coordDeriv j (f n) x - h10Gradient v x j)
        2 (volume.restrict U)) atTop (𝓝 0) := by
  let μ := volume.restrict U
  obtain ⟨p,f,hp,hData⟩ := v.exists_smooth_graph_approximation
  obtain ⟨C,hC⟩ := exists_h10_sobolevL6_bound
  have hn (n : ℕ) : p n ∈ h10Submodule U := by
    apply Submodule.le_topologicalClosure _ (Submodule.subset_span ?_)
    exact ⟨f n,hData n⟩
  let W (n : ℕ) : H10 U := ⟨p n,hn n⟩
  have hV (n : ℕ) : h10Value (W n) =ᵐ[μ] f n := (hData n).2.2.2.1
  have hCoord (n : ℕ) (j : Fin 3) : (fun x => h10Gradient (W n) x j) =ᵐ[μ] coordDeriv j (f n) :=
    (hData n).2.2.2.2 j
  refine ⟨f,fun n => ⟨(hData n).1,(hData n).2.1,(hData n).2.2.1,
    (hasZeroTrace_of_contDiff_hasCompactSupport hU (hData n).1 (hData n).2.1 (hData n).2.2.1).1⟩,?_,?_,?_⟩
  · have hP : Tendsto (fun n => (p n).1) atTop (𝓝 v.val.1) := continuous_fst.continuousAt.tendsto.comp hp
    apply ((Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mp hP).congr
    intro n
    exact eLpNorm_congr_ae ((hV n).sub EventuallyEq.rfl)
  · have hNorm : Tendsto (fun n => ‖W n - v‖) atTop (𝓝 0) := by
      have h := (hp.sub_const v.val).norm
      rw [sub_self,norm_zero] at h
      exact h.congr (fun n => by with_unfolding_all rfl)
    have hLim : Tendsto (fun n => (C : ℝ≥0∞) * ENNReal.ofReal ‖W n - v‖) atTop (𝓝 0) := by
      have h := ENNReal.tendsto_ofReal hNorm
      rw [ENNReal.ofReal_zero] at h
      simpa only [mul_zero] using ENNReal.Tendsto.const_mul (a := (C : ℝ≥0∞)) h (Or.inr ENNReal.coe_ne_top)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hLim (fun _ => zero_le)
    intro n
    have hDiff : h10Value (W n - v) =ᵐ[μ] f n - h10Value v :=
      (Lp.coeFn_sub (W n).val.1 v.val.1).trans ((hV n).sub EventuallyEq.rfl)
    change eLpNorm (f n - h10Value v) 6 μ ≤ (C : ℝ≥0∞) * ENNReal.ofReal ‖W n - v‖
    rw [← eLpNorm_congr_ae hDiff]
    exact (hC hU.measurableSet (W n - v)).2
  · intro j
    have hP : Tendsto (fun n => (p n).2 j) atTop (𝓝 (v.val.2 j)) :=
      ((continuous_apply j).comp continuous_snd).continuousAt.tendsto.comp hp
    apply ((Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mp hP).congr
    intro n
    exact eLpNorm_congr_ae ((hCoord n j).sub EventuallyEq.rfl)

end Thesis
