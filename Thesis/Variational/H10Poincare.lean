module

public import Thesis.Variational.H10FractionalEmbedding

/-! Poincaré's inequality on the literal zero-trace Sobolev graph. -/

public section

noncomputable section

open Filter MeasureTheory Set Topology
open scoped BigOperators ContDiff ENNReal Matrix.Norms.Frobenius

namespace Thesis

private theorem sq_norm_smoothGraphValue_le_translationGradient
    {U : Set Point} (hU : MeasurableSet U) {z : Point}
    (hSeparate : ∀ x ∈ U, x + z ∉ U)
    (p : H1Graph U) (φ : Point → S0) (hφ : ContDiff ℝ ∞ φ) (hφU : tsupport φ ⊆ U)
    (hV : (p.1 : Point → S0) =ᵐ[volume.restrict U] φ)
    (hD : ∀ j, (p.2 j : Point → S0) =ᵐ[volume.restrict U] coordDeriv j φ) :
    ‖p.1‖ ^ 2 ≤ (9 * ‖z‖ ^ 2) * ∑ j : Fin 3, ‖p.2 j‖ ^ 2 := by
  have hφ0 {x : Point} (hx : x ∉ U) : φ x = 0 :=
    Function.notMem_support.mp (fun h => hx (hφU (subset_closure h)))
  have hEq :
      (∫⁻ x in U, ENNReal.ofReal (‖φ x‖ ^ 2)) =
        ∫⁻ x in U, ENNReal.ofReal (‖φ (x+z) - φ x‖ ^ 2) := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem (μ := volume) hU] with x hx
    rw [hφ0 (hSeparate x hx),zero_sub,norm_neg]
  have hpInt : ENNReal.ofReal (‖p.1‖ ^ 2) = ∫⁻ x in U, ENNReal.ofReal (‖φ x‖ ^ 2) := by
    rw [← lintegral_sq_norm_lp (volume.restrict U) p.1]
    exact lintegral_congr_ae (hV.mono fun _ he => congrArg (fun y : S0 => ENNReal.ofReal (‖y‖^2)) he)
  have hNonneg : 0 ≤ (9 * ‖z‖ ^ 2) * ∑ j : Fin 3, ‖p.2 j‖ ^ 2 :=
    mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  apply (ENNReal.ofReal_le_ofReal_iff hNonneg).mp
  calc
    _ = ∫⁻ x in U, ENNReal.ofReal (‖φ (x+z)-φ x‖ ^ 2) := hpInt.trans hEq
    _ ≤ ∫⁻ x, ENNReal.ofReal (‖φ (x+z)-φ x‖ ^ 2) := setLIntegral_le_lintegral _ _
    _ ≤ ENNReal.ofReal (9 * ‖z‖ ^ 2) * ∫⁻ x, ENNReal.ofReal (∑ j : Fin 3, ‖coordDeriv j φ x‖ ^ 2) :=
      lintegral_sq_smooth_translation_difference_le hφ z
    _ = _ := by
      rw [lintegral_smooth_gradient_eq_columns_norm_sq hU p φ hφ hφU hD,
        ENNReal.ofReal_mul (by positivity : 0 ≤ 9*‖z‖^2)]

/-- On a bounded set the value norm of the zero-trace graph is controlled
by the norms of its actual weak columns. -/
theorem exists_H10_value_poincare {U : Set Point} (hU : MeasurableSet U)
    (hBound : Bornology.IsBounded U) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ v : H10 U,
      ‖v.val.1‖ ≤ C * Real.sqrt (∑ j : Fin 3, ‖v.val.2 j‖ ^ 2) := by
  obtain ⟨R,hR⟩ := hBound.exists_norm_le
  let d := 2 * max R 0 + 1
  have hd : 0 < d := lt_of_lt_of_le zero_lt_one (le_add_of_nonneg_left
    (mul_nonneg (by norm_num) (le_max_right R 0)))
  let z : Point := d • axis 0
  have hz : ‖z‖ = d := by
    change ‖d • axis 0‖ = d
    rw [norm_smul,Real.norm_of_nonneg hd.le,show ‖axis 0‖ = 1 from by simp [axis],mul_one]
  have hSep (x : Point) (hx : x ∈ U) : x+z ∉ U := by
    intro h
    have hz' : ‖z‖ ≤ ‖x+z‖ + ‖x‖ := by
      have hZ : x+z-x = z := by abel
      simpa only [hZ] using norm_sub_le (x+z) x
    rw [hz] at hz'
    dsimp only [d] at hz'
    linarith only [hR x hx,hR (x+z) h,hz',le_max_left R 0]
  let K := 9*‖z‖^2
  let C := max 1 (Real.sqrt K)
  have hK : 0 ≤ K := by positivity
  refine ⟨C,le_max_left _ _,fun v => ?_⟩
  obtain ⟨p,φ,hLim,hP⟩ := H10.exists_smooth_graph_approximation v
  have hStep (n : ℕ) : ‖(p n).1‖ ^ 2 ≤ K * ∑ j : Fin 3, ‖(p n).2 j‖ ^ 2 := by
    obtain ⟨hφ,_,hφU,hV,hD⟩ := hP n
    exact sq_norm_smoothGraphValue_le_translationGradient hU hSep (p n) (φ n) hφ hφU hV hD
  have hCol (j : Fin 3) :
      Tendsto (fun n => ‖(p n).2 j‖ ^ 2) atTop (𝓝 (‖v.val.2 j‖ ^ 2)) :=
    (((continuous_apply j).comp continuous_snd).tendsto v.val |>.comp hLim).norm.pow 2
  have hTotal :
      Tendsto (fun n => K * ∑ j : Fin 3, ‖(p n).2 j‖ ^ 2) atTop
        (𝓝 (K * ∑ j : Fin 3, ‖v.val.2 j‖ ^ 2)) :=
    (tendsto_finsetSum Finset.univ (fun j _ => hCol j)).const_mul _
  have hSq : ‖v.val.1‖ ^ 2 ≤ K * ∑ j : Fin 3, ‖v.val.2 j‖ ^ 2 :=
    le_of_tendsto_of_tendsto (((continuous_fst.tendsto v.val).comp hLim).norm.pow 2)
      hTotal (Eventually.of_forall hStep)
  calc
    ‖v.val.1‖ ≤ Real.sqrt (K * ∑ j : Fin 3, ‖v.val.2 j‖ ^ 2) := Real.le_sqrt_of_sq_le hSq
    _ = Real.sqrt K * Real.sqrt (∑ j : Fin 3, ‖v.val.2 j‖ ^ 2) := Real.sqrt_mul hK _
    _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.sqrt_nonneg _)

end Thesis
