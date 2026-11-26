module

public import Thesis.Interpolation.VacuumSphereSobolevLift
public import Thesis.Foundation.VacuumCoordinateRetraction
import StratificationTheory.Frozen.SphereGradientCharacterization
import StratificationTheory.Foundation.AngularGradientUniqueness
import StratificationTheory.Foundation.RadialSobolevPullback
import HarmonicMaps.Analysis.SobolevPostcompositionLocal
import HarmonicMaps.Analysis.SobolevPostcompositionBasic
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-! The native angular columns under the bounded vacuum projection. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set StratificationTheory
open scoped ContDiff ENNReal Topology Matrix.Norms.Frobenius

namespace Thesis

theorem sphericalGradient_ae_eq_of_radial_columns
    {q : ℕ} {v : UnitBoundarySphere 3 → Ambient q} (hv : MemSphereW12 (by decide : 2 ≤ 3) v)
    {w : Point → Ambient q} {D : Point → HarmonicMaps.Gradient 3 q}
    {A : UnitBoundarySphere 3 → HarmonicMaps.Gradient 3 q}
    (hw : MemW12Loc ⟨({0}ᶜ : Set Point),isOpen_compl_singleton⟩ w D)
    (hRay : ∀ (r : PositiveRadius) (θ : UnitBoundarySphere 3), w (r.val • θ.val) = v θ)
    (hD : ∀ (r : PositiveRadius) (θ : UnitBoundarySphere 3) (i : Fin 3), D (r.val • θ.val) i = r.val⁻¹ • A θ i)
    (i : Fin 3) :
    (fun θ => (sphereGradient (by decide : 2 ≤ 3) v hv i) θ) =ᵐ[unitBoundarySurface 3]
      fun θ => A θ i := by
  obtain ⟨g,E,hg,hgRay,hScaled⟩ := (sphereGradient_characterization (by decide : 2 ≤ 3) v hv).1.1
  have hSurf : unitBoundarySurface 3 = (volume : Measure Point).toSphere :=
    euclideanHausdorffMeasure_unitSphere_eq_toSphere (by decide : 0 < 3)
  have hFormula (ρ : PositiveRadius) (j : Fin 3) :
      (fun θ : UnitBoundarySphere 3 => E (ρ.val • θ.val) j) =ᵐ[(volume : Measure Point).toSphere]
        fun θ => ρ.val⁻¹ • (sphereGradient (by decide : 2 ≤ 3) v hv j) θ := by
    rw [← hSurf]
    filter_upwards [hScaled ρ j] with θ h
    change ρ.val • E (ρ.val • θ.val) j = (sphereGradient (by decide : 2 ≤ 3) v hv j) θ at h
    rw [← h,smul_smul,inv_mul_cancel₀ ρ.property.ne',one_smul]
  rw [hSurf]
  exact angular_radial_gradient_ae_eq_of_ae_formula (by decide : 0 < 3) hg hw hgRay hRay
    hFormula (fun r j => Eventually.of_forall fun θ => hD r θ j) i

theorem sphericalProjected_weakColumn_fixed
    {v : UnitBoundarySphere 3 → Ambient 5}
    {w : Point → Ambient 5} {D : Point → HarmonicMaps.Gradient 3 5}
    {A : UnitBoundarySphere 3 → HarmonicMaps.Gradient 3 5}
    (hw : MemW12Loc ⟨({0}ᶜ : Set Point),isOpen_compl_singleton⟩ w D)
    (hRay : ∀ (r : PositiveRadius) (θ : UnitBoundarySphere 3), w (r.val • θ.val) = v θ)
    (hD : ∀ (r : PositiveRadius) (θ : UnitBoundarySphere 3) (i : Fin 3), D (r.val • θ.val) i = r.val⁻¹ • A θ i)
    (Q : Ambient 5 → Ambient 5) (hQ : ContDiff ℝ ∞ Q) {L : ℝ}
    (hQD : ∀ x, ‖fderiv ℝ Q x‖ ≤ L) (hFix : ∀ θ, Q (v θ) = v θ)
    (i : Fin 3) :
    (fun θ => fderiv ℝ Q (v θ) (A θ i)) =ᵐ[unitBoundarySurface 3] fun θ => A θ i := by
  let E (x : Point) (j : Fin 3) := fderiv ℝ Q (w x) (D x j)
  let B (θ : UnitBoundarySphere 3) (j : Fin 3) := fderiv ℝ Q (v θ) (A θ j)
  have hW : MemW12Loc ⟨({0}ᶜ : Set Point),isOpen_compl_singleton⟩ (Q ∘ w) E :=
    hw.postcompose Q hQ L hQD
  have hQR (r : PositiveRadius) (θ : UnitBoundarySphere 3) : (Q ∘ w) (r.val • θ.val) = v θ := by
    rw [Function.comp_apply,hRay,hFix]
  have hE (r : PositiveRadius) (j : Fin 3) :
      (fun θ : UnitBoundarySphere 3 => E (r.val • θ.val) j) =ᵐ[(volume : Measure Point).toSphere]
        fun θ => r.val⁻¹ • B θ j := by
    refine Eventually.of_forall fun θ => ?_
    change fderiv ℝ Q (w (r.val • θ.val)) (D (r.val • θ.val) j) = _
    rw [hRay,hD,map_smul]
  have hSurf : unitBoundarySurface 3 = (volume : Measure Point).toSphere :=
    euclideanHausdorffMeasure_unitSphere_eq_toSphere (by decide : 0 < 3)
  rw [hSurf]
  exact angular_radial_gradient_ae_eq_of_ae_formula (by decide : 0 < 3) hW hw hQR hRay
    hE (fun r j => Eventually.of_forall fun θ => hD r θ j) i

/-- On each column, the smooth bounded projection preserves the angular
strong convergence at the same sequence of values. -/
theorem tendsto_sphericalProjection_column
    {m : ℕ → UnitBoundarySphere 3 → Ambient 5} {v : UnitBoundarySphere 3 → Ambient 5}
    {Z : ℕ → UnitBoundarySphere 3 → Ambient 5} {A : UnitBoundarySphere 3 → Ambient 5}
    (hm : ∀ k, AEStronglyMeasurable (m k) (unitBoundarySurface 3))
    (hv : AEStronglyMeasurable v (unitBoundarySurface 3))
    (hZ : ∀ k, MemLp (Z k) 2 (unitBoundarySurface 3))
    (hA : MemLp A 2 (unitBoundarySurface 3))
    (hValue : ∀ᵐ θ ∂unitBoundarySurface 3, Tendsto (fun k => m k θ) atTop (𝓝 (v θ)))
    (hConv : Tendsto (fun k => eLpNorm (Z k-A) 2 (unitBoundarySurface 3)) atTop (𝓝 0))
    {Q : Ambient 5 → Ambient 5} (hQ : ContDiff ℝ ∞ Q) {L : ℝ} (hQD : ∀ z, ‖fderiv ℝ Q z‖ ≤ L) :
    Tendsto (fun k => eLpNorm (fun θ => fderiv ℝ Q (m k θ) (Z k θ)-fderiv ℝ Q (v θ) (A θ))
      2 (unitBoundarySurface 3)) atTop (𝓝 0) := by
  let μ := unitBoundarySurface 3
  let E (k : ℕ) (θ : UnitBoundarySphere 3) := fderiv ℝ Q (m k θ) (Z k θ-A θ)
  let F (k : ℕ) (θ : UnitBoundarySphere 3) :=
    (fderiv ℝ Q (m k θ)-fderiv ℝ Q (v θ)) (A θ)
  have hEM (k : ℕ) : MemLp (E k) 2 μ := memLp_postcomposition_column (hm k) ((hZ k).sub hA) hQ hQD
  have hFM (k : ℕ) : AEStronglyMeasurable (F k) μ :=
    (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      ((((hQ.continuous_fderiv (by simp)).comp_aestronglyMeasurable (hm k)).sub
        ((hQ.continuous_fderiv (by simp)).comp_aestronglyMeasurable hv)).prodMk
        hA.aestronglyMeasurable)
  have hFbound (k : ℕ) : ∀ᵐ θ ∂μ, ‖F k θ‖ ≤ (2*L)*‖A θ‖ := by
    refine Eventually.of_forall fun θ => (ContinuousLinearMap.le_opNorm _ _).trans ?_
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact (norm_sub_le _ _).trans (by linarith only [hQD (m k θ),hQD (v θ)])
  have hFL : Tendsto (fun k => eLpNorm (F k) 2 μ) atTop (𝓝 0) := by
    apply tendsto_eLpNorm_two_zero_of_dominated hFM hA hFbound
    filter_upwards [hValue] with θ hθ
    have hD := (hQ.continuous_fderiv (by simp)).continuousAt.tendsto.comp hθ
    have hZero : Tendsto (fun k => fderiv ℝ Q (m k θ)-fderiv ℝ Q (v θ)) atTop (𝓝 0) := by
      simpa only [sub_self,Function.comp_def] using
        hD.sub (tendsto_const_nhds (x := fderiv ℝ Q (v θ)))
    have h := (ContinuousLinearMap.apply ℝ (Ambient 5) (A θ)).continuous.tendsto 0 |>.comp hZero
    simpa only [F,Function.comp_def,ContinuousLinearMap.apply_apply,zero_apply] using h
  have hEL : Tendsto (fun k => eLpNorm (E k) 2 μ) atTop (𝓝 0) := by
    have h := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal L) hConv (Or.inr ENNReal.ofReal_ne_top)
    have hU : Tendsto (fun k => ENNReal.ofReal L*eLpNorm (Z k-A) 2 μ) atTop (𝓝 0) := by
      simpa only [mul_zero] using h
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hU (fun _ => bot_le)
    intro k
    apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul (p := 2)
    refine Eventually.of_forall fun θ => (ContinuousLinearMap.le_opNorm _ _).trans ?_
    exact mul_le_mul_of_nonneg_right (hQD (m k θ)) (norm_nonneg _)
  have hU : Tendsto (fun k => eLpNorm (E k) 2 μ+eLpNorm (F k) 2 μ) atTop (𝓝 0) := by
    simpa only [zero_add] using hEL.add hFL
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hU (fun _ => bot_le)
  intro k
  have he : (fun θ => fderiv ℝ Q (m k θ) (Z k θ)-fderiv ℝ Q (v θ) (A θ)) = E k+F k := by
    funext θ
    simp only [E,F,Pi.add_apply,map_sub,sub_apply]
    abel
  change eLpNorm (fun θ => fderiv ℝ Q (m k θ) (Z k θ)-fderiv ℝ Q (v θ) (A θ)) 2 μ ≤ _
  rw [he]
  exact eLpNorm_add_le (hEM k).aestronglyMeasurable (hFM k) (by norm_num)

private theorem integral_normSq_eq_eLpNorm_two_toReal_sq
    {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] {μ : Measure X} {F : X → E}
    (hF : MemLp F 2 μ) :
    (∫ x, ‖F x‖^2 ∂μ) = (eLpNorm F 2 μ).toReal^2 := by
  have hN : eLpNorm F 2 μ = ENNReal.ofReal ((∫ x, ‖F x‖^2 ∂μ) ^ (2 : ℝ)⁻¹) := by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
      hF.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)
  have h₀ : 0 ≤ ∫ x, ‖F x‖^2 ∂μ := integral_nonneg fun _ => sq_nonneg _
  rw [hN,ENNReal.toReal_ofReal (Real.rpow_nonneg h₀ _)]
  exact (Real.rpow_inv_natCast_pow (n := 2) h₀ (by decide)).symm

theorem tendsto_integral_normSq_zero_from_native_L2
    {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] {μ : Measure X} {F : ℕ → X → E}
    (hF : ∀ k, MemLp (F k) 2 μ)
    (h : Tendsto (fun k => eLpNorm (F k) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ x, ‖F k x‖^2 ∂μ) atTop (𝓝 0) := by
  have h' := ((ENNReal.tendsto_toReal (by norm_num : (0 : ℝ≥0∞) ≠ ⊤)).comp h).pow 2
  simpa only [Function.comp_def,ENNReal.toReal_zero,zero_pow (by decide : (2 : ℕ) ≠ 0),
    ← integral_normSq_eq_eLpNorm_two_toReal_sq (hF _)] using h'

theorem tendsto_integral_normSq_from_native_Lp
    {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] {μ : Measure X}
    {f : ℕ → Lp E 2 μ} {g : Lp E 2 μ} (h : Tendsto f atTop (𝓝 g)) :
    Tendsto (fun k => ∫ x, ‖f k x‖^2 ∂μ) atTop (𝓝 (∫ x, ‖g x‖^2 ∂μ)) := by
  have hT := h.norm.pow 2
  simpa only [Lp.norm_def,← integral_normSq_eq_eLpNorm_two_toReal_sq (Lp.memLp _)] using hT

end Thesis
