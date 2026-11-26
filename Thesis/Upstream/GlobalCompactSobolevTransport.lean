module

public import Thesis.Upstream.EuclideanGradientTransform
import StratificationTheory.Foundation.SmoothOpenDomainSobolevPullback
import StratificationTheory.Foundation.SobolevLocalAssembly

/-! Global compact-gradient transport in the actual smooth volume coordinates. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set StratificationTheory
open scoped ContDiff ENNReal

namespace Thesis

/-- The displayed pullback columns under a smooth change of coordinates. -/
@[expose] def ambientGradientPullback {n q : ℕ} (F : Domain n → Domain n)
    (D : Domain n → HarmonicMaps.Gradient n q) (x : Domain n) (i : Fin n) : Ambient q :=
  ∑ j : Fin n, (fderiv ℝ F x (EuclideanSpace.single i 1)) j • D (F x) j

theorem packAmbientGradient_pullback {n q : ℕ} (F : Domain n → Domain n)
    (D : Domain n → HarmonicMaps.Gradient n q) (x : Domain n) :
    packAmbientGradient (ambientGradientPullback F D x) =
      ambientGradientPrecompose n q (fderiv ℝ F x) (packAmbientGradient (D (F x))) := by
  apply PiLp.ext
  intro i
  rw [ambientGradientPrecompose_apply,packAmbientGradient_apply,ambientGradientPullback]
  simp only [packAmbientGradient_apply]

/-- The pullback of a global Sobolev field with compactly supported
gradient is global (W^{1,2}). Its gradient norm is controlled by the
original gradient norm with a constant from the fixed chart and support. -/
theorem exists_memW12_global_volumePreserving_pullback {n q : ℕ}
    (F : Domain n ≃ₜ Domain n) (hF : ContDiff ℝ ∞ (F : Domain n → Domain n))
    (hMP : MeasurePreserving F (volume : Measure (Domain n)) volume)
    (K : Set (Domain n)) (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {u : Domain n → Ambient q} {D : Domain n → HarmonicMaps.Gradient n q},
        MemW12 (⟨univ,isOpen_univ⟩ : OpenDomain n) u D →
        (∀ x ∉ K, D x = 0) →
        MemW12 (⟨univ,isOpen_univ⟩ : OpenDomain n) (u ∘ F) (ambientGradientPullback F D) ∧
          (∫ x, hsNormSq (ambientGradientPullback F D x)) ≤ C^2 * ∫ x, hsNormSq (D x) := by
  let B (x : Domain n) := ambientGradientPrecompose n q (fderiv ℝ F x)
  have hBC : Continuous B := (ambientGradientPrecompose n q).continuous.comp (hF.continuous_fderiv (by simp))
  have hK' : IsCompact (F ⁻¹' K) := F.isCompact_preimage.2 hK
  obtain ⟨M,hM⟩ := hK'.exists_bound_of_continuousOn hBC.continuousOn
  let C := max M 0
  have hC : 0 ≤ C := le_max_right _ _
  refine ⟨C,hC,?_⟩
  intro u D hu hSupp
  have hU : MemLp u 2 (volume : Measure (Domain n)) := by simpa only [Measure.restrict_univ] using hu.2.1
  have hD : ∀ j, MemLp (fun x => D x j) 2 (volume : Measure (Domain n)) :=
    fun j => by simpa only [Measure.restrict_univ] using hu.2.2 j
  let Y (x : Domain n) := packAmbientGradient (D (F x))
  let G := ambientGradientPullback F D
  let Z (x : Domain n) := packAmbientGradient (G x)
  have hYLp : MemLp Y 2 volume :=
    (memLp_packAmbientGradient hD).comp_measurePreserving hMP
  have hZEq (x : Domain n) : Z x = B x (Y x) := packAmbientGradient_pullback F D x
  have hZMeas : AEStronglyMeasurable Z volume := by
    have h := (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      (hBC.aestronglyMeasurable.prodMk hYLp.1)
    exact h.congr (Eventually.of_forall fun x => (hZEq x).symm)
  have hZN (x : Domain n) : ‖Z x‖ ≤ C*‖Y x‖ := by
    by_cases hx : F x ∈ K
    · rw [hZEq]
      exact ((B x).le_opNorm _).trans (mul_le_mul_of_nonneg_right
        ((hM x hx).trans (le_max_left _ _)) (norm_nonneg _))
    · have hy : Y x = 0 := by
        change packAmbientGradient (D (F x)) = 0
        rw [hSupp _ hx]
        rfl
      rw [hZEq,hy,map_zero,norm_zero,mul_zero]
  have hZLp : MemLp Z 2 volume :=
    (hYLp.norm.const_mul C).mono' hZMeas (Eventually.of_forall hZN)
  have hGLp := memLp_of_packAmbientGradient hZLp
  have huF := hU.comp_measurePreserving hMP
  refine ⟨?_,?_⟩
  · apply memW12_of_local_sobolev_pair
      (by simpa only [Measure.restrict_univ] using huF)
      (fun j => by simpa only [Measure.restrict_univ] using hGLp j)
    intro x _
    let V := ballDomain x 1
    refine ⟨1,zero_lt_one,subset_univ _,?_⟩
    obtain ⟨L,hL⟩ := (isCompact_closedBall x 1).exists_bound_of_continuousOn
      (hF.continuous_fderiv (by simp)).continuousOn
    apply memW12_smooth_open_domain_pullback hu V F hF.contDiffOn (mapsTo_univ _ _)
      L (fun y hy => hL y (ball_subset_closedBall hy)) 1 ENNReal.one_ne_top
    rw [Measure.restrict_univ,one_smul]
    exact (Measure.map_mono Measure.restrict_le_self hMP.measurable).trans_eq hMP.map_eq
  · have hAff : (∫ x, ‖Y x‖^2) = ∫ x, hsNormSq (D x) := by
      have h := hMP.integral_comp F.toMeasurableEquiv.measurableEmbedding (fun x => hsNormSq (D x))
      simpa only [Y,norm_packAmbientGradient_sq,Function.comp_def] using h
    rw [← hAff,← integral_const_mul]
    have hI := (memLp_two_iff_integrable_sq_norm hZLp.1).mp hZLp
    have hYI := (memLp_two_iff_integrable_sq_norm hYLp.1).mp hYLp
    have h := integral_mono hI (hYI.const_mul (C^2)) (fun x => by
      have hh := pow_le_pow_left₀ (norm_nonneg _) (hZN x) 2
      rwa [mul_pow] at hh)
    simpa only [Z,G,norm_packAmbientGradient_sq] using h

end Thesis
