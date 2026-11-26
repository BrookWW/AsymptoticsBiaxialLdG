module

public import SupportingAnalysis.Calculus.RealLine
public import HolderToCK.Analysis.ClassicalEquation
public import HolderToCK.Analysis.Harmonic.RadialMean
public import HolderToCK.Analysis.Poisson.WeakHarmonicMean

/-! Radial averaging for scalar classical harmonic functions via the HolderToCK sphere mean. -/

public section

open MeasureTheory Metric Set Filter InnerProductSpace
open scoped ContDiff ENNReal Topology

set_option autoImplicit false

namespace SupportingAnalysis

variable {d : ℕ}

private theorem holder_sphere_integral_of_harmonicOnNhd {u : E d → E 1} (hd : 2 ≤ d)
    (a : E d) {r s : ℝ} (hs : 0 < s) (hsr : s < r)
    (hu : ContDiffOn ℝ 2 u (ball a r))
    (hLap : ∀ x ∈ ball a r, Laplacian.laplacian u x = 0) :
    (∫ θ : sphere (0 : E d) 1, u (a + s • θ.val)
      ∂(volume : Measure (E d)).toSphere) =
      (volume : Measure (E d)).toSphere.real univ • u a := by
  let R := (r + s) / 2
  let Ω := HarmonicMaps.ballDomain a R
  let Ωlarge := HarmonicMaps.ballDomain a r
  have hRr : R < r := by dsimp [R]; linarith
  have hRs : s < R := by dsimp [R]; linarith
  have hclosed : closedBall a R ⊆ ball a r := closedBall_subset_ball hRr
  have hsub : ball a R ⊆ ball a r := ball_subset_ball hRr.le
  have huSmall : ContDiffOn ℝ 2 u Ω.val := hu.mono hsub
  have huOne : ContDiffOn ℝ 1 u (ball a r) := hu.of_le (by norm_num)
  have hmeasure : (volume : Measure (E d)).restrict (ball a R) ≤ volume.restrict (closedBall a R) :=
    Measure.restrict_mono_set volume ball_subset_closedBall
  let Du : E d → HarmonicMaps.Gradient d 1 := fun x i => fderiv ℝ u x (EuclideanSpace.single i 1)
  have hweak : HarmonicMaps.MemW12 Ω u Du := by
    refine ⟨HolderToCK.hasWeakGradient_of_contDiffOn_one Ω (huOne.mono hsub), ?_, ?_⟩
    · exact ((HolderToCK.continuousOn_locallyMemL2 (Ω := Ωlarge) hu.continuousOn)
        _ (isCompact_closedBall _ _) hclosed).mono_measure hmeasure
    · intro i
      have hc : ContinuousOn (fun x => Du x i) (ball a r) :=
        (huOne.continuousOn_fderiv_of_isOpen isOpen_ball le_rfl).clm_apply continuousOn_const
      exact ((HolderToCK.continuousOn_locallyMemL2 (Ω := Ωlarge) hc)
        _ (isCompact_closedBall _ _) hclosed).mono_measure hmeasure
  have hEq : HolderToCK.WeakPoissonOn Ω Du (fun _ => 0) :=
    HolderToCK.weakPoissonOn_of_contDiffOn_two_of_laplacian_eq Ω huSmall
      (fun x hx => hLap x (hsub hx))
  exact hEq.harmonic_sphere_integral_eq_of_continuous hd a hweak
    huSmall.continuousOn ⟨s, hs⟩ hRs

/-- The scalar radial probability averaging principle in the shape used by the compact potential. -/
theorem holder_harmonic_radial_probability_mean (hd : 2 ≤ d)
    (u : E d → ℝ) (a : E d) (r : ℝ) (ρ : E d → ℝ)
    (hr : 0 < r) (hu : HarmonicOnNhd u (closedBall a r)) (hρ : Continuous ρ)
    (hRad : ∃ profile : ℝ → ℝ, ∀ y, ρ y = profile ‖y‖)
    (_hNonneg : ∀ y, 0 ≤ ρ y) (hSupp : Function.support ρ ⊆ ball 0 r)
    (hMass : (∫ y, ρ y) = 1) : (∫ y, ρ y * u (a - y)) = u a := by
  let i : Fin d := ⟨0, by omega⟩
  let e : E d := EuclideanSpace.single i 1
  have hNormE : ‖e‖ = 1 := by
    simp only [e, EuclideanSpace.single, PiLp.norm_single, norm_one]
  let κ : ℝ → ℝ := fun t => ρ (t • e)
  have hκ : Continuous κ := by
    have hC : Continuous (fun t : ℝ => t • e) := continuous_id.smul continuous_const
    exact hρ.comp hC
  obtain ⟨profile, hProfile⟩ := hRad
  have hRho (z : E d) : κ ‖z‖ = ρ z := by
    rw [show κ ‖z‖ = ρ (‖z‖ • e) from rfl, hProfile (‖z‖ • e), hProfile z,
      norm_smul, Real.norm_of_nonneg (norm_nonneg z), hNormE, mul_one]
  have hκZero (t : ℝ) (ht : r ≤ t) : κ t = 0 := by
    have hNot : t • e ∉ ball (0 : E d) r := by
      simp only [mem_ball, dist_zero_right, norm_smul, Real.norm_of_nonneg (hr.le.trans ht),
        hNormE, mul_one, not_lt]
      exact ht
    exact Function.notMem_support.mp (fun hs => hNot (hSupp hs))
  let L : ℝ ≃L[ℝ] E 1 := realLineEuclideanIso.symm.toContinuousLinearEquiv
  let v := L ∘ u
  have hv : ContDiffOn ℝ 2 v (closedBall a r) := L.contDiff.comp_contDiffOn hu.contDiffOn
  have hLap (x : E d) (hx : x ∈ ball a r) : Laplacian.laplacian v x = 0 := by
    have hh := hu x (ball_subset_closedBall hx)
    show Laplacian.laplacian (L.toContinuousLinearMap ∘ u) x = 0
    rw [hh.1.laplacian_CLM_comp_left]
    change L (Laplacian.laplacian u x) = 0
    rw [hh.2.eq_of_nhds, Pi.zero_apply, map_zero]
  have hSphere (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) r) :
      (∫ θ : sphere (0 : E d) 1, v (a + s • θ.val)
        ∂(volume : Measure (E d)).toSphere) =
        (volume : Measure (E d)).toSphere.real univ • v a :=
    holder_sphere_integral_of_harmonicOnNhd hd a hs.1 hs.2
      (hv.mono ball_subset_closedBall) hLap
  have hV := HolderToCK.radial_kernel_convolution_eq_of_sphereMean
    (by omega : 0 < d) a ⟨r, hr⟩ v hv.continuousOn κ hκ hκZero hSphere
  simp_rw [hRho, hMass, one_smul] at hV
  have hSample (z : E d) (hz : z ∈ closedBall 0 r) : a - z ∈ closedBall a r := by
    have hh : a - z - a = -z := by abel
    rw [mem_closedBall, dist_eq_norm, hh, norm_neg]
    simpa only [mem_closedBall, dist_zero_right] using hz
  have hRef : ContinuousOn (fun z => u (a - z)) (closedBall 0 r) := by
    have hC : Continuous (fun z : E d => a - z) := by fun_prop
    exact hu.contDiffOn.continuousOn.comp hC.continuousOn (fun z hz => hSample z hz)
  have hInt : Integrable (fun z => ρ z * u (a - z)) := by
    apply (integrableOn_iff_integrable_of_support_subset (s := closedBall 0 r) ?_).mp
      ((hρ.continuousOn.mul hRef).integrableOn_compact (isCompact_closedBall _ _))
    intro z hz
    exact ball_subset_closedBall (hSupp (Function.support_mul_subset_left _ _ hz))
  apply L.injective
  calc
    _ = ∫ z, L (ρ z * u (a - z)) := (L.toContinuousLinearMap.integral_comp_comm hInt).symm
    _ = L (u a) := by
      simpa only [v, Function.comp_apply, ← smul_eq_mul, map_smul] using hV

end SupportingAnalysis
