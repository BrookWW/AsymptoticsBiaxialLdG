module

public import Thesis.Interpolation.VacuumSphereSobolevLift
public import HarmonicMaps.Analysis.FixedMollifierKernel
import HarmonicMaps.Analysis.BallPolarIntegral
import HarmonicMaps.Analysis.MollificationDistance
import StratificationTheory.Foundation.SphereGradientData
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-! Uniform vacuum-tube entry of the mollified critical sphere maps. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set StratificationTheory
open scoped ContDiff ENNReal Matrix.Norms.Frobenius Topology

namespace Thesis

private theorem uniform_cap_integral_small
    {F : UnitBoundarySphere 3 → ℝ} (hF : Integrable F (unitBoundarySurface 3))
    (hF₀ : ∀ z, 0 ≤ F z) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > (0 : ℝ), ∀ z : UnitBoundarySphere 3,
      (∫ w in ball z δ, F w ∂unitBoundarySurface 3) < ε := by
  let μ := unitBoundarySurface 3
  let ν := μ.withDensity (fun z => ENNReal.ofReal (F z))
  letI : NullSingletonClass μ := by
    change NullSingletonClass (Measure.euclideanHausdorffMeasure (3-1) :
      Measure (UnitBoundarySphere 3))
    letI : NullSingletonClass (Measure.hausdorffMeasure (↑(3-1 : ℕ)) : Measure (UnitBoundarySphere 3)) :=
      Measure.nullSingletonClass_hausdorff (UnitBoundarySphere 3) (by norm_num)
    refine ⟨fun z => ?_⟩
    rw [Measure.euclideanHausdorffMeasure_def,Measure.smul_apply,measure_singleton,smul_zero]
  letI : IsFiniteMeasure ν := ⟨by
    rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
    rw [← ofReal_integral_eq_lintegral_ofReal hF (Eventually.of_forall hF₀)]
    exact ENNReal.ofReal_lt_top⟩
  have hLocal (z : UnitBoundarySphere 3) :
      ∃ U : Set (UnitBoundarySphere 3), z ∈ U ∧ IsOpen U ∧ ν U < ENNReal.ofReal ε := by
    obtain ⟨U,hz,hU,hν⟩ := ({z} : Set (UnitBoundarySphere 3)).exists_isOpen_lt_of_lt
      (μ := ν) (ENNReal.ofReal ε) (by rw [measure_singleton]; exact ENNReal.ofReal_pos.mpr hε)
    exact ⟨U,hz (mem_singleton z),hU,hν⟩
  choose U hz hU hν using hLocal
  letI : CompactSpace (UnitBoundarySphere 3) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere (0 : Domain 3) 1)
  obtain ⟨δ,hδ,hLeb⟩ := lebesgue_number_lemma_of_metric (s := univ) isCompact_univ hU
    (fun z _ => mem_iUnion.mpr ⟨z,hz z⟩)
  refine ⟨δ,hδ,?_⟩
  intro z
  obtain ⟨j,hj⟩ := hLeb z (mem_univ _)
  have h := (measure_mono (μ := ν) hj).trans_lt (hν j)
  rw [withDensity_apply _ measurableSet_ball,← ofReal_integral_eq_lintegral_ofReal hF.restrict
    (Eventually.of_forall hF₀)] at h
  exact (ENNReal.ofReal_lt_ofReal_iff hε).mp h

private theorem small_radial_ball_angular_cap
    (base : UnitBoundarySphere 3) {x : Point} (hx : 1/2 ≤ ‖x‖)
    {r h : ℝ} (hr : 0 < r) (θ : UnitBoundarySphere 3)
    (hNear : r • θ.val ∈ ball x h) :
    r ∈ Ioo (‖x‖-h) (‖x‖+h) ∧
      θ ∈ ball (sphereRadialDirection base x) (4*h) := by
  have hxN : x ≠ 0 := norm_ne_zero_iff.mp ((by norm_num : 0 < (1/2 : ℝ)).trans_le hx).ne'
  let z := sphereRadialDirection base x
  have hz : ‖x‖ • z.val = x := by
    change ‖x‖ • (sphereRadialDirection base x).val = _
    rw [sphereRadialDirection,dif_pos hxN]
    exact NormedSpace.norm_smul_normalize x
  have hθ : ‖θ.val‖ = 1 := mem_sphere_zero_iff_norm.mp θ.property
  have hrN : ‖r • θ.val‖ = r := by rw [norm_smul,Real.norm_of_nonneg hr.le,hθ,mul_one]
  have hClose := mem_ball.mp hNear
  have hRad := abs_norm_sub_norm_le (r • θ.val) x
  rw [hrN,← dist_eq_norm] at hRad
  have hAbs : |r-‖x‖| < h := hRad.trans_lt hClose
  refine ⟨⟨by linarith only [(abs_lt.mp hAbs).1],by linarith only [(abs_lt.mp hAbs).2]⟩,?_⟩
  have hVec : ‖x‖ • (θ.val-z.val) = (‖x‖-r) • θ.val + (r • θ.val-x) := by
    rw [smul_sub,hz,sub_smul]
    abel
  have hBound := norm_add_le ((‖x‖-r) • θ.val) (r • θ.val-x)
  rw [← hVec,norm_smul,Real.norm_of_nonneg (norm_nonneg x),norm_smul,Real.norm_eq_abs,
    hθ,mul_one,abs_sub_comm] at hBound
  rw [dist_eq_norm] at hClose
  have hD : ‖x‖ * ‖θ.val-z.val‖ < 2*h := hBound.trans_lt (by linarith only [hAbs,hClose])
  have hHalf := mul_le_mul_of_nonneg_right hx (norm_nonneg (θ.val-z.val))
  change dist θ z < 4*h
  rw [Subtype.dist_eq,dist_eq_norm]
  linarith only [hD,hHalf]

/-- In three dimensions the radial Euler factor cancels the angular
gradient scaling, leaving a radial interval of length at most 2h. -/
theorem sphericalRadial_ball_energy_le
    {q : ℕ} {D : Point → HarmonicMaps.Gradient 3 q} {A : UnitBoundarySphere 3 → HarmonicMaps.Gradient 3 q}
    (base : UnitBoundarySphere 3)
    (hD : ∀ (r : PositiveRadius) (θ : UnitBoundarySphere 3) (i : Fin 3), D (r.val • θ.val) i = r.val⁻¹ • A θ i)
    (hA : Integrable (fun θ => hsNormSq (A θ)) (unitBoundarySurface 3))
    {x : Point} (hx : 1/2 ≤ ‖x‖) {h : ℝ} (hh : 0 < h) (hh₀ : h ≤ 1/4)
    (hI : IntegrableOn (fun y => hsNormSq (D y)) (ball x h)) :
    (∫ y in ball x h, hsNormSq (D y)) ≤
      2*h*∫ θ in ball (sphereRadialDirection base x) (4*h), hsNormSq (A θ)
        ∂unitBoundarySurface 3 := by
  let U := ball x h
  let J := Ioo (‖x‖-h) (‖x‖+h)
  let K := ball (sphereRadialDirection base x) (4*h)
  let G (θ : UnitBoundarySphere 3) := hsNormSq (A θ)
  let g := U.indicator (fun y => hsNormSq (D y))
  let M := ∫ θ in K, G θ ∂unitBoundarySurface 3
  have hgI : Integrable g volume := (integrable_indicator_iff measurableSet_ball).mpr hI
  have hG (θ : UnitBoundarySphere 3) : 0 ≤ G θ := hsNormSq_nonneg _
  have hM : 0 ≤ M := integral_nonneg hG
  have hJ : J ⊆ Ioi (0 : ℝ) := fun r hr => by
    have hLower : ‖x‖-h < r := hr.1
    change 0 < r
    linarith only [hLower,hx,hh₀]
  have hMeasG : Integrable (K.indicator G) (unitBoundarySurface 3) :=
    (integrable_indicator_iff measurableSet_ball).mpr hA.restrict
  rw [← integral_indicator measurableSet_ball,integral_eq_polar (by decide : 0 < 3) hgI (0 : Point)]
  rw [← euclideanHausdorffMeasure_unitSphere_eq_toSphere (by decide : 0 < 3)]
  simp only [zero_add,Nat.reduceSub]
  have hPolar (r : ℝ) (hr : 0 < r) :
      r^2*(∫ θ : UnitBoundarySphere 3, g (r • θ.val) ∂unitBoundarySurface 3) ≤
        J.indicator (fun _ => M) r := by
    by_cases hrJ : r ∈ J
    · rw [indicator_of_mem hrJ,← integral_const_mul]
      change _ ≤ ∫ θ in K, G θ ∂unitBoundarySurface 3
      rw [← integral_indicator measurableSet_ball]
      apply integral_mono_of_nonneg
        (Eventually.of_forall fun θ => mul_nonneg (sq_nonneg _) (indicator_nonneg
          (fun y _ => hsNormSq_nonneg (D y)) _)) hMeasG
      refine Eventually.of_forall fun θ => ?_
      change r^2 * g (r • θ.val) ≤ K.indicator G θ
      by_cases hθ : r • θ.val ∈ U
      · have hC := (small_radial_ball_angular_cap base hx hr θ hθ).2
        rw [show g (r • θ.val) = hsNormSq (D (r • θ.val)) from indicator_of_mem hθ _,
          indicator_of_mem hC]
        have hEner : hsNormSq (D (r • θ.val)) = r⁻¹^2*G θ := by
          unfold hsNormSq
          simp only [G,hD ⟨r,hr⟩ θ,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hr.le),mul_pow]
          change (∑ i : Fin 3, r⁻¹^2 * ‖A θ i‖^2) = r⁻¹^2 * ∑ i : Fin 3, ‖A θ i‖^2
          rw [Finset.mul_sum]
        rw [hEner]
        have he : r^2*(r⁻¹^2*G θ) = G θ := by field_simp [hr.ne']
        rw [he]
      · rw [show g (r • θ.val) = 0 from indicator_of_notMem hθ _,mul_zero]
        exact indicator_nonneg (fun θ _ => hG θ) _
    · rw [indicator_of_notMem hrJ]
      have he : (fun θ : UnitBoundarySphere 3 => g (r • θ.val)) = fun _ => (0 : ℝ) := by
        funext θ
        apply indicator_of_notMem
        intro hC
        exact hrJ (small_radial_ball_angular_cap base hx hr θ hC).1
      rw [he,integral_zero,mul_zero]
  calc
    _ ≤ ∫ r in Ioi (0 : ℝ), J.indicator (fun _ => M) r := by
      apply integral_mono_of_nonneg
      · exact Eventually.of_forall fun r => mul_nonneg (sq_nonneg _)
          (integral_nonneg (fun θ => indicator_nonneg (fun y _ => hsNormSq_nonneg (D y)) (r • θ.val)))
      · exact ((integrable_indicator_iff measurableSet_Ioo).mpr
          (integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top))).restrict
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
        exact hPolar r hr
    _ = 2*h*M := by
      have hJmeasure : volume.real J = 2*h := by
        dsimp only [J]
        rw [measureReal_def,Real.volume_Ioo,ENNReal.toReal_ofReal]
        · ring
        · linarith only [hh]
      rw [integral_indicator measurableSet_Ioo,Measure.restrict_restrict_of_subset hJ,
        setIntegral_const,smul_eq_mul,hJmeasure]

private theorem sourceMollification_targetDistance_sq_le_scaledLocalEnergy
    {q : ℕ} (N : CompactSmoothEmbeddedTarget q)
    {u : Point → Ambient q} {D : Point → HarmonicMaps.Gradient 3 q}
    (x : Point) (h : PositiveRadius) (hu : MemW12 (ballDomain x h.val) u D)
    (hN : ∀ᵐ z ∂volume.restrict (ball x h.val), u z ∈ N.carrierSet) :
    Metric.infDist (∫ y in ball (0 : Point) 1, fixedMollifierKernel 3 y • u (x-h.val • y))
        N.carrierSet ^ 2 ≤
      fixedMollifierKernelBound 3 * 16 * h.val⁻¹ * ∫ y in ball x h.val, hsNormSq (D y) := by
  letI : IsFiniteMeasure (volume.restrict (ballDomain x h.val).val) :=
    isFiniteMeasure_restrict.mpr measure_ball_ne_top
  let b := ⨍ y in ball x h.val, u y
  let f (y : Point) := u (x-h.val • y)
  have hf : MemLp f 2 (fixedMollifierProbability 3) :=
    mollification_sampling_memLp_probability h x hu.2.1
  have hNp : ∀ᵐ y ∂fixedMollifierProbability 3, f y ∈ N.carrierSet :=
    ae_fixedMollifierProbability_of_ae_unitBall (ae_mollification_sampling_ball h x hN)
  have hvar : IntegrableOn (fun z => ‖u z-b‖^2) (ball x h.val) :=
    (hu.2.1.sub (memLp_const b)).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
  have hKernel := mollification_local_kernel_estimate h x hvar
    (Eventually.of_forall fun z => sq_nonneg ‖u z-b‖) (fixedMollifierKernel_le_bound 3)
  have hP := hu.poincare_ball h.property
  calc
    _ = Metric.infDist (∫ y, f y ∂fixedMollifierProbability 3) N.carrierSet ^ 2 := by
      rw [fixedMollifierProbability_integral_eq_setIntegral]
    _ ≤ ∫ y, ‖f y-∫ z, f z ∂fixedMollifierProbability 3‖ ^2 ∂fixedMollifierProbability 3 :=
      probability_infDist_sq_le_variance _ hf _ hNp
    _ ≤ ∫ y, ‖f y-b‖ ^2 ∂fixedMollifierProbability 3 :=
      probability_variance_le _ hf b
    _ = ∫ y in ball (0 : Point) 1, fixedMollifierKernel 3 y * ‖u (x-h.val • y)-b‖ ^2 := by
      rw [fixedMollifierProbability_integral_eq_setIntegral]
      simp only [f,smul_eq_mul]
    _ ≤ fixedMollifierKernelBound 3 * (h.val^3)⁻¹ * ∫ z in ball x h.val, ‖u z-b‖^2 :=
      hKernel.2
    _ ≤ fixedMollifierKernelBound 3 * (h.val^3)⁻¹ *
        (16*h.val^2*∫ y in ball x h.val, hsNormSq (D y)) := by
      have hK : 0 ≤ fixedMollifierKernelBound 3 * (h.val^3)⁻¹ :=
        mul_nonneg (fixedMollifierKernelBound_pos 3).le (inv_nonneg.mpr (pow_nonneg h.property.le _))
      apply mul_le_mul_of_nonneg_left _ hK
      norm_num only [Nat.reduceAdd] at hP
      exact hP
    _ = _ := by
      field_simp [h.property.ne']

/-- For the same radial Sobolev graph, every sufficiently small positive
smoothing scale puts the entire fixed shell in the prescribed vacuum tube. -/
theorem exists_uniform_sphericalVacuum_mollificationTube
    (a : BulkCoefficients) (base : UnitBoundarySphere 3) {u : Point → Ambient 5}
    {D : Point → HarmonicMaps.Gradient 3 5} {A : UnitBoundarySphere 3 → HarmonicMaps.Gradient 3 5}
    (hu : MemW12Loc ⟨({0}ᶜ : Set Point),isOpen_compl_singleton⟩ u D)
    (hVac : ∀ x : Point, x ≠ 0 → u x ∈ (vacuumCompactSmoothEmbeddedTarget a).carrierSet)
    (hD : ∀ (r : PositiveRadius) (θ : UnitBoundarySphere 3) (i : Fin 3), D (r.val • θ.val) i = r.val⁻¹ • A θ i)
    (hA : ∀ i : Fin 3, MemLp (fun θ => A θ i) 2 (unitBoundarySurface 3))
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ δ > (0 : ℝ), ∀ (h : PositiveRadius), h.val < δ → ∀ x : Point, ‖x‖ ∈ Icc (3/4 : ℝ) (5/4) →
      Metric.infDist (∫ y in ball (0 : Point) 1, fixedMollifierKernel 3 y • u (x-h.val • y))
        (vacuumCompactSmoothEmbeddedTarget a).carrierSet < ρ := by
  let H (θ : UnitBoundarySphere 3) := hsNormSq (A θ)
  have hH : Integrable H (unitBoundarySurface 3) := by
    change Integrable (fun θ => ∑ i : Fin 3, ‖A θ i‖^2) (unitBoundarySurface 3)
    exact integrable_finsetSum _ (fun i _ => (hA i).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0))
  let K := fixedMollifierKernelBound 3 * 16
  have hK : 0 < K := mul_pos (fixedMollifierKernelBound_pos 3) (by norm_num)
  let ε := ρ^2/(4*K)
  have hε : 0 < ε := div_pos (sq_pos_of_pos hρ) (mul_pos (by norm_num) hK)
  obtain ⟨η,hη,hcap⟩ := uniform_cap_integral_small hH (fun θ => hsNormSq_nonneg (A θ)) hε
  let δ := min (1/4 : ℝ) (η/4)
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos hη (by norm_num))
  refine ⟨δ,hδ,?_⟩
  intro h hh x hx
  have hSmall : h.val < 1/4 := hh.trans_le (min_le_left _ _)
  have hC : closedBall x h.val ⊆ ({0}ᶜ : Set Point) := by
    intro y hy h0
    have hz := mem_singleton_iff.mp h0
    have hY := mem_closedBall.mp hy
    rw [hz,dist_zero_left] at hY
    linarith only [hY,hx.1,hSmall]
  have huBall := hu.memW12_ball hC
  have hVacB : ∀ᵐ z ∂volume.restrict (ball x h.val), u z ∈ (vacuumCompactSmoothEmbeddedTarget a).carrierSet := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    exact hVac z (fun he => hC (ball_subset_closedBall hz) (mem_singleton_iff.mpr he))
  have hScale : 4*h.val ≤ η := by
    have hh' := hh.trans_le (min_le_right _ _)
    linarith only [hh']
  let z := sphereRadialDirection base x
  have hHS : (∫ θ in ball z (4*h.val), H θ ∂unitBoundarySurface 3) < ε :=
    (setIntegral_mono_set hH.restrict (Eventually.of_forall fun z' => hsNormSq_nonneg (A z'))
      (Eventually.of_forall (ball_subset_ball hScale))).trans_lt (hcap z)
  have hE := sphericalRadial_ball_energy_le base hD hH (show 1/2 ≤ ‖x‖ by linarith only [hx.1])
    h.property hSmall.le huBall.integrable_hsNormSq
  have hDist := sourceMollification_targetDistance_sq_le_scaledLocalEnergy (vacuumCompactSmoothEmbeddedTarget a)
    x h huBall hVacB
  have hCst : 0 ≤ K*h.val⁻¹ := mul_nonneg hK.le (inv_nonneg.mpr h.property.le)
  have hErr := mul_le_mul_of_nonneg_left hE hCst
  have hEq : K*h.val⁻¹*(2*h.val*∫ θ in ball z (4*h.val), H θ ∂unitBoundarySurface 3) =
      2*K*∫ θ in ball z (4*h.val), H θ ∂unitBoundarySurface 3 := by field_simp [h.property.ne']
  rw [hEq] at hErr
  apply (sq_lt_sq₀ Metric.infDist_nonneg hρ.le).mp
  refine (hDist.trans hErr).trans_lt ((mul_lt_mul_of_pos_left hHS (by positivity : 0 < 2*K)).trans_le ?_)
  dsimp only [ε]
  have hEq : 2*K*(ρ^2/(4*K)) = ρ^2/2 := by
    field_simp [hK.ne']
    norm_num
  rw [hEq]
  linarith only [sq_nonneg ρ]

end Thesis
