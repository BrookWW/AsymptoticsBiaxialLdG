module

public import Thesis.StressEnergy
public import Thesis.Foundation.BulkGeometry
public import Thesis.Foundation.WeakGradient
public import Thesis.Upstream.MinimizingSobolev
public import HarmonicMaps.Analysis.RadialStressCentered
public import HarmonicMaps.Analysis.RadiusBoundaryIdentityPolar
public import HarmonicMaps.Analysis.RadialCutoffIntegral
public import HarmonicMaps.Analysis.RadialCutoffWeightedIntegral
public import HarmonicMaps.Analysis.BallEnergyAbsoluteContinuity
public import HarmonicMaps.Analysis.NormalizedEnergyCalculus

/-! Radial Pohozaev identities for the sextic bulk energy. -/

public section

open Set MeasureTheory Filter
open scoped BigOperators ContDiff Topology Matrix Matrix.Norms.Frobenius

namespace Thesis

/-- Squared derivative in the radial direction, defined by zero at the center. -/
noncomputable def radialGradientNormSq (D : Point → Gradient) (a x : Point) : ℝ :=
  ‖‖x - a‖⁻¹ • ∑ i, (x - a) i • D x i‖ ^ 2

private theorem radialGradientNormSq_coordinates (D : Point → Gradient) (a x : Point) :
    radialGradientNormSq D a x =
      ‖‖x - a‖⁻¹ • ∑ i, (x - a) i • frobeniusGradient D x i‖ ^ 2 := by
  unfold radialGradientNormSq
  rw [← frobeniusCoordinateEquiv.norm_map]
  simp only [map_smul, map_sum, frobeniusGradient]

/-- The radial contraction includes the bulk term in the trace of stress. -/
theorem stressTensor_contract_radial (a : BulkCoefficients) (ε : ElasticScale)
    (Q : Point → S0) {η : ℝ → ℝ} (hη : ContDiff ℝ ∞ η)
    (hplateau : ∃ b : ℝ, 0 < b ∧ ∀ t ∈ Ico 0 b, η t = η 0) (c x : Point) :
    let D := ClassicalGradient Q
    let e := energyDensity a ε (Q x) (D x)
    let p := (ε : ℝ)⁻¹ ^ 2 * bulkPotential a (Q x)
    let X : Point → Point := fun y => HarmonicMaps.radialVectorField η (y - c)
    (∑ i, ∑ j, ((fderiv ℝ X x) (axis j)) i * stressTensor a ε Q x i j) =
      η ‖x - c‖ * (e + 2 * p) + ‖x - c‖ * deriv η ‖x - c‖ *
        (e - radialGradientNormSq D c x) := by
  let D := ClassicalGradient Q
  let e := energyDensity a ε (Q x) (D x)
  let p := (ε : ℝ)⁻¹ ^ 2 * bulkPotential a (Q x)
  let X : Point → Point := fun y => HarmonicMaps.radialVectorField η (y - c)
  let A (i j : Fin 3) := (fderiv ℝ X x (axis i)) j
  let g := gradientNormSq (D x)
  let b := ∑ i, ∑ j, frobeniusS0 (D x i) (D x j) * A i j
  let s := ‖x - c‖
  change (∑ i, ∑ j, A j i * stressTensor a ε Q x i j) =
    η s * (e + 2 * p) + s * deriv η s * (e - radialGradientNormSq D c x)
  have hdiv : (∑ i, A i i) = 3 * η s + s * deriv η s := by
    dsimp only [A, X]
    rw [HarmonicMaps.radialVectorField_centered_fderiv hη hplateau c x]
    by_cases hx : x - c = 0
    · dsimp only [s]
      rw [hx, (HarmonicMaps.radialVectorField_hasFDerivAt_zero hplateau).fderiv]
      simp [axis]
    · exact HarmonicMaps.radialVectorField_divergence
        (hη.differentiable (by simp) _) hx
  have hgeom : g * (∑ i, A i i) - 2 * b =
      (η s + s * deriv η s) * g - 2 * (s * deriv η s * radialGradientNormSq D c x) := by
    have hg : HarmonicMaps.hsNormSq (frobeniusGradient D x) = g := by
      simp only [HarmonicMaps.hsNormSq, frobeniusGradient, frobeniusCoordinateEquiv.norm_map,
        g, gradientNormSq_eq_sum_norm_sq]
    have h := HarmonicMaps.radialStressEnergyIdentity_centered
      (frobeniusGradient D) hη hplateau c x
    rw [hg, ← radialGradientNormSq_coordinates] at h
    simpa only [Nat.cast_ofNat, show (3 : ℝ) - 2 = 1 by norm_num, one_mul,
      frobeniusGradient, frobeniusCoordinateEquiv_inner, A, b, s, X, axis] using h
  have hsym (i j : Fin 3) : frobeniusS0 (D x j) (D x i) = frobeniusS0 (D x i) (D x j) := by
    simp only [← frobeniusCoordinateEquiv_inner, real_inner_comm]
  have hexpand : (∑ i, ∑ j, A j i * stressTensor a ε Q x i j) = e * (∑ i, A i i) - b := by
    change (∑ i, ∑ j, A j i * ((if i = j then e else 0) - frobeniusS0 (D x i) (D x j))) = _
    simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    · rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
        rw [hsym i j, mul_comm]
  rw [hexpand, hdiv]
  rw [hdiv] at hgeom
  have he : e = (1 / 2 : ℝ) * g + p := rfl
  rw [he]
  linear_combination (1 / 2 : ℝ) * hgeom

/-- The integral on the sphere of radius `r` in canonical polar coordinates. -/
noncomputable def polarBoundaryIntegral (c : Point) (f : Point → ℝ) (r : ℝ) : ℝ :=
  r ^ 2 * ∫ θ : Metric.sphere (0 : Point) 1, f (c + r • θ.val)
    ∂(volume : Measure Point).toSphere

theorem integrableOn_classicalEnergyDensity_ball (a : BulkCoefficients) (ε : ElasticScale)
    {Ω : Set Point} (hΩ : IsOpen Ω) {Q : Point → S0} (hQ : ContDiffOn ℝ ∞ Q Ω)
    {c : Point} {R : ℝ} (hball : Metric.closedBall c R ⊆ Ω) :
    IntegrableOn (fun x => energyDensity a ε (Q x) (ClassicalGradient Q x))
      (Metric.ball c R) volume :=
  (((contDiffOn_classicalEnergyDensity a ε hΩ hQ).continuousOn.mono hball).integrableOn_compact
    (isCompact_closedBall c R)).mono_set Metric.ball_subset_closedBall

private theorem integral_radial_stressCutoff_eq_zero (a : BulkCoefficients) (ε : ElasticScale)
    {Ω : Set Point} (hΩ : IsOpen Ω) {Q : Point → S0} (hQ : ContDiffOn ℝ ∞ Q Ω)
    (hEuler : ∀ x ∈ Ω, (ε : ℝ) ^ 2 • (laplacian Q x : S0).val = bulkGradient a (Q x))
    {c : Point} {R : ℝ} (hball : Metric.closedBall c R ⊆ Ω)
    (t δ : HarmonicMaps.PositiveRadius) (htδ : t.val + δ.val < R) :
    let D := ClassicalGradient Q
    let e : Point → ℝ := fun x => energyDensity a ε (Q x) (D x)
    let p : Point → ℝ := fun x => (ε : ℝ)⁻¹ ^ 2 * bulkPotential a (Q x)
    let η := HarmonicMaps.radialCutoffProfile t δ
    (∫ x in Metric.ball c R,
      η ‖x - c‖ * (e x + 2 * p x) + ‖x - c‖ * deriv η ‖x - c‖ *
        (e x - radialGradientNormSq D c x)) = 0 := by
  let η := HarmonicMaps.radialCutoffProfile t δ
  let X : Point → Point := fun y => HarmonicMaps.radialVectorField η (y - c)
  have hη := HarmonicMaps.radialCutoffProfile_contDiff t δ
  have hplateau := HarmonicMaps.radialCutoffProfile_plateau t δ
  have hX := HarmonicMaps.radialVectorField_admissible hη hplateau htδ
    (fun _ hr => HarmonicMaps.radialCutoffProfile_eq_zero t δ hr) c
  have hTest : IsSmoothTest Ω X :=
    ⟨hX.1, hX.2.1, hX.2.2.trans (Metric.ball_subset_closedBall.trans hball)⟩
  simp_rw [← stressTensor_contract_radial a ε Q hη hplateau c]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => ?_)]
  · exact integral_stressTensor_contract_eq_zero a ε hΩ hQ hEuler hTest
  · have hx' : x ∉ tsupport X := fun h => hx (hX.2.2 h)
    change (∑ i, ∑ j, ((fderiv ℝ X x) (axis j)) i * stressTensor a ε Q x i j) = 0
    rw [fderiv_of_notMem_tsupport ℝ hx']
    simp only [zero_apply, PiLp.zero_apply, zero_mul, Finset.sum_const_zero]

/-- Radial Pohozaev and the energy derivative use the actual bulk and gradient
densities on the same ball. The energy primitive is absolutely continuous. -/
theorem pohozaev_radius_boundary_identity (a : BulkCoefficients) (ε : ElasticScale)
    {Ω : Set Point} (hΩ : IsOpen Ω) {Q : Point → S0} (hQ : ContDiffOn ℝ ∞ Q Ω)
    (hEuler : ∀ x ∈ Ω, (ε : ℝ) ^ 2 • (laplacian Q x : S0).val = bulkGradient a (Q x))
    {c : Point} {R : ℝ} (hR : 0 < R) (hball : Metric.closedBall c R ⊆ Ω) :
    let D := ClassicalGradient Q
    let e : Point → ℝ := fun x => energyDensity a ε (Q x) (D x)
    let p : Point → ℝ := fun x => (ε : ℝ)⁻¹ ^ 2 * bulkPotential a (Q x)
    let F : ℝ → ℝ := fun r => ∫ x in Metric.ball c r, e x
    AbsolutelyContinuousOnInterval F 0 R ∧
      ∀ᵐ r : ℝ, r ∈ Ioo 0 R →
        HasDerivAt F (polarBoundaryIntegral c e r) r ∧
        r * polarBoundaryIntegral c e r - F r =
          r * polarBoundaryIntegral c (radialGradientNormSq D c) r +
            2 * ∫ x in Metric.ball c r, p x := by
  let D := ClassicalGradient Q
  let e : Point → ℝ := fun x => energyDensity a ε (Q x) (D x)
  let p : Point → ℝ := fun x => (ε : ℝ)⁻¹ ^ 2 * bulkPotential a (Q x)
  let v := radialGradientNormSq D c
  let f : Point → ℝ := fun x => e x + 2 * p x
  let F : ℝ → ℝ := fun r => ∫ x in Metric.ball c r, e x
  let B := Metric.ball c R
  have he : IntegrableOn e B volume := integrableOn_classicalEnergyDensity_ball a ε hΩ hQ hball
  have hp : IntegrableOn p B volume :=
    ((continuousOn_const.mul (((contDiff_bulkPotential a).continuous.comp_continuousOn
      hQ.continuousOn).mono hball)).integrableOn_compact (isCompact_closedBall c R)).mono_set
        Metric.ball_subset_closedBall
  have hv : IntegrableOn v B volume := by
    have hW := (memH1Loc_iff_memW12Loc ⟨Ω, hΩ⟩ Q D).1
      (memH1Loc_of_contDiffOn hΩ (hQ.of_le (by norm_num)))
    rw [show v = _ from funext (radialGradientNormSq_coordinates D c)]
    exact hW.integrable_radial_columns_ball hball
  have hf : IntegrableOn f B volume := he.add (hp.const_mul 2)
  have hn : 0 < 3 := by decide
  have hpolE : IntegrableOn (polarBoundaryIntegral c e) (Ioo 0 R) volume :=
    HarmonicMaps.integrableOn_polar_boundary_density hn he
  have hpolV : IntegrableOn (polarBoundaryIntegral c v) (Ioo 0 R) volume :=
    HarmonicMaps.integrableOn_polar_boundary_density hn hv
  change AbsolutelyContinuousOnInterval F 0 R ∧ _
  refine ⟨HarmonicMaps.absolutelyContinuousOnInterval_integral_ball hn hR.le he, ?_⟩
  filter_upwards [HarmonicMaps.ae_hasDerivAt_integral_ball hn hR.le he,
    HarmonicMaps.ae_tendsto_integral_radius_mul_radialCutoff_derivative hpolE,
    HarmonicMaps.ae_tendsto_integral_radius_mul_radialCutoff_derivative hpolV] with r hder hE hV
  intro hr
  refine ⟨hder hr, ?_⟩
  let t : HarmonicMaps.PositiveRadius := ⟨r, hr.1⟩
  let δ : ℕ → HarmonicMaps.PositiveRadius := fun k => ⟨1 / ((k : ℝ) + 1), by positivity⟩
  let η (k : ℕ) := HarmonicMaps.radialCutoffProfile t (δ k)
  have hδ : Tendsto (fun k => (δ k).val) atTop (𝓝 (0 : ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hδright : Tendsto (fun k => (δ k).val) atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.2 ⟨hδ, Filter.Eventually.of_forall fun k => (δ k).property⟩
  have hF : Tendsto (fun k => ∫ x in B, η k ‖x - c‖ * f x)
      atTop (𝓝 (∫ x in Metric.ball c r, f x)) :=
    (HarmonicMaps.tendsto_integral_radialCutoff hn t hr.2 hf).comp hδright
  have hlim := hF.add ((hE hr δ hδ).sub (hV hr δ hδ))
  have hsmall : ∀ᶠ k : ℕ in atTop, (δ k).val < R - r :=
    hδ (Iio_mem_nhds (sub_pos.mpr hr.2))
  have hzero : (fun k => (∫ x in B, η k ‖x - c‖ * f x) +
      ((∫ s in Ioo (0 : ℝ) R, s * deriv (η k) s * polarBoundaryIntegral c e s) -
        (∫ s in Ioo (0 : ℝ) R, s * deriv (η k) s * polarBoundaryIntegral c v s))) =ᶠ[atTop]
      (fun _ => (0 : ℝ)) := by
    filter_upwards [hsmall] with k hk
    have hT := integral_radial_stressCutoff_eq_zero a ε hΩ hQ hEuler hball t (δ k)
      (by dsimp only [t]; linarith only [hk])
    let w : ℝ → ℝ := fun s => s * deriv (η k) s
    have hηcont := (HarmonicMaps.radialCutoffProfile_contDiff t (δ k)).continuous
    have hw : Continuous w := continuous_id.mul
      ((HarmonicMaps.radialCutoffProfile_contDiff t (δ k)).continuous_deriv (by norm_num))
    change (∫ x in B, η k ‖x - c‖ * f x + w ‖x - c‖ * (e - v) x) = 0 at hT
    rw [integral_add (HarmonicMaps.integrableOn_radial_mul hf hηcont)
      (HarmonicMaps.integrableOn_radial_mul (he.sub hv) hw)] at hT
    simp_rw [Pi.sub_apply, mul_sub] at hT
    rw [integral_sub (HarmonicMaps.integrableOn_radial_mul he hw)
      (HarmonicMaps.integrableOn_radial_mul hv hw),
      HarmonicMaps.integral_radial_mul_eq_polar hn he hw,
      HarmonicMaps.integral_radial_mul_eq_polar hn hv hw] at hT
    exact hT
  have hbalance := tendsto_nhds_unique_of_eventuallyEq hlim tendsto_const_nhds hzero
  change (∫ x in Metric.ball c r, f x) +
    (-r * polarBoundaryIntegral c e r - -r * polarBoundaryIntegral c v r) = 0 at hbalance
  change (∫ x in Metric.ball c r, e x + 2 * p x) + _ = 0 at hbalance
  have hsub : Metric.ball c r ⊆ B := Metric.ball_subset_ball hr.2.le
  rw [integral_add (he.mono_set hsub) ((hp.mono_set hsub).const_mul 2), integral_const_mul]
    at hbalance
  linarith only [hbalance]

/-- The positive-radius derivative of the normalized energy contains both
the radial Dirichlet contribution and the nonnegative bulk term. -/
theorem ae_hasDerivAt_normalized_classicalBallEnergy (a : BulkCoefficients) (ε : ElasticScale)
    {Ω : Set Point} (hΩ : IsOpen Ω) {Q : Point → S0} (hQ : ContDiffOn ℝ ∞ Q Ω)
    (hEuler : ∀ x ∈ Ω, (ε : ℝ) ^ 2 • (laplacian Q x : S0).val = bulkGradient a (Q x))
    {c : Point} {R : ℝ} (hR : 0 < R) (hball : Metric.closedBall c R ⊆ Ω) :
    let D := ClassicalGradient Q
    let F : ℝ → ℝ := fun r => ∫ x in Metric.ball c r, energyDensity a ε (Q x) (D x)
    let P : ℝ → ℝ := fun r => ∫ x in Metric.ball c r, (ε : ℝ)⁻¹ ^ 2 * bulkPotential a (Q x)
    ∀ᵐ r : ℝ, r ∈ Ioo 0 R →
      HasDerivAt (fun t => F t / t)
        ((r * polarBoundaryIntegral c (radialGradientNormSq D c) r + 2 * P r) / r ^ 2) r := by
  filter_upwards [(pohozaev_radius_boundary_identity a ε hΩ hQ hEuler hR hball).2] with r hr
  intro hrR
  obtain ⟨hf, hid⟩ := hr hrR
  have hd := hf.div (hasDerivAt_id r) hrR.1.ne'
  let e (x : Point) := energyDensity a ε (Q x) (ClassicalGradient Q x)
  let F (t : ℝ) := ∫ x in Metric.ball c t, e x
  change HasDerivAt (fun t : ℝ => F t / t)
    ((polarBoundaryIntegral c e r * r - F r * 1) / r ^ 2) r at hd
  rw [mul_one, mul_comm (polarBoundaryIntegral c e r) r, hid] at hd
  exact hd

/-- Chapter 2 monotonicity for the actual sextic energy, including any
positive outer radius whose closed ball is contained in the solution domain. -/
theorem normalized_classicalBallEnergy_monotoneOn (a : BulkCoefficients) (ε : ElasticScale)
    {Ω : Set Point} (hΩ : IsOpen Ω) {Q : Point → S0} (hQ : ContDiffOn ℝ ∞ Q Ω)
    (hEuler : ∀ x ∈ Ω, (ε : ℝ) ^ 2 • (laplacian Q x : S0).val = bulkGradient a (Q x))
    {c : Point} {R : ℝ} (hR : 0 < R) (hball : Metric.closedBall c R ⊆ Ω) :
    MonotoneOn (fun r => (energy a ε (Metric.ball c r) Q (ClassicalGradient Q)).toReal / r)
      (Ioc 0 R) := by
  let D := ClassicalGradient Q
  let e : Point → ℝ := fun x => energyDensity a ε (Q x) (D x)
  let F : ℝ → ℝ := fun r => ∫ x in Metric.ball c r, e x
  let G : ℝ → ℝ := fun r => F r / r
  have hrepresented (r : ℝ) (hr : r ≤ R) :
      (energy a ε (Metric.ball c r) Q D).toReal = F r := by
    have he := integrableOn_classicalEnergyDensity_ball a ε hΩ hQ
      ((Metric.closedBall_subset_closedBall hr).trans hball)
    have hpos (x : Point) : 0 ≤ e x := by
      unfold e energyDensity
      rw [gradientNormSq_eq_sum_norm_sq]
      exact add_nonneg (mul_nonneg (by norm_num) (Finset.sum_nonneg fun j _ => sq_nonneg _))
        (mul_nonneg (sq_nonneg _) (bulkPotential_nonneg a (Q x)))
    change (∫⁻ x in Metric.ball c r, ENNReal.ofReal (e x)).toReal = F r
    rw [← ofReal_integral_eq_lintegral_ofReal he (Filter.Eventually.of_forall hpos),
      ENNReal.toReal_ofReal (integral_nonneg hpos)]
  intro s hs r hr hsr
  rcases hsr.eq_or_lt with rfl | hlt
  · exact le_rfl
  change (energy a ε (Metric.ball c s) Q D).toReal / s ≤
    (energy a ε (Metric.ball c r) Q D).toReal / r
  rw [hrepresented s hs.2, hrepresented r hr.2]
  change G s ≤ G r
  have hF := (pohozaev_radius_boundary_identity a ε hΩ hQ hEuler hR hball).1
  have hFac : AbsolutelyContinuousOnInterval F s r := hF.mono (by
    rw [uIcc_of_le hlt.le, uIcc_of_le hR.le]
    exact fun t ht => ⟨hs.1.le.trans ht.1, ht.2.trans hr.2⟩)
  have hinv : AbsolutelyContinuousOnInterval (fun t : ℝ => t⁻¹) s r := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    rw [uIcc_of_le hlt.le]
    exact contDiffOn_id.inv fun t ht => (hs.1.trans_le ht.1).ne'
  have hG : AbsolutelyContinuousOnInterval G s r := by
    simpa only [G, div_eq_mul_inv, Pi.mul_def] using hFac.mul hinv
  have hder : 0 ≤ᵐ[volume.restrict (Ioo s r)] deriv G := by
    apply (ae_restrict_iff' measurableSet_Ioo).2
    filter_upwards [ae_hasDerivAt_normalized_classicalBallEnergy a ε hΩ hQ hEuler hR hball] with t ht
    intro hst
    have ht0 := hs.1.trans hst.1
    have hd := ht ⟨ht0, hst.2.trans_le hr.2⟩
    change 0 ≤ deriv G t
    rw [show deriv G t = _ from hd.deriv]
    apply div_nonneg _ (sq_nonneg t)
    refine add_nonneg (mul_nonneg ht0.le ?_) (mul_nonneg (by norm_num) ?_)
    · exact mul_nonneg (sq_nonneg t) (integral_nonneg fun _ => sq_nonneg _)
    · exact integral_nonneg fun x => mul_nonneg (sq_nonneg _) (bulkPotential_nonneg a (Q x))
  apply sub_nonneg.mp
  rw [← hG.integral_deriv_eq_sub, intervalIntegral.integral_of_le hlt.le,
    ← restrict_Ioo_eq_restrict_Ioc]
  exact integral_nonneg_of_ae hder

end Thesis

end
