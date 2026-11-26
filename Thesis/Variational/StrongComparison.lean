module

public import Thesis.Upstream.Rellich
import Thesis.Foundation.BulkGeometry
import Thesis.Foundation.VacuumTarget
import StratificationTheory.Compactness.CompactBallCover
import StratificationTheory.Compactness.WeakL2Localization
import StratificationTheory.Compactness.WeakEnergyLowerSemicontinuity
import StratificationTheory.Compactness.GradientStrongConvergence
import StratificationTheory.Compactness.RadialTraceDilation
import StratificationTheory.Compactness.SubsequenceConvergence
import StratificationTheory.Foundation.PolarGoodRadius
import StratificationTheory.Foundation.PolarSliceConvergence
import StratificationTheory.Frozen.AmbientRadialTraceWellDefined
import StratificationTheory.Foundation.RadialPiecewiseSobolevData
import StratificationTheory.Interpolation.RadialThreePieceGluing
import StratificationTheory.Interpolation.CompetitorExtension
import HarmonicMaps.Analysis.AffineBallSobolev
import HarmonicMaps.Analysis.AffineEnergyScaling

/-! Weak energy lower bounds and strong convergence for the penalized energy. -/

public section

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators Matrix.Norms.Frobenius

namespace Thesis

local instance strongComparisonS0ContinuousENorm : ContinuousENorm S0 :=
  @SeminormedAddGroup.toContinuousENorm S0 inferInstance

/-- Weak L² convergence of the displayed tensors, expressed against all L² tests. -/
@[expose] def WeakL2FrobeniusConvergence (U : Set Point) (u : ℕ → Point → S0) (v : Point → S0) : Prop :=
  ∀ w : Lp S0 2 (volume.restrict U),
    Tendsto (fun k => ∫ x in U, frobeniusS0 (u k x) (w x))
      atTop (𝓝 (∫ x in U, frobeniusS0 (v x) (w x)))

theorem weakL2FrobeniusConvergence_iff_upstream (U : Set Point)
    (u : ℕ → Point → S0) (v : Point → S0) :
    WeakL2FrobeniusConvergence U u v ↔
      ∀ w : Lp (HarmonicMaps.Ambient 5) 2 (volume.restrict U),
        Tendsto (fun k => ∫ x in U, inner ℝ (frobeniusCoordinateEquiv (u k x)) (w x))
          atTop (𝓝 (∫ x in U, inner ℝ (frobeniusCoordinateEquiv (v x)) (w x))) := by
  constructor
  · intro h w
    let g (x : Point) := frobeniusCoordinateEquiv.symm (w x)
    have hg : MemLp g 2 (volume.restrict U) :=
      (frobeniusCoordinateEquiv_memLp_iff (volume.restrict U) 2 g).mp
        ((Lp.memLp w).ae_eq (Eventually.of_forall fun x =>
          (frobeniusCoordinateEquiv.apply_symm_apply (w x)).symm))
    let z := hg.toLp g
    have hpair (f : Point → S0) :
        (∫ x in U, frobeniusS0 (f x) (z x)) =
          ∫ x in U, inner ℝ (frobeniusCoordinateEquiv (f x)) (w x) := by
      apply integral_congr_ae
      filter_upwards [hg.coeFn_toLp] with x hx
      change z x = frobeniusCoordinateEquiv.symm (w x) at hx
      rw [hx, ← frobeniusCoordinateEquiv_inner, LinearIsometryEquiv.apply_symm_apply]
    rw [← hpair v]
    exact (h z).congr (fun k => hpair (u k))
  · intro h w
    have hF : MemLp (frobeniusField w) 2 (volume.restrict U) :=
      (frobeniusCoordinateEquiv_memLp_iff (volume.restrict U) 2 w).mpr (Lp.memLp w)
    let z := hF.toLp (frobeniusField w)
    have hpair (f : Point → S0) :
        (∫ x in U, inner ℝ (frobeniusCoordinateEquiv (f x)) (z x)) =
          ∫ x in U, frobeniusS0 (f x) (w x) := by
      apply integral_congr_ae
      filter_upwards [hF.coeFn_toLp] with x hx
      change z x = frobeniusCoordinateEquiv (w x) at hx
      rw [hx, frobeniusCoordinateEquiv_inner]
    rw [← hpair v]
    exact (h z).congr (fun k => hpair (u k))

theorem WeakL2FrobeniusConvergence.mono {U V : Set Point} {u : ℕ → Point → S0}
    {v : Point → S0} (h : WeakL2FrobeniusConvergence U u v)
    (hV : MeasurableSet V) (hVU : V ⊆ U) :
    WeakL2FrobeniusConvergence V u v :=
  (weakL2FrobeniusConvergence_iff_upstream V u v).mpr
    (StratificationTheory.Compactness.weak_L2_integral_convergence_mono hV hVU
      ((weakL2FrobeniusConvergence_iff_upstream U u v).mp h))

private theorem memLp_frobeniusGradient_columns {U : Set Point} {D : Point → Gradient}
    (hD : ∀ j, MemLp (fun x => D x j) 2 (volume.restrict U)) :
    ∀ j, MemLp (fun x => frobeniusGradient D x j) 2 (volume.restrict U) :=
  fun j => (frobeniusCoordinateEquiv_memLp_iff (volume.restrict U) 2 (fun x => D x j)).mpr (hD j)

private theorem dirichletEnergy_ne_top_of_columns {U : Set Point} {D : Point → Gradient}
    (hD : ∀ j, MemLp (fun x => D x j) 2 (volume.restrict U)) :
    dirichletEnergy U D ≠ ⊤ := by
  rw [dirichletEnergy_eq_half_upstream]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (HarmonicMaps.dirichletEnergy_ne_top_of_integrable
      (HarmonicMaps.integrable_hsNormSq_of_memLp_columns (memLp_frobeniusGradient_columns hD)))

/-- The half-normalized tensor Dirichlet energy is weakly lower semicontinuous. -/
theorem dirichletEnergy_le_liminf_of_weak_frobenius {U : Set Point}
    {D : ℕ → Point → Gradient} {G : Point → Gradient}
    (hD : ∀ k j, MemLp (fun x => D k x j) 2 (volume.restrict U))
    (hG : ∀ j, MemLp (fun x => G x j) 2 (volume.restrict U))
    (hWeak : ∀ j : Fin 3, WeakL2FrobeniusConvergence U (fun k x => D k x j) (fun x => G x j)) :
    dirichletEnergy U G ≤ atTop.liminf (fun k => dirichletEnergy U (D k)) := by
  have h := StratificationTheory.Compactness.dirichletEnergy_le_liminf_of_weak_columns
    (fun k => memLp_frobeniusGradient_columns (hD k)) (memLp_frobeniusGradient_columns hG)
    (fun j => (weakL2FrobeniusConvergence_iff_upstream U _ _).mp (hWeak j))
  simp_rw [dirichletEnergy_eq_half_upstream, ENNReal.liminf_const_mul_of_ne_top ENNReal.ofReal_ne_top]
  exact mul_le_mul_right h _

/-- A weakly convergent sequence satisfies the same lower bound on every
measurable subregion, using its original gradients. -/
theorem dirichletEnergy_le_liminf_of_weak_frobenius_on_subset {U V : Set Point}
    {D : ℕ → Point → Gradient} {G : Point → Gradient}
    (hV : MeasurableSet V) (hVU : V ⊆ U)
    (hD : ∀ k j, MemLp (fun x => D k x j) 2 (volume.restrict U))
    (hG : ∀ j, MemLp (fun x => G x j) 2 (volume.restrict U))
    (hWeak : ∀ j : Fin 3, WeakL2FrobeniusConvergence U (fun k x => D k x j) (fun x => G x j)) :
    dirichletEnergy V G ≤ atTop.liminf (fun k => dirichletEnergy V (D k)) :=
  dirichletEnergy_le_liminf_of_weak_frobenius
    (fun k j => (hD k j).mono_measure (Measure.restrict_mono_set volume hVU))
    (fun j => (hG j).mono_measure (Measure.restrict_mono_set volume hVU))
    (fun j => (hWeak j).mono hV hVU)

private theorem tendsto_ennreal_sq_zero {s : ℕ → ℝ≥0∞} (h : Tendsto s atTop (𝓝 0)) :
    Tendsto (fun k => s k ^ 2) atTop (𝓝 0) := by
  have h' : Tendsto (fun k => s k ^ (2 : ℝ)) atTop (𝓝 ((0 : ℝ≥0∞) ^ (2 : ℝ))) :=
    (ENNReal.continuous_rpow_const.tendsto 0).comp h
  simpa only [ENNReal.rpow_two, zero_pow (by decide : (2 : ℕ) ≠ 0)] using h'

/-- Strong map L² convergence, weak gradient convergence and convergence
of the original Dirichlet energies imply strong H¹ convergence. -/
theorem strongH1_of_dirichletEnergy_tendsto {U : Set Point}
    {u : ℕ → Point → S0} {D : ℕ → Point → Gradient} {v : Point → S0} {G : Point → Gradient}
    (hu : ∀ k, MemH1 U (u k) (D k)) (hv : MemH1 U v G)
    (hMap : Tendsto (fun k => eLpNorm (u k - v) 2 (volume.restrict U)) atTop (𝓝 0))
    (hWeak : ∀ j : Fin 3, WeakL2FrobeniusConvergence U (fun k x => D k x j) (fun x => G x j))
    (hEnergy : Tendsto (fun k => dirichletEnergy U (D k)) atTop (𝓝 (dirichletEnergy U G))) :
    StrongH1 U u D v G := by
  have hFactor (A : Point → Gradient) : 2 * (dirichletEnergy U A).toReal =
      (HarmonicMaps.dirichletEnergy (frobeniusGradient A) U).toReal := by
    rw [dirichletEnergy_eq_half_upstream, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num)]
    ring
  have hEnergyNative : Tendsto (fun k =>
      (HarmonicMaps.dirichletEnergy (frobeniusGradient (D k)) U).toReal)
      atTop (𝓝 (HarmonicMaps.dirichletEnergy (frobeniusGradient G) U).toReal) := by
    have h := ((ENNReal.tendsto_toReal (dirichletEnergy_ne_top_of_columns hv.2.1)).comp hEnergy)
    simpa only [Function.comp_def, hFactor] using h.const_mul (2 : ℝ)
  have hD (k : ℕ) := memLp_frobeniusGradient_columns (hu k).2.1
  have hG := memLp_frobeniusGradient_columns hv.2.1
  have hCols := StratificationTheory.Compactness.gradient_columns_strong_of_weak_and_energy
    hD hG (fun j => (weakL2FrobeniusConvergence_iff_upstream U _ _).mp (hWeak j)) hEnergyNative
  have hF (k : ℕ) : MemLp (frobeniusField (u k)) 2 (volume.restrict U) :=
    (frobeniusCoordinateEquiv_memLp_iff _ _ _).mpr (hu k).1
  have hV : MemLp (frobeniusField v) 2 (volume.restrict U) :=
    (frobeniusCoordinateEquiv_memLp_iff _ _ _).mpr hv.1
  have hEq (k : ℕ) := h1Deviation_eq_sq_eLpNorm U (u k) v (D k) G
    (hV.aestronglyMeasurable.sub (hF k).aestronglyMeasurable)
    (fun j => (hG j).aestronglyMeasurable.sub (hD k j).aestronglyMeasurable)
  have hNormMap (k : ℕ) :
      eLpNorm (frobeniusField v - frobeniusField (u k)) 2 (volume.restrict U) =
        eLpNorm (u k - v) 2 (volume.restrict U) := by
    apply eLpNorm_congr_norm_ae
    exact Eventually.of_forall fun x => by
      change ‖frobeniusCoordinateEquiv (v x) - frobeniusCoordinateEquiv (u k x)‖ =
        ‖u k x - v x‖
      rw [← map_sub, LinearIsometryEquiv.norm_map, norm_sub_rev]
  have hNormCol (k : ℕ) (j : Fin 3) :
      eLpNorm (fun x => frobeniusGradient G x j - frobeniusGradient (D k) x j)
          2 (volume.restrict U) =
        eLpNorm (fun x => frobeniusGradient (D k) x j - frobeniusGradient G x j)
          2 (volume.restrict U) :=
    eLpNorm_congr_norm_ae (Eventually.of_forall fun _ => norm_sub_rev _ _)
  have hSum := tendsto_finsetSum (s := Finset.univ) fun (j : Fin 3) _ =>
    tendsto_ennreal_sq_zero (hCols j)
  refine ⟨hu, hv, ?_⟩
  simpa only [hEq, hNormMap, hNormCol, Finset.sum_const_zero, zero_add] using
    (tendsto_ennreal_sq_zero hMap).add hSum

private theorem continuous_bulkPotential_ambient (a : BulkCoefficients) : Continuous (bulkPotential a) := by
  let trace : Tensor →L[ℝ] ℝ := (Matrix.traceLinearMap (Fin 3) ℝ ℝ).toContinuousLinearMap
  change Continuous (fun A : S0 =>
    let t := trace ((symmetricTraceless.subtypeL A) ^ 2)
    let s := trace ((symmetricTraceless.subtypeL A) ^ 3)
    let t₀ := preferredTraceSq a
    a.a2 / 2 * t₀ - a.a4 / 4 * t₀ ^ 2 - a.a6 / 6 * t₀ ^ 3
      - a.a2 / 2 * t + a.a4 / 4 * t ^ 2 + a.a6 / 6 * t ^ 3 + a.a6' / 6 * s ^ 2)
  fun_prop

/-- The total energy separates exactly into the half-normalized Dirichlet
energy and the actual L¹ norm of the nonnegative scaled bulk potential. -/
theorem energy_eq_dirichlet_add_scaledPotential (a : BulkCoefficients) (ε : ElasticScale)
    {U : Set Point} (u : Point → S0) {D : Point → Gradient}
    (hD : ∀ j, MemLp (fun x => D x j) 2 (volume.restrict U)) :
    energy a ε U u D = dirichletEnergy U D +
      eLpNorm (fun x => (ε : ℝ)⁻¹ ^ 2 * bulkPotential a (u x)) 1 (volume.restrict U) := by
  have hGrad (x : Point) : 0 ≤ gradientNormSq (D x) := by
    rw [gradientNormSq_eq_sum_norm_sq]
    exact Finset.sum_nonneg fun j _ => sq_nonneg ‖D x j‖
  have hMeas : AEMeasurable (fun x => ENNReal.ofReal ((1 / 2 : ℝ) * gradientNormSq (D x)))
      (volume.restrict U) := by
    apply AEMeasurable.ennreal_ofReal
    simp only [gradientNormSq_eq_sum_norm_sq]
    apply aemeasurable_const.mul
    exact Finset.aemeasurable_fun_sum Finset.univ fun (j : Fin 3) _ =>
      (hD j).aestronglyMeasurable.norm.aemeasurable.pow_const (2 : ℕ)
  have hBulk (x : Point) : 0 ≤ (ε : ℝ)⁻¹ ^ 2 * bulkPotential a (u x) :=
    mul_nonneg (sq_nonneg _) (bulkPotential_nonneg a (u x))
  simp only [energy, energyDensity, dirichletEnergy, eLpNorm_one_eq_lintegral_enorm]
  simp_rw [ENNReal.ofReal_add (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) (hGrad _)) (hBulk _),
    lintegral_add_left' hMeas]
  congr 1
  exact lintegral_congr fun x => by rw [← ofReal_norm, Real.norm_of_nonneg (hBulk x)]

private theorem memLp_scaledPotential_of_energy_ne_top (a : BulkCoefficients) (ε : ElasticScale)
    {U : Set Point} {u : Point → S0} {D : Point → Gradient} (hu : MemH1 U u D)
    (hE : energy a ε U u D ≠ ⊤) :
    MemLp (fun x => (ε : ℝ)⁻¹ ^ 2 * bulkPotential a (u x)) 1 (volume.restrict U) := by
  refine ⟨((continuous_bulkPotential_ambient a).comp_aestronglyMeasurable hu.1.1).const_mul _, ?_⟩
  rw [energy_eq_dirichlet_add_scaledPotential a ε u hu.2.1] at hE
  exact (le_add_left le_rfl).trans_lt (lt_top_iff_ne_top.mpr hE)

/-- The limsup comparison with the limit's Dirichlet energy forces both
strong H¹ convergence and vanishing scaled bulk energy. -/
theorem strongH1_and_scaledPotential_of_limsup_energy_le_dirichlet
    (a : BulkCoefficients) (ε : ℕ → ElasticScale) {U : Set Point}
    {u : ℕ → Point → S0} {D : ℕ → Point → Gradient} {v : Point → S0} {G : Point → Gradient}
    (hu : ∀ k, MemH1 U (u k) (D k)) (hv : MemH1 U v G)
    (hMap : Tendsto (fun k => eLpNorm (u k - v) 2 (volume.restrict U)) atTop (𝓝 0))
    (hWeak : ∀ j : Fin 3, WeakL2FrobeniusConvergence U (fun k x => D k x j) (fun x => G x j))
    (hFinite : ∀ k, energy a (ε k) U (u k) (D k) ≠ ⊤)
    (hUpper : atTop.limsup (fun k => energy a (ε k) U (u k) (D k)) ≤ dirichletEnergy U G) :
    StrongH1 U u D v G ∧
      (∀ k, MemLp (fun x => (ε k : ℝ)⁻¹ ^ 2 * bulkPotential a (u k x))
        1 (volume.restrict U)) ∧
      Tendsto (fun k => eLpNorm (fun x => (ε k : ℝ)⁻¹ ^ 2 * bulkPotential a (u k x))
        1 (volume.restrict U)) atTop (𝓝 0) ∧
      Tendsto (fun k => energy a (ε k) U (u k) (D k)) atTop (𝓝 (dirichletEnergy U G)) := by
  let A (k : ℕ) := dirichletEnergy U (D k)
  let B (k : ℕ) := eLpNorm (fun x => (ε k : ℝ)⁻¹ ^ 2 * bulkPotential a (u k x))
    1 (volume.restrict U)
  let E (k : ℕ) := energy a (ε k) U (u k) (D k)
  have hSplit (k : ℕ) : E k = A k + B k :=
    energy_eq_dirichlet_add_scaledPotential a (ε k) (u k) (hu k).2.1
  have hLE (k : ℕ) : A k ≤ E k := by rw [hSplit]; exact le_add_right le_rfl
  have hLower : dirichletEnergy U G ≤ atTop.liminf A :=
    dirichletEnergy_le_liminf_of_weak_frobenius (fun k => (hu k).2.1) hv.2.1 hWeak
  have hLimA : Tendsto A atTop (𝓝 (dirichletEnergy U G)) :=
    tendsto_of_le_liminf_of_limsup_le hLower ((limsup_le_limsup (Eventually.of_forall hLE)).trans hUpper)
  have hLimE : Tendsto E atTop (𝓝 (dirichletEnergy U G)) :=
    tendsto_of_le_liminf_of_limsup_le
      (hLower.trans (liminf_le_liminf (Eventually.of_forall hLE))) hUpper
  have hSub : Tendsto (fun k => E k - A k) atTop (𝓝 0) := by
    have h := (ENNReal.tendsto_sub (Or.inl (dirichletEnergy_ne_top_of_columns hv.2.1))).comp
      (hLimE.prodMk_nhds hLimA)
    simpa [Function.comp_def] using h
  have hLimB : Tendsto B atTop (𝓝 0) := by
    apply hSub.congr
    intro k
    rw [hSplit, ENNReal.add_sub_cancel_left (dirichletEnergy_ne_top_of_columns (hu k).2.1)]
  exact ⟨strongH1_of_dirichletEnergy_tendsto hu hv hMap hWeak hLimA,
    fun k => memLp_scaledPotential_of_energy_ne_top a (ε k) (hu k) (hFinite k), hLimB, hLimE⟩

/-- The bulk contribution of an a.e. vacuum-valued map vanishes. -/
theorem energy_eq_dirichlet_of_takesVacuumValues (a : BulkCoefficients) (ε : ElasticScale)
    {U : Set Point} {u : Point → S0} (D : Point → Gradient) (hu : TakesVacuumValues a U u) :
    energy a ε U u D = dirichletEnergy U D := by
  apply lintegral_congr_ae
  filter_upwards [hu] with x hx
  simp only [energyDensity, (bulkPotential_eq_zero_iff a (u x)).mpr hx, mul_zero, add_zero]

/-- The open annulus at two radii about the same center. -/
abbrev radialAnnulus (c : Point) (r s : ℝ) : Set Point :=
  {x | r < ‖x - c‖ ∧ ‖x - c‖ < s}

theorem isOpen_radialAnnulus (c : Point) (r s : ℝ) : IsOpen (radialAnnulus c r s) :=
  isOpen_Ioo.preimage (continuous_id.sub continuous_const).norm

/-- Continuous radial traces take values in L² on the unit sphere. -/
abbrev RadialL2Trace (r s : ℝ) :=
  C(Icc r s, Lp (HarmonicMaps.Ambient 5) 2
    (Measure.euclideanHausdorffMeasure 2 : Measure (Metric.sphere (0 : Point) 1)))

/-- The continuous radial trace represents the original map on almost every
interior slice, in isometric Frobenius coordinates. -/
@[expose] def RepresentsRadialL2Trace (c : Point) {r s : ℝ} (u : Point → S0) (H : RadialL2Trace r s) : Prop :=
  let σ : Measure (Metric.sphere (0 : Point) 1) := Measure.euclideanHausdorffMeasure 2
  ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo r s,
    ∃ hslice : MemLp (fun θ : Metric.sphere (0 : Point) 1 => frobeniusField u (c + t • θ.val)) 2 σ,
      H ⟨t, ht.1.le, ht.2.le⟩ =
        hslice.toLp (fun θ : Metric.sphere (0 : Point) 1 => frobeniusField u (c + t • θ.val))

private theorem lintegral_radial_piecewise (c : Point) {r s : ℝ}
    (hr : 0 < r) (hrs : r < s) (f g : Point → ℝ≥0∞) :
    (∫⁻ x in Metric.ball c s, if ‖x - c‖ < r then f x else g x) =
      (∫⁻ x in Metric.ball c r, f x) + ∫⁻ x in radialAnnulus c r s, g x := by
  have hPartition : Metric.ball c s =ᵐ[(volume : Measure Point)]
      (Metric.ball c r ∪ radialAnnulus c r s : Set Point) := by
    filter_upwards [StratificationTheory.ae_norm_sub_ne_radius c hr] with x hx
    apply propext
    simp only [radialAnnulus]
    refine ⟨fun hs => ?_, fun h => h.elim (fun h' => h'.trans hrs) And.right⟩
    rcases lt_or_gt_of_ne hx with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, hs⟩
  have hAnn := (isOpen_radialAnnulus c r s).measurableSet
  have hDisjoint : Disjoint (Metric.ball c r) (radialAnnulus c r s) := by
    refine Set.disjoint_left.mpr fun x hx hy => ?_
    exact (not_lt_of_gt (mem_ball_iff_norm.mp hx)) hy.1
  rw [Measure.restrict_congr_set hPartition, lintegral_union hAnn hDisjoint]
  congr 1
  · apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    exact if_pos (mem_ball_iff_norm.mp hx)
  · apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem hAnn] with x hx
    exact if_neg hx.1.not_gt

private theorem energy_radial_piecewise (a : BulkCoefficients) (ε : ElasticScale)
    (c : Point) {r s : ℝ} (hr : 0 < r) (hrs : r < s)
    (u w : Point → S0) (D G : Point → Gradient) :
    energy a ε (Metric.ball c s) (fun x => if ‖x - c‖ < r then u x else w x)
      (fun x j => if ‖x - c‖ < r then D x j else G x j) =
      energy a ε (Metric.ball c r) u D + energy a ε (radialAnnulus c r s) w G := by
  have hsplit (x : Point) :
      energyDensity a ε (if ‖x - c‖ < r then u x else w x)
        (fun j => if ‖x - c‖ < r then D x j else G x j) =
      if ‖x - c‖ < r then energyDensity a ε (u x) (D x) else energyDensity a ε (w x) (G x) := by
    split_ifs <;> rfl
  unfold energy
  simp_rw [hsplit, apply_ite ENNReal.ofReal]
  exact lintegral_radial_piecewise c hr hrs _ _

/-- Matching radial traces glue an inner vacuum map, a penalized annular
connector and the original exterior. Local minimality then compares the
original energy with the sum of the inner and annular energies. -/
theorem energy_le_dirichlet_add_annulus_of_matching_radial_traces
    (a : BulkCoefficients) (ε : ElasticScale) {Ω : Set Point}
    (c : Point) {r s R : ℝ} (hr : 0 < r) (hrs : r < s) (hsR : s < R)
    (hR : Metric.closedBall c R ⊆ Ω)
    (u v w : Point → S0) (D G J : Point → Gradient)
    (hMin : IsLocalEnergyMinimizer a ε Ω u D)
    (hE : energy a ε (Metric.ball c R) u D ≠ ⊤)
    (hv : MemH1 (Metric.ball c r) v G) (hvN : TakesVacuumValues a (Metric.ball c r) v)
    (hw : MemH1 (radialAnnulus c r s) w J)
    (H : RadialL2Trace (r / 2) r) (K : RadialL2Trace r s)
    (L : RadialL2Trace s ((s + R) / 2))
    (hH : RepresentsRadialL2Trace c v H) (hK : RepresentsRadialL2Trace c w K)
    (hL : RepresentsRadialL2Trace c u L)
    (hMatchInner : H ⟨r, by linarith only [hr], le_rfl⟩ = K ⟨r, le_rfl, hrs.le⟩)
    (hMatchOuter : K ⟨s, hrs.le, le_rfl⟩ = L ⟨s, le_rfl, by linarith only [hsR]⟩) :
    energy a ε (Metric.ball c s) u D ≤
      dirichletEnergy (Metric.ball c r) G + energy a ε (radialAnnulus c r s) w J := by
  let BR := HarmonicMaps.ballDomain c R
  let Br := HarmonicMaps.ballDomain c r
  let A : HarmonicMaps.OpenDomain 3 := ⟨radialAnnulus c r s, isOpen_radialAnnulus c r s⟩
  have hRpos : 0 < R := hr.trans (hrs.trans hsR)
  have hu : MemH1 BR.val u D := by
    apply hMin.1 _ Metric.isOpen_ball
    unfold CompactlyContained
    rw [closure_ball c hRpos.ne']
    exact ⟨isCompact_closedBall c R, hR⟩
  have hu' := (memH1_iff_memW12 BR u D).1 hu
  have hv' := (memH1_iff_memW12 Br v G).1 hv
  have hw' := (memH1_iff_memW12 A w J).1 hw
  let f₁ (x : Point) := if ‖x - c‖ < r then v x else w x
  let F₁ (x : Point) (j : Fin 3) := if ‖x - c‖ < r then G x j else J x j
  let f (x : Point) := if ‖x - c‖ < s then f₁ x else u x
  let F (x : Point) (j : Fin 3) := if ‖x - c‖ < s then F₁ x j else D x j
  have hfMap : frobeniusField f = fun x =>
      if ‖x - c‖ < s then
        (if ‖x - c‖ < r then frobeniusField v x else frobeniusField w x)
      else frobeniusField u x := by
    funext x
    simp only [frobeniusField, f, f₁]
    split_ifs <;> rfl
  have hfGrad : frobeniusGradient F = fun x j =>
      if ‖x - c‖ < s then
        (if ‖x - c‖ < r then frobeniusGradient G x j else frobeniusGradient J x j)
      else frobeniusGradient D x j := by
    funext x j
    simp only [frobeniusGradient, F, F₁]
    split_ifs <;> rfl
  obtain ⟨hfRaw, _, hfTrace⟩ := StratificationTheory.memW12_radial_three_piece_gluing
    (by decide : 2 ≤ 3) c hr hrs hsR (frobeniusField v) (frobeniusField w) (frobeniusField u)
    (frobeniusGradient G) (frobeniusGradient J) (frobeniusGradient D) hv' hw' hu'
    H K L hH hK hL hMatchInner hMatchOuter
  have hf := (memH1_iff_memW12 BR f F).2 (by simpa only [hfMap, hfGrad] using hfRaw)
  have hTrace := (sameTrace_iff_hasZeroBoundaryDifference BR f u F D).2
    (by simpa only [hfMap, hfGrad] using hfTrace)
  have hComparison := hMin.2 c R hRpos hR f F hf hTrace
  have hOuterSub : radialAnnulus c s R ⊆ Metric.ball c R := fun _ hx =>
    mem_ball_iff_norm.mpr hx.2
  have hOuterFinite : energy a ε (radialAnnulus c s R) u D ≠ ⊤ :=
    ne_top_of_le_ne_top hE (lintegral_mono_set hOuterSub)
  have hOrigSplit :
      energy a ε (Metric.ball c R) u D =
        energy a ε (Metric.ball c s) u D + energy a ε (radialAnnulus c s R) u D := by
    simpa only [ite_self] using energy_radial_piecewise a ε c (hr.trans hrs) hsR u u D D
  have hNewSplit : energy a ε (Metric.ball c R) f F =
      (dirichletEnergy (Metric.ball c r) G + energy a ε (radialAnnulus c r s) w J) +
        energy a ε (radialAnnulus c s R) u D := by
    change energy a ε (Metric.ball c R)
      (fun x => if ‖x - c‖ < s then f₁ x else u x)
      (fun x j => if ‖x - c‖ < s then F₁ x j else D x j) = _
    rw [energy_radial_piecewise a ε c (hr.trans hrs) hsR]
    change energy a ε (Metric.ball c s)
      (fun x => if ‖x - c‖ < r then v x else w x)
      (fun x j => if ‖x - c‖ < r then G x j else J x j) + _ = _
    rw [energy_radial_piecewise a ε c hr hrs, energy_eq_dirichlet_of_takesVacuumValues a ε G hvN]
  rw [hOrigSplit, hNewSplit] at hComparison
  exact (ENNReal.add_le_add_iff_right hOuterFinite).mp hComparison

/-- Compressing the vacuum comparison from radius `s` to radius `r`
preserves its trace on the corresponding sphere and multiplies its
three-dimensional Dirichlet energy by `r / s`. -/
theorem energy_le_scaledDirichlet_add_annulus_of_matching_radial_traces
    (a : BulkCoefficients) (ε : ElasticScale) {Ω : Set Point}
    (c : Point) {r s R : ℝ} (hr : 0 < r) (hrs : r < s) (hsR : s < R)
    (hR : Metric.closedBall c R ⊆ Ω)
    (u v w : Point → S0) (D G J : Point → Gradient)
    (hMin : IsLocalEnergyMinimizer a ε Ω u D)
    (hE : energy a ε (Metric.ball c R) u D ≠ ⊤)
    (hv : MemH1 (Metric.ball c s) v G) (hvN : TakesVacuumValues a (Metric.ball c s) v)
    (hw : MemH1 (radialAnnulus c r s) w J)
    (H : RadialL2Trace (s / 2) s) (K : RadialL2Trace r s)
    (L : RadialL2Trace s ((s + R) / 2))
    (hH : RepresentsRadialL2Trace c v H) (hK : RepresentsRadialL2Trace c w K)
    (hL : RepresentsRadialL2Trace c u L)
    (hMatchInner : H ⟨s, by linarith only [hr, hrs], le_rfl⟩ = K ⟨r, le_rfl, hrs.le⟩)
    (hMatchOuter : K ⟨s, hrs.le, le_rfl⟩ = L ⟨s, le_rfl, by linarith only [hsR]⟩) :
    energy a ε (Metric.ball c s) u D ≤
      ENNReal.ofReal (r / s) * dirichletEnergy (Metric.ball c s) G +
        energy a ε (radialAnnulus c r s) w J := by
  let τ : ℝ := s / r
  have hs : 0 < s := hr.trans hrs
  have hτ : 0 < τ := div_pos hs hr
  have hScale : τ * r = s := div_mul_cancel₀ s hr.ne'
  have hRadius : s / τ = r := (div_eq_iff hτ.ne').2 (by rw [mul_comm, hScale])
  let v₀ (x : Point) := v (c + τ • (x - c))
  let G₀ (x : Point) (j : Fin 3) := τ • G (c + τ • (x - c)) j
  let Br := HarmonicMaps.ballDomain c r
  let Bs := HarmonicMaps.ballDomain c s
  have hg : frobeniusGradient G₀ =
      fun x j => τ • frobeniusGradient G (c + τ • (x - c)) j := by
    funext x j
    change frobeniusCoordinateEquiv (τ • G (c + τ • (x - c)) j) =
      τ • frobeniusCoordinateEquiv (G (c + τ • (x - c)) j)
    exact map_smul frobeniusCoordinateEquiv _ _
  have hvNative := (memH1_iff_memW12 Bs v G).mp hv
  have hv₀ : MemH1 (Metric.ball c r) v₀ G₀ := by
    apply (memH1_iff_memW12 Br _ _).mpr
    rw [hg]
    have hPullback := hvNative.affineBall_pullback c hτ
    rwa [hRadius] at hPullback
  have hv₀N : TakesVacuumValues a (Metric.ball c r) v₀ := by
    change ∀ᵐ x ∂volume.restrict (Metric.ball c r), v (c + τ • (x - c)) ∈ vacuum a
    simpa only [hRadius] using HarmonicMaps.ae_affineBall c c hτ s hvN
  let σ : Measure (Metric.sphere (0 : Point) 1) := Measure.euclideanHausdorffMeasure 2
  obtain ⟨H₀, hH₀, hEndpoint⟩ :=
    StratificationTheory.Compactness.exists_dilated_inner_radial_trace σ (frobeniusField v) c
      hs hτ hr hScale le_rfl le_rfl H hH
  have hE₀ : dirichletEnergy (Metric.ball c r) G₀ =
      ENNReal.ofReal (r / s) * dirichletEnergy (Metric.ball c s) G := by
    have hPower : τ ^ (2 - (3 : ℤ)) = r / s := by
      norm_num [τ, zpow_neg, inv_div]
    have hNative := HarmonicMaps.dirichletEnergy_affineBall c c hτ s (frobeniusGradient G)
    change HarmonicMaps.dirichletEnergy (fun x j => τ • frobeniusGradient G (c + τ • (x - c)) j)
      (Metric.ball c (s / τ)) = ENNReal.ofReal (τ ^ (2 - (3 : ℤ))) *
        HarmonicMaps.dirichletEnergy (frobeniusGradient G) (Metric.ball c s) at hNative
    rw [hRadius, hPower] at hNative
    rw [dirichletEnergy_eq_half_upstream, dirichletEnergy_eq_half_upstream, hg, hNative]
    ac_rfl
  have hComparison := energy_le_dirichlet_add_annulus_of_matching_radial_traces a ε c hr hrs hsR hR
    u v₀ w D G₀ J hMin hE hv₀ hv₀N hw H₀ K L hH₀ hK hL
    (hEndpoint.trans hMatchInner) hMatchOuter
  rwa [hE₀] at hComparison

/-- Angular integration with the three-dimensional polar Jacobian. -/
@[expose] noncomputable def polarIntegralDensity (c : Point) (f : Point → ℝ) (ρ : ℝ) : ℝ :=
  ρ ^ 2 * ∫ θ : Metric.sphere (0 : Point) 1, f (c + ρ • θ.val)
    ∂(volume : Measure Point).toSphere

/-- On a positive interval of radii, Fatou's lemma selects one common
radius with bounded polar energy along a strict subsequence. The selected
radius retains every given almost-everywhere property and integrability of
all original slices. -/
theorem exists_good_radius_subsequence_of_bounded_polar_energy
    (c : Point) {r R M : ℝ} (hr : 0 < r) (hrR : r < R) (hM : 0 < M)
    (f : ℕ → Point → ℝ)
    (hf : ∀ k, IntegrableOn (f k) (Metric.ball c R))
    (hNonneg : ∀ k x, 0 ≤ f k x)
    (hEnergy : ∀ k, (∫ x in Metric.ball c R, f k x) ≤ M)
    (P : ℝ → Prop) (hP : ∀ᵐ ρ ∂volume.restrict (Ioo r R), P ρ) :
    ∃ ρ ∈ Ioo r R, P ρ ∧
      (∀ k, Integrable (fun θ : Metric.sphere (0 : Point) 1 => f k (c + ρ • θ.val))
        (volume : Measure Point).toSphere) ∧
      ∃ κ : ℕ → ℕ, StrictMono κ ∧ ∀ k,
        polarIntegralDensity c (f (κ k)) ρ ≤ 4 * M / (R - r) := by
  let μ : Measure ℝ := volume.restrict (Ioo r R)
  let F (k : ℕ) := polarIntegralDensity c (f k)
  let A (k : ℕ) (ρ : ℝ) := ENNReal.ofReal (F k ρ)
  let A₀ (ρ : ℝ) := atTop.liminf (fun k => A k ρ)
  let C : ℝ := 2 * M / (R - r)
  have hWidth : 0 < R - r := sub_pos.mpr hrR
  have hC : 0 < C := by dsimp only [C]; positivity
  have hSubset : Ioo r R ⊆ Ioo (0 : ℝ) R := fun _ h => ⟨hr.trans h.1, h.2⟩
  have hI (k : ℕ) : Integrable (F k) μ :=
    (StratificationTheory.integrable_polar_density_ball (n := 3) (hf k)).mono_set hSubset
  have hF₀ (k : ℕ) : 0 ≤ᵐ[μ] F k :=
    Eventually.of_forall fun ρ =>
      mul_nonneg (sq_nonneg ρ) (integral_nonneg fun θ => hNonneg k (c + ρ • θ.val))
  have hMass : μ univ = ENNReal.ofReal (R - r) := by
    change volume.restrict (Ioo r R) univ = _
    rw [Measure.restrict_apply_univ, Real.volume_Ioo]
  have hInt (k : ℕ) : (∫⁻ ρ, A k ρ ∂μ) ≤ ENNReal.ofReal M := by
    change (∫⁻ ρ, ENNReal.ofReal (F k ρ) ∂μ) ≤ _
    rw [← ofReal_integral_eq_lintegral_ofReal (hI k) (hF₀ k)]
    apply ENNReal.ofReal_le_ofReal
    have hPolar : (∫ ρ, F k ρ ∂μ) = ∫ x in Metric.ball c R \ Metric.ball c r, f k x := by
      rw [HarmonicMaps.integral_annulus_eq_polar (n := 3) (by decide) hr hrR.le
        ((hf k).mono_set sdiff_subset), intervalIntegral.integral_of_le hrR.le,
        integral_Ioc_eq_integral_Ioo]
      rfl
    rw [hPolar]
    exact (setIntegral_mono_set (hf k) (Eventually.of_forall (hNonneg k))
      (Eventually.of_forall sdiff_subset)).trans (hEnergy k)
  have hFatou : ∫⁻ ρ, A₀ ρ ∂μ ≤ ENNReal.ofReal M :=
    (lintegral_liminf_le' (fun k => (hI k).aemeasurable.ennreal_ofReal)).trans
      ((liminf_le_liminf (Eventually.of_forall hInt)).trans_eq (liminf_const _))
  have hSlice : ∀ᵐ ρ ∂μ, ∀ k,
      Integrable (fun θ : Metric.sphere (0 : Point) 1 => f k (c + ρ • θ.val))
        (volume : Measure Point).toSphere := by
    apply ae_all_iff.mpr
    intro k
    exact ae_restrict_of_ae_restrict_of_subset hSubset
      (StratificationTheory.ae_integrable_polar_slice_ball (n := 3) (hf k))
  have hGood : ∃ ρ ∈ Ioo r R, P ρ ∧
      (∀ k, Integrable (fun θ : Metric.sphere (0 : Point) 1 => f k (c + ρ • θ.val))
        (volume : Measure Point).toSphere) ∧ A₀ ρ ≤ ENNReal.ofReal C := by
    by_contra h
    have hLower : ∀ᵐ ρ ∂μ, ENNReal.ofReal C ≤ A₀ ρ := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo, hP, hSlice] with ρ hρ hp hi
      exact le_of_lt (lt_of_not_ge fun hc => h ⟨ρ, hρ, hp, hi, hc⟩)
    have hCompare := (lintegral_mono_ae hLower).trans hFatou
    rw [lintegral_const, hMass, ← ENNReal.ofReal_mul hC.le] at hCompare
    have hCancel : C * (R - r) = 2 * M := div_mul_cancel₀ _ hWidth.ne'
    rw [hCancel] at hCompare
    have hImpossible := (ENNReal.ofReal_le_ofReal_iff hM.le).mp hCompare
    linarith
  obtain ⟨ρ, hρ, hp, hi, hρEnergy⟩ := hGood
  have hThreshold : 0 < 4 * M / (R - r) := by positivity
  have hStrict : ENNReal.ofReal C < ENNReal.ofReal (4 * M / (R - r)) := by
    apply (ENNReal.ofReal_lt_ofReal_iff hThreshold).2
    exact (div_lt_div_iff_of_pos_right hWidth).2 (by linarith)
  have hFreq : ∃ᶠ k in atTop, A k ρ < ENNReal.ofReal (4 * M / (R - r)) :=
    frequently_lt_of_liminf_lt (by isBoundedDefault) (hρEnergy.trans_lt hStrict)
  obtain ⟨κ, hκ, hBound⟩ := extraction_of_frequently_atTop hFreq
  refine ⟨ρ, hρ, hp, hi, κ, hκ, fun k => ?_⟩
  exact ((ENNReal.ofReal_lt_ofReal_iff hThreshold).mp (hBound k)).le

theorem integrable_energyDensity_of_energy_ne_top (a : BulkCoefficients) (ε : ElasticScale)
    {U : Set Point} {u : Point → S0} {D : Point → Gradient}
    (hu : MemH1 U u D) (hE : energy a ε U u D ≠ ⊤) :
    IntegrableOn (fun x => energyDensity a ε (u x) (D x)) U := by
  have hD : IntegrableOn (fun x => gradientNormSq (D x)) U := by
    change Integrable (fun x => gradientNormSq (D x)) (volume.restrict U)
    simpa only [HarmonicMaps.hsNormSq, frobeniusGradient, LinearIsometryEquiv.norm_map,
      gradientNormSq_eq_sum_norm_sq] using
      HarmonicMaps.integrable_hsNormSq_of_memLp_columns (memLp_frobeniusGradient_columns hu.2.1)
  exact (hD.const_mul _).add ((memLp_one_iff_integrable).mp
    (memLp_scaledPotential_of_energy_ne_top a ε hu hE))

theorem energyDensity_nonneg (a : BulkCoefficients) (ε : ElasticScale)
    (u : S0) (D : Gradient) : 0 ≤ energyDensity a ε u D := by
  rw [energyDensity, gradientNormSq_eq_sum_norm_sq]
  exact add_nonneg (mul_nonneg (by norm_num) (Finset.sum_nonneg fun j _ => sq_nonneg ‖D j‖))
    (mul_nonneg (sq_nonneg _) (bulkPotential_nonneg a u))

/-- A good radius for the actual penalized sequence has the source's
uniform boundary-energy bound and strong angular L² convergence on the
same subsequence. Other almost-everywhere slice data may be retained. -/
theorem exists_good_polar_radius_of_penalized_energy_and_strongL2
    (a : BulkCoefficients) (ε : ℕ → ElasticScale) (c : Point) {r R M : ℝ}
    (hr : 0 < r) (hrR : r < R) (hM : 0 < M)
    (u : ℕ → Point → S0) (D : ℕ → Point → Gradient) (v : Point → S0)
    (hu : ∀ k, MemH1 (Metric.ball c R) (u k) (D k))
    (hv : MemLp v 2 (volume.restrict (Metric.ball c R)))
    (hEnergy : ∀ k, energy a (ε k) (Metric.ball c R) (u k) (D k) ≤ ENNReal.ofReal M)
    (hStrong : Tendsto (fun k => eLpNorm (u k - v) 2 (volume.restrict (Metric.ball c R)))
      atTop (𝓝 0))
    (P : ℝ → Prop) (hP : ∀ᵐ ρ ∂volume.restrict (Ioo r R), P ρ) :
    ∃ ρ ∈ Ioo r R, P ρ ∧
      (∀ k, Integrable (fun θ : Metric.sphere (0 : Point) 1 =>
        energyDensity a (ε k) (u k (c + ρ • θ.val)) (D k (c + ρ • θ.val)))
        (volume : Measure Point).toSphere) ∧
      ∃ κ : ℕ → ℕ, StrictMono κ ∧
        (∀ k, polarIntegralDensity c (fun x => energyDensity a (ε (κ k)) (u (κ k) x) (D (κ k) x)) ρ
          ≤ 4 * M / (R - r)) ∧
        Tendsto (fun k => ∫ θ : Metric.sphere (0 : Point) 1,
          ‖u (κ k) (c + ρ • θ.val) - v (c + ρ • θ.val)‖ ^ 2
            ∂(volume : Measure Point).toSphere) atTop (𝓝 0) := by
  let f (k : ℕ) (x : Point) := energyDensity a (ε k) (u k x) (D k x)
  let μ := volume.restrict (Metric.ball c R)
  have hI (k : ℕ) : IntegrableOn (f k) (Metric.ball c R) :=
    integrable_energyDensity_of_energy_ne_top a (ε k) (hu k)
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hEnergy k))
  have hF₀ (k : ℕ) (x : Point) : 0 ≤ f k x := energyDensity_nonneg a (ε k) (u k x) (D k x)
  have hBound (k : ℕ) : (∫ x in Metric.ball c R, f k x) ≤ M := by
    apply (ENNReal.ofReal_le_ofReal_iff hM.le).mp
    rw [ofReal_integral_eq_lintegral_ofReal (hI k) (Eventually.of_forall (hF₀ k))]
    exact hEnergy k
  let u' (k : ℕ) := frobeniusField (u k)
  let v' := frobeniusField v
  have hu' (k : ℕ) : MemLp (u' k) 2 μ := (frobeniusCoordinateEquiv_memLp_iff _ _ _).mpr (hu k).1
  have hv' : MemLp v' 2 μ := (frobeniusCoordinateEquiv_memLp_iff _ _ _).mpr hv
  have hStrong' : Tendsto (fun k => eLpNorm (u' k - v') 2 μ) atTop (𝓝 0) := by
    apply hStrong.congr
    intro k
    apply eLpNorm_congr_norm_ae
    exact Eventually.of_forall fun x => by
      change ‖u k x - v x‖ =
        ‖frobeniusCoordinateEquiv (u k x) - frobeniusCoordinateEquiv (v x)‖
      rw [← map_sub, LinearIsometryEquiv.norm_map]
  obtain ⟨κ₀, hκ₀, hSlice⟩ := StratificationTheory.exists_subseq_ae_tendsto_polar_l2_ball
    (n := 3) (q := 5) (by decide) hu' hv' hStrong'
  let P' (ρ : ℝ) : Prop := P ρ ∧
    Tendsto (fun k => ∫ θ : Metric.sphere (0 : Point) 1,
      ‖u' (κ₀ k) (c + ρ • θ.val) - v' (c + ρ • θ.val)‖ ^ 2
        ∂(volume : Measure Point).toSphere) atTop (𝓝 0)
  have hsub : Ioo r R ⊆ Ioo (0 : ℝ) R := fun _ h => ⟨hr.trans h.1, h.2⟩
  have hP' : ∀ᵐ ρ ∂volume.restrict (Ioo r R), P' ρ :=
    hP.and (ae_restrict_of_ae_restrict_of_subset hsub (hSlice.mono fun _ hx => hx.2))
  have hSlicesAll : ∀ᵐ ρ ∂volume.restrict (Ioo r R), ∀ k,
      Integrable (fun θ : Metric.sphere (0 : Point) 1 => f k (c + ρ • θ.val))
        (volume : Measure Point).toSphere :=
    ae_all_iff.mpr fun k => ae_restrict_of_ae_restrict_of_subset hsub
      (StratificationTheory.ae_integrable_polar_slice_ball (n := 3) (hI k))
  obtain ⟨ρ, hρ, ⟨⟨hp, hConv⟩, hAll⟩, _, κ₁, hκ₁, hB⟩ :=
    exists_good_radius_subsequence_of_bounded_polar_energy c hr hrR hM (f ∘ κ₀)
      (fun k => hI (κ₀ k)) (fun k => hF₀ (κ₀ k)) (fun k => hBound (κ₀ k))
      (fun ρ => P' ρ ∧ ∀ k, Integrable
        (fun θ : Metric.sphere (0 : Point) 1 => f k (c + ρ • θ.val))
        (volume : Measure Point).toSphere) (hP'.and hSlicesAll)
  refine ⟨ρ, hρ, hp, hAll, κ₀ ∘ κ₁, hκ₀.comp hκ₁, hB, ?_⟩
  have hNorm (k : ℕ) (x : Point) : ‖u' k x - v' x‖ = ‖u k x - v x‖ := by
    change ‖frobeniusCoordinateEquiv (u k x) - frobeniusCoordinateEquiv (v x)‖ =
      ‖u k x - v x‖
    rw [← map_sub, LinearIsometryEquiv.norm_map]
  simpa only [Function.comp_def, hNorm] using hConv.comp hκ₁.tendsto_atTop

/-- A Sobolev shell joining the given outer and inner maps by their
continuous radial L² traces. -/
structure RadialAnnularConnector (c : Point) (s R : ℝ) (hsR : s < R)
    (outer inner : Point → S0) where
  radius : ℝ
  radius_pos : 0 < radius
  radius_lt : radius < s
  toFun : Point → S0
  gradient : Point → Gradient
  sobolev : MemH1 (radialAnnulus c radius s) toFun gradient
  innerTrace : RadialL2Trace (s / 2) s
  connectorTrace : RadialL2Trace radius s
  outerTrace : RadialL2Trace s ((s + R) / 2)
  innerData : RepresentsRadialL2Trace c inner innerTrace
  connectorData : RepresentsRadialL2Trace c toFun connectorTrace
  outerData : RepresentsRadialL2Trace c outer outerTrace
  matchInner : innerTrace ⟨s, by linarith only [radius_pos, radius_lt], le_rfl⟩ =
    connectorTrace ⟨radius, le_rfl, radius_lt.le⟩
  matchOuter : connectorTrace ⟨s, radius_lt.le, le_rfl⟩ =
    outerTrace ⟨s, le_rfl, by linarith only [hsR]⟩

/-- Annular competitors with vanishing cost give the energy limsup bound
for their prescribed vacuum interior map. -/
theorem energy_limsup_le_dirichlet_of_annular_connectors
    (a : BulkCoefficients) (ε : ℕ → ElasticScale) {Ω : Set Point}
    (c : Point) {s R : ℝ} (hsR : s < R) (hR : Metric.closedBall c R ⊆ Ω)
    (u : ℕ → Point → S0) (D : ℕ → Point → Gradient) (v : Point → S0) (G : Point → Gradient)
    (hMin : ∀ k, IsLocalEnergyMinimizer a (ε k) Ω (u k) (D k))
    (hFinite : ∀ k, energy a (ε k) (Metric.ball c R) (u k) (D k) ≠ ⊤)
    (hV : MemH1 (Metric.ball c s) v G) (hVN : TakesVacuumValues a (Metric.ball c s) v)
    (cost : ℕ → ℝ≥0∞) (hCost : Tendsto cost atTop (𝓝 0))
    (hShells : ∀ᶠ k in atTop, ∃ W : RadialAnnularConnector c s R hsR (u k) v,
      energy a (ε k) (radialAnnulus c W.radius s) W.toFun W.gradient ≤ cost k) :
    atTop.limsup (fun k => energy a (ε k) (Metric.ball c s) (u k) (D k)) ≤
      dirichletEnergy (Metric.ball c s) G := by
  have hUpper : ∀ᶠ k in atTop,
      energy a (ε k) (Metric.ball c s) (u k) (D k) ≤
        dirichletEnergy (Metric.ball c s) G + cost k := by
    filter_upwards [hShells] with k hk
    obtain ⟨W, hW⟩ := hk
    have hC := energy_le_scaledDirichlet_add_annulus_of_matching_radial_traces a (ε k)
      c W.radius_pos W.radius_lt hsR hR (u k) v W.toFun (D k) G W.gradient
      (hMin k) (hFinite k) hV hVN W.sobolev W.innerTrace W.connectorTrace W.outerTrace
      W.innerData W.connectorData W.outerData W.matchInner W.matchOuter
    have hCoeff : ENNReal.ofReal (W.radius / s) ≤ 1 := by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal
        ((div_le_iff₀ (W.radius_pos.trans W.radius_lt)).2 (by simpa using W.radius_lt.le))
    have hCoeffEnergy := mul_le_mul_left hCoeff (dirichletEnergy (Metric.ball c s) G)
    rw [one_mul] at hCoeffEnergy
    exact hC.trans (add_le_add hCoeffEnergy hW)
  have hLim : Tendsto (fun k => dirichletEnergy (Metric.ball c s) G + cost k)
      atTop (𝓝 (dirichletEnergy (Metric.ball c s) G)) := by
    simpa only [add_zero] using
      (tendsto_const_nhds (x := dirichletEnergy (Metric.ball c s) G)).add hCost
  exact (limsup_le_limsup hUpper).trans_eq hLim.limsup_eq

/-- An eventual supply of actual annular connectors with vanishing shell
cost closes the energy comparison on a single interior ball. -/
theorem strongH1_and_scaledPotential_of_annular_connectors
    (a : BulkCoefficients) (ε : ℕ → ElasticScale) {Ω : Set Point}
    (c : Point) {s R : ℝ} (hsR : s < R) (hR : Metric.closedBall c R ⊆ Ω)
    (u : ℕ → Point → S0) (D : ℕ → Point → Gradient) (v : Point → S0) (G : Point → Gradient)
    (hMin : ∀ k, IsLocalEnergyMinimizer a (ε k) Ω (u k) (D k))
    (hFinite : ∀ k, energy a (ε k) (Metric.ball c R) (u k) (D k) ≠ ⊤)
    (hU : ∀ k, MemH1 (Metric.ball c s) (u k) (D k))
    (hV : MemH1 (Metric.ball c s) v G) (hVN : TakesVacuumValues a (Metric.ball c s) v)
    (hStrong : Tendsto (fun k => eLpNorm (u k - v) 2 (volume.restrict (Metric.ball c s)))
      atTop (𝓝 0))
    (hWeak : ∀ j : Fin 3,
      WeakL2FrobeniusConvergence (Metric.ball c s) (fun k x => D k x j) (fun x => G x j))
    (cost : ℕ → ℝ≥0∞) (hCost : Tendsto cost atTop (𝓝 0))
    (hShells : ∀ᶠ k in atTop, ∃ W : RadialAnnularConnector c s R hsR (u k) v,
      energy a (ε k) (radialAnnulus c W.radius s) W.toFun W.gradient ≤ cost k) :
    StrongH1 (Metric.ball c s) u D v G ∧
      (∀ k, MemLp (fun x => (ε k : ℝ)⁻¹ ^ 2 * bulkPotential a (u k x))
        1 (volume.restrict (Metric.ball c s))) ∧
      Tendsto (fun k => eLpNorm (fun x => (ε k : ℝ)⁻¹ ^ 2 * bulkPotential a (u k x))
        1 (volume.restrict (Metric.ball c s))) atTop (𝓝 0) ∧
      Tendsto (fun k => energy a (ε k) (Metric.ball c s) (u k) (D k))
        atTop (𝓝 (dirichletEnergy (Metric.ball c s) G)) := by
  apply strongH1_and_scaledPotential_of_limsup_energy_le_dirichlet a ε hU hV hStrong hWeak
  · intro k
    exact ne_top_of_le_ne_top (hFinite k) (lintegral_mono_set (Metric.ball_subset_ball hsR.le))
  · exact energy_limsup_le_dirichlet_of_annular_connectors a ε c hsR hR u D v G
      hMin hFinite hV hVN cost hCost hShells

private theorem tendsto_lintegral_zero_on_compact_of_ball (Ω : HarmonicMaps.OpenDomain 3)
    (f : ℕ → Point → ℝ≥0∞)
    (hBall : ∀ (c : Point) (r : ℝ), 0 < r → Metric.closedBall c r ⊆ Ω.val →
      Tendsto (fun k => ∫⁻ x in Metric.ball c r, f k x) atTop (𝓝 0))
    (K : Set Point) (hK : IsCompact K) (hKΩ : K ⊆ Ω.val) :
    Tendsto (fun k => ∫⁻ x in K, f k x) atTop (𝓝 0) := by
  classical
  obtain ⟨t, R, hR, hCover⟩ :=
    StratificationTheory.Compactness.exists_finite_interior_ball_cover Ω K hK hKΩ
  let I := {x : K // x ∈ t}
  letI : Fintype I := inferInstanceAs (Fintype {x : K // x ∈ t})
  let U (j : I) := Metric.ball j.val.val ((R j.val).val / 2)
  have hSubset : K ⊆ ⋃ j : I, U j := by
    intro x hx
    obtain ⟨c, hc, hxc⟩ := mem_iUnion₂.mp (hCover hx)
    exact mem_iUnion.mpr ⟨⟨c, hc⟩, hxc⟩
  have hMeasure : volume.restrict K ≤ ∑ j : I, volume.restrict (U j) := calc
    _ ≤ volume.restrict (⋃ j : I, U j) := Measure.restrict_mono_set volume hSubset
    _ ≤ Measure.sum (fun j : I => volume.restrict (U j)) := Measure.restrict_iUnion_le
    _ = _ := Measure.sum_fintype _
  have hTerm (j : I) : Tendsto (fun k => ∫⁻ x in U j, f k x) atTop (𝓝 0) :=
    hBall j.val.val ((R j.val).val / 2) (half_pos (R j.val).property)
      ((Metric.closedBall_subset_closedBall (by linarith only [(R j.val).property])).trans
        (hR j.val))
  have hSum : Tendsto (fun k => ∑ j : I, ∫⁻ x in U j, f k x) atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum Finset.univ (fun j _ => hTerm j)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hSum (fun _ => zero_le) ?_
  intro k
  calc
    (∫⁻ x in K, f k x) ≤ ∫⁻ x, f k x ∂∑ j : I, volume.restrict (U j) :=
      lintegral_mono' hMeasure le_rfl
    _ = _ := lintegral_finsetSum_measure Finset.univ (f k) _

/-- Convergence on the comparison balls passes to both frozen local
convergence predicates by finite covers of compact subsets. -/
theorem strongH1Loc_and_scaledPotentialLoc_of_ball_convergence
    (a : BulkCoefficients) (ε : ℕ → ElasticScale) {Ω : Set Point} (hΩ : IsOpen Ω)
    (u : ℕ → Point → S0) (D : ℕ → Point → Gradient) (v : Point → S0) (G : Point → Gradient)
    (hU : ∀ k, MemH1Loc Ω (u k) (D k)) (hV : MemH1Loc Ω v G)
    (hFinite : ∀ k, energy a (ε k) Ω (u k) (D k) ≠ ⊤)
    (hBall : ∀ (c : Point) (r : ℝ), 0 < r → Metric.closedBall c r ⊆ Ω →
      StrongH1 (Metric.ball c r) u D v G ∧
      Tendsto (fun k => eLpNorm (fun x => (ε k : ℝ)⁻¹ ^ 2 * bulkPotential a (u k x))
        1 (volume.restrict (Metric.ball c r))) atTop (𝓝 0)) :
    StrongH1Loc Ω u D v G ∧ ConvergesScaledPotentialLoc a Ω ε u := by
  let F (k : ℕ) (x : Point) := ENNReal.ofReal
    (‖u k x - v x‖ ^ 2 + ∑ j, ‖D k x j - G x j‖ ^ 2)
  let V (k : ℕ) (x : Point) := ‖(ε k : ℝ)⁻¹ ^ 2 * bulkPotential a (u k x)‖ₑ
  have hStrong (K : Set Point) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
      Tendsto (fun k => h1Deviation K (u k) v (D k) G) atTop (𝓝 0) :=
    tendsto_lintegral_zero_on_compact_of_ball ⟨Ω, hΩ⟩ F
      (fun c r hr hrΩ => (hBall c r hr hrΩ).1.2.2) K hK hKΩ
  have hPot (K : Set Point) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
      Tendsto (fun k => ∫⁻ x in K, V k x) atTop (𝓝 0) :=
    tendsto_lintegral_zero_on_compact_of_ball ⟨Ω, hΩ⟩ V
      (fun c r hr hrΩ => by simpa only [eLpNorm_one_eq_lintegral_enorm] using
        (hBall c r hr hrΩ).2) K hK hKΩ
  constructor
  · intro W hW hWΩ
    refine ⟨fun k => hU k W hW hWΩ, hV W hW hWΩ, ?_⟩
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (hStrong (closure W) hWΩ.1 hWΩ.2) (fun _ => zero_le)
      (fun _ => h1Deviation_mono subset_closure)
  · intro W hW hWΩ
    refine ⟨fun k => memLp_scaledPotential_of_energy_ne_top a (ε k) (hU k W hW hWΩ)
      (ne_top_of_le_ne_top (hFinite k) (lintegral_mono_set (subset_closure.trans hWΩ.2))), ?_⟩
    simp only [eLpNorm_one_eq_lintegral_enorm]
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (hPot (closure W) hWΩ.1 hWΩ.2) (fun _ => zero_le) (fun _ => lintegral_mono_set subset_closure)

/-- If each strict subsequence has a further convergent subsequence on a
fixed ball, with the same limit map and gradient, the two convergence
claims hold there for the original sequence. -/
theorem strongH1_and_scaledPotential_of_ball_subsubsequences
    (a : BulkCoefficients) (ε : ℕ → ElasticScale) (c : Point) (r : ℝ)
    (u : ℕ → Point → S0) (D : ℕ → Point → Gradient) (v : Point → S0) (G : Point → Gradient)
    (hU : ∀ k, MemH1 (Metric.ball c r) (u k) (D k)) (hV : MemH1 (Metric.ball c r) v G)
    (hSub : ∀ κ : ℕ → ℕ, StrictMono κ → ∃ σ : ℕ → ℕ, StrictMono σ ∧
      StrongH1 (Metric.ball c r) (fun k => u (κ (σ k))) (fun k => D (κ (σ k))) v G ∧
      Tendsto (fun k => eLpNorm (fun x => (ε (κ (σ k)) : ℝ)⁻¹ ^ 2 * bulkPotential a (u (κ (σ k)) x))
        1 (volume.restrict (Metric.ball c r))) atTop (𝓝 0)) :
    StrongH1 (Metric.ball c r) u D v G ∧
      Tendsto (fun k => eLpNorm (fun x => (ε k : ℝ)⁻¹ ^ 2 * bulkPotential a (u k x))
        1 (volume.restrict (Metric.ball c r))) atTop (𝓝 0) := by
  let F (k : ℕ) := h1Deviation (Metric.ball c r) (u k) v (D k) G
  let H (k : ℕ) := eLpNorm (fun x => (ε k : ℝ)⁻¹ ^ 2 * bulkPotential a (u k x))
    1 (volume.restrict (Metric.ball c r))
  have hConv : Tendsto (fun k => (F k, H k)) atTop (𝓝 (0, 0)) := by
    apply StratificationTheory.Compactness.tendsto_of_strict_subsequence
    intro κ hκ
    obtain ⟨σ, hσ, hStrong, hPot⟩ := hSub κ hκ
    exact ⟨σ, hσ, hStrong.2.2.prodMk_nhds hPot⟩
  rw [nhds_prod_eq] at hConv
  have hF : Tendsto F atTop (𝓝 0) := hConv.fst
  have hH : Tendsto H atTop (𝓝 0) := hConv.snd
  exact ⟨⟨hU, hV, hF⟩, hH⟩

open scoped Classical in
/-- A same-trace vacuum competitor on a smaller ball extends by the
original map, with its literal piecewise gradient and matching outer trace. -/
theorem extend_sameTrace_vacuum_competitor_ball
    (a : BulkCoefficients) (c : Point) {r R : ℝ} (hrR : r ≤ R)
    (v z : Point → S0) (G J : Point → Gradient)
    (hv : MemH1 (Metric.ball c R) v G) (hvN : TakesVacuumValues a (Metric.ball c R) v)
    (hzN : TakesVacuumValues a (Metric.ball c r) z)
    (hzTrace : SameTrace (Metric.ball c r) z v J G) :
    let w := (Metric.ball c r).piecewise z v
    let D := (Metric.ball c r).piecewise J G
    MemH1 (Metric.ball c R) w D ∧ TakesVacuumValues a (Metric.ball c R) w ∧
      SameTrace (Metric.ball c R) w v D G := by
  classical
  let Br := HarmonicMaps.ballDomain c r
  let BR := HarmonicMaps.ballDomain c R
  let N := vacuumCompactSmoothEmbeddedTarget a
  have hN := vacuumCompactSmoothEmbeddedTarget_carrierSet a
  have hv' := (memH1_iff_memW12 BR v G).mp hv
  have hvN' := (takesVacuumValues_iff_upstream a BR N hN v).mp hvN
  have hzN' := (takesVacuumValues_iff_upstream a Br N hN z).mp hzN
  have hSame := (sameTrace_iff_hasZeroBoundaryDifference Br z v J G).mp hzTrace
  obtain ⟨W, E, hWEq, hEEq, hMem, hWVac, hOuter⟩ :=
    StratificationTheory.Interpolation.extend_zeroBoundary_competitor_ball N hrR hv' hvN' hzN' hSame
  dsimp only
  let w := (Metric.ball c r).piecewise z v
  let D := (Metric.ball c r).piecewise J G
  have hw : frobeniusField w = W := by
    rw [hWEq]
    funext x
    by_cases hx : x ∈ Metric.ball c r
    · simp only [w, frobeniusField, piecewise_eq_of_mem _ _ _ hx]
    · simp only [w, frobeniusField, piecewise_eq_of_notMem _ _ _ hx]
  have hD : frobeniusGradient D = E := by
    rw [hEEq]
    funext x j
    by_cases hx : x ∈ Metric.ball c r
    · simp only [D, frobeniusGradient, piecewise_eq_of_mem _ _ _ hx]
    · simp only [D, frobeniusGradient, piecewise_eq_of_notMem _ _ _ hx]
  refine ⟨(memH1_iff_memW12 BR w D).2 ?_,
    (takesVacuumValues_iff_upstream a BR N hN w).2 ?_,
    (sameTrace_iff_hasZeroBoundaryDifference BR w v D G).2 ?_⟩
  · rwa [hw, hD]
  · rwa [hw]
  · rwa [hw, hD]

private theorem dirichletEnergy_eq_add_sdiff {A B : Set Point}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hAB : A ⊆ B)
    (D : Point → Gradient) :
    dirichletEnergy B D = dirichletEnergy A D + dirichletEnergy (B \ A) D := by
  unfold dirichletEnergy
  rw [← lintegral_union (hB.diff hA) disjoint_sdiff_right, union_sdiff_cancel hAB]

/-- Dirichlet minimality on a ball passes to every smaller concentric ball
by extending its same-trace competitors by the original vacuum map. -/
theorem dirichletComparison_on_smaller_concentric_ball
    (a : BulkCoefficients) (c : Point) {r R : ℝ} (hrR : r ≤ R)
    (v : Point → S0) (G : Point → Gradient)
    (hv : MemH1 (Metric.ball c R) v G) (hvN : TakesVacuumValues a (Metric.ball c R) v)
    (hMin : ∀ (z : Point → S0) (J : Point → Gradient),
      MemH1 (Metric.ball c R) z J → TakesVacuumValues a (Metric.ball c R) z →
      SameTrace (Metric.ball c R) z v J G →
      dirichletEnergy (Metric.ball c R) G ≤ dirichletEnergy (Metric.ball c R) J)
    (z : Point → S0) (J : Point → Gradient)
    (hzN : TakesVacuumValues a (Metric.ball c r) z)
    (hzTrace : SameTrace (Metric.ball c r) z v J G) :
    dirichletEnergy (Metric.ball c r) G ≤ dirichletEnergy (Metric.ball c r) J := by
  classical
  let A := Metric.ball c r
  let B := Metric.ball c R
  let w := A.piecewise z v
  let D := A.piecewise J G
  obtain ⟨hMem, hVac, hTrace⟩ :=
    extend_sameTrace_vacuum_competitor_ball a c hrR v z G J hv hvN hzN hzTrace
  have hComparison := hMin w D hMem hVac hTrace
  have hA : MeasurableSet A := measurableSet_ball
  have hB : MeasurableSet B := measurableSet_ball
  have hAB : A ⊆ B := Metric.ball_subset_ball hrR
  have hInner : dirichletEnergy A D = dirichletEnergy A J := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem hA] with x hx
    rw [show D x = J x from piecewise_eq_of_mem _ _ _ hx]
  have hOuter : dirichletEnergy (B \ A) D = dirichletEnergy (B \ A) G := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem (hB.diff hA)] with x hx
    rw [show D x = G x from piecewise_eq_of_notMem _ _ _ hx.2]
  have hFinite : dirichletEnergy (B \ A) G ≠ ⊤ :=
    ne_top_of_le_ne_top (dirichletEnergy_ne_top_of_columns hv.2.1) (lintegral_mono_set sdiff_subset)
  rw [dirichletEnergy_eq_add_sdiff hA hB hAB G,
    dirichletEnergy_eq_add_sdiff hA hB hAB D, hInner, hOuter] at hComparison
  exact (ENNReal.add_le_add_iff_right hFinite).mp hComparison

/-- An interior positive radial interval has a unique continuous trace
representing the original Sobolev slices. -/
theorem existsUnique_radialL2Trace_of_memH1Loc {Ω : Set Point} (hΩ : IsOpen Ω)
    {u : Point → S0} {D : Point → Gradient} (hu : MemH1Loc Ω u D)
    (c : Point) {r s : ℝ} (hr : 0 < r) (hrs : r < s) (hs : Metric.closedBall c s ⊆ Ω) :
    ∃! H : RadialL2Trace r s, RepresentsRadialL2Trace c u H :=
  StratificationTheory.ambient_radial_trace_existsUnique (by decide : 2 ≤ 3)
    ((memH1Loc_iff_memW12Loc ⟨Ω, hΩ⟩ u D).mp hu) hr hrs hs

@[expose] def restrict_radialL2Trace {r s r' s' : ℝ} (H : RadialL2Trace r s)
    (hr : r ≤ r') (hs : s' ≤ s) : RadialL2Trace r' s' :=
  H.comp ⟨fun t => ⟨t.val, hr.trans t.property.1, t.property.2.trans hs⟩,
    continuous_subtype_val.subtype_mk _⟩

theorem RepresentsRadialL2Trace.restrict {c : Point} {r s r' s' : ℝ}
    {u : Point → S0} {H : RadialL2Trace r s}
    (h : RepresentsRadialL2Trace c u H) (hr : r ≤ r') (hs : s' ≤ s) :
    RepresentsRadialL2Trace c u (restrict_radialL2Trace H hr hs) := by
  unfold RepresentsRadialL2Trace at *
  filter_upwards [h] with t ht ht'
  exact ht ⟨hr.trans_lt ht'.1, ht'.2.trans_le hs⟩

private theorem RepresentsRadialL2Trace.congr_slice {c : Point} {r s : ℝ}
    {u v : Point → S0} {H : RadialL2Trace r s} (h : RepresentsRadialL2Trace c u H)
    (hSame : ∀ t ∈ Ioo r s, ∀ θ : Metric.sphere (0 : Point) 1, u (c + t • θ.val) = v (c + t • θ.val)) :
    RepresentsRadialL2Trace c v H := by
  unfold RepresentsRadialL2Trace at *
  filter_upwards [h] with t ht hmem
  obtain ⟨hLp, hSlice⟩ := ht hmem
  have hEq : (fun θ : Metric.sphere (0 : Point) 1 => frobeniusField u (c + t • θ.val)) =
      (fun θ : Metric.sphere (0 : Point) 1 => frobeniusField v (c + t • θ.val)) :=
    funext fun θ => congrArg frobeniusCoordinateEquiv (hSame t hmem θ)
  have hLp' := hEq ▸ hLp
  exact ⟨hLp', hSlice.trans (MemLp.toLp_congr hLp hLp'
    (Eventually.of_forall (fun θ => congrFun hEq θ)))⟩

/-- A same-trace competitor has the same radial endpoint class as the
original map, obtained from its Sobolev extension across that sphere. -/
theorem exists_inner_radialL2Trace_eq_of_sameTrace
    (a : BulkCoefficients) (c : Point) {s R : ℝ} (hs : 0 < s) (hsR : s < R)
    (v z : Point → S0) (G J : Point → Gradient)
    (hv : MemH1 (Metric.ball c R) v G) (hvN : TakesVacuumValues a (Metric.ball c R) v)
    (hzN : TakesVacuumValues a (Metric.ball c s) z)
    (hzTrace : SameTrace (Metric.ball c s) z v J G)
    (H : RadialL2Trace (s / 2) s) (hH : RepresentsRadialL2Trace c v H) :
    ∃ H' : RadialL2Trace (s / 2) s, RepresentsRadialL2Trace c z H' ∧
      H' ⟨s, by linarith only [hs], le_rfl⟩ = H ⟨s, by linarith only [hs], le_rfl⟩ := by
  classical
  let w := (Metric.ball c s).piecewise z v
  have hw := (extend_sameTrace_vacuum_competitor_ball a c hsR.le v z G J hv hvN hzN hzTrace).1
  let m : ℝ := (s + R) / 2
  have hsm : s < m := by dsimp only [m]; linarith
  have hmR : m < R := by dsimp only [m]; linarith
  have ha : 0 < s / 2 := half_pos hs
  have has : s / 2 < s := by linarith only [hs]
  obtain ⟨V, hV, _⟩ := existsUnique_radialL2Trace_of_memH1Loc Metric.isOpen_ball
    hv.memH1Loc c ha (has.trans hsm) (Metric.closedBall_subset_ball hmR)
  obtain ⟨W, hW, _⟩ := existsUnique_radialL2Trace_of_memH1Loc Metric.isOpen_ball
    hw.memH1Loc c ha (has.trans hsm) (Metric.closedBall_subset_ball hmR)
  let VL := restrict_radialL2Trace V (le_refl (s / 2)) hsm.le
  let WL := restrict_radialL2Trace W (le_refl (s / 2)) hsm.le
  let VR := restrict_radialL2Trace V has.le (le_refl m)
  let WR := restrict_radialL2Trace W has.le (le_refl m)
  have hDist (t : ℝ) (ht : 0 ≤ t) (θ : Metric.sphere (0 : Point) 1) :
      dist (c + t • θ.val) c = t := by
    have hNorm : ‖θ.val‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using θ.property
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht, hNorm, mul_one]
  have hLeft : RepresentsRadialL2Trace c z WL := by
    apply (hW.restrict (le_refl (s / 2)) hsm.le).congr_slice
    intro t ht θ
    have hMem : c + t • θ.val ∈ Metric.ball c s := by
      rw [Metric.mem_ball, hDist t (ha.trans ht.1).le]
      exact ht.2
    exact piecewise_eq_of_mem _ _ _ hMem
  have hRight : RepresentsRadialL2Trace c v WR := by
    apply (hW.restrict has.le (le_refl m)).congr_slice
    intro t ht θ
    have hMem : c + t • θ.val ∉ Metric.ball c s := by
      rw [Metric.mem_ball, hDist t (hs.trans ht.1).le]
      exact ht.1.not_gt
    exact piecewise_eq_of_notMem _ _ _ hMem
  have hVL : VL = H :=
    (existsUnique_radialL2Trace_of_memH1Loc Metric.isOpen_ball hv.memH1Loc c ha has
      (Metric.closedBall_subset_ball hsR)).unique (hV.restrict le_rfl hsm.le) hH
  have hVR : WR = VR :=
    (existsUnique_radialL2Trace_of_memH1Loc Metric.isOpen_ball hv.memH1Loc c hs hsm
      (Metric.closedBall_subset_ball hmR)).unique hRight (hV.restrict has.le le_rfl)
  refine ⟨WL, hLeft, ?_⟩
  calc
    WL ⟨s, has.le, le_rfl⟩ = WR ⟨s, le_rfl, hsm.le⟩ := rfl
    _ = VR ⟨s, le_rfl, hsm.le⟩ := congrArg (fun F : RadialL2Trace s m => F ⟨s, le_rfl, hsm.le⟩) hVR
    _ = VL ⟨s, has.le, le_rfl⟩ := rfl
    _ = H ⟨s, has.le, le_rfl⟩ := congrArg (fun F : RadialL2Trace (s / 2) s => F ⟨s, has.le, le_rfl⟩) hVL

/-- Shells connecting the weak limit itself suffice to compare the limit
with every same-trace vacuum map on the chosen ball. -/
theorem dirichletComparison_of_annular_connectors
    (a : BulkCoefficients) (ε : ℕ → ElasticScale) {Ω : Set Point}
    (c : Point) {s R : ℝ} (hs : 0 < s) (hsR : s < R) (hR : Metric.closedBall c R ⊆ Ω)
    (u : ℕ → Point → S0) (D : ℕ → Point → Gradient) (v : Point → S0) (G : Point → Gradient)
    (hMin : ∀ k, IsLocalEnergyMinimizer a (ε k) Ω (u k) (D k))
    (hFinite : ∀ k, energy a (ε k) (Metric.ball c R) (u k) (D k) ≠ ⊤)
    (hU : ∀ k, MemH1 (Metric.ball c s) (u k) (D k))
    (hV : MemH1 (Metric.ball c R) v G) (hVN : TakesVacuumValues a (Metric.ball c R) v)
    (hWeak : ∀ j : Fin 3,
      WeakL2FrobeniusConvergence (Metric.ball c s) (fun k x => D k x j) (fun x => G x j))
    (cost : ℕ → ℝ≥0∞) (hCost : Tendsto cost atTop (𝓝 0))
    (hShells : ∀ᶠ k in atTop, ∃ W : RadialAnnularConnector c s R hsR (u k) v,
      energy a (ε k) (radialAnnulus c W.radius s) W.toFun W.gradient ≤ cost k)
    (z : Point → S0) (J : Point → Gradient)
    (hz : MemH1 (Metric.ball c s) z J) (hzN : TakesVacuumValues a (Metric.ball c s) z)
    (hzTrace : SameTrace (Metric.ball c s) z v J G) :
    dirichletEnergy (Metric.ball c s) G ≤ dirichletEnergy (Metric.ball c s) J := by
  have hShellsZ : ∀ᶠ k in atTop, ∃ W : RadialAnnularConnector c s R hsR (u k) z,
      energy a (ε k) (radialAnnulus c W.radius s) W.toFun W.gradient ≤ cost k := by
    filter_upwards [hShells] with k hk
    obtain ⟨W, hW⟩ := hk
    obtain ⟨H, hH, hEndpoint⟩ :=
      exists_inner_radialL2Trace_eq_of_sameTrace a c hs hsR v z G J hV hVN hzN hzTrace
        W.innerTrace W.innerData
    let W' : RadialAnnularConnector c s R hsR (u k) z :=
      { radius := W.radius
        radius_pos := W.radius_pos
        radius_lt := W.radius_lt
        toFun := W.toFun
        gradient := W.gradient
        sobolev := W.sobolev
        innerTrace := H
        connectorTrace := W.connectorTrace
        outerTrace := W.outerTrace
        innerData := hH
        connectorData := W.connectorData
        outerData := W.outerData
        matchInner := hEndpoint.trans W.matchInner
        matchOuter := W.matchOuter }
    exact ⟨W', hW⟩
  have hUpper := energy_limsup_le_dirichlet_of_annular_connectors a ε c hsR hR u D z J
    hMin hFinite hz hzN cost hCost hShellsZ
  have hLower := dirichletEnergy_le_liminf_of_weak_frobenius
    (fun k => (hU k).2.1) (hV.mono (Metric.ball_subset_ball hsR.le)).2.1 hWeak
  have hBound (k : ℕ) : dirichletEnergy (Metric.ball c s) (D k) ≤
      energy a (ε k) (Metric.ball c s) (u k) (D k) := by
    rw [energy_eq_dirichlet_add_scaledPotential a (ε k) (u k) (hU k).2.1]
    exact le_add_right le_rfl
  exact hLower.trans (((liminf_le_liminf (Eventually.of_forall hBound)).trans liminf_le_limsup).trans hUpper)

end Thesis
end
end
