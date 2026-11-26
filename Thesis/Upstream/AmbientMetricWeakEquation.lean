module

public import Thesis.Upstream.GlobalCompactSobolevTransport
public import HolderToCK.Foundation.WeakPoisson
import Thesis.Upstream.AmbientZeroTraceExtension
import StratificationTheory.Compactness.L2PairingConvergence
import HarmonicMaps.Analysis.VariableMollificationL2

/-! The same weak Dirichlet equation under a smooth volume-preserving chart. -/

public section

noncomputable section

open Filter Function HarmonicMaps MeasureTheory Set
open scoped BigOperators ContDiff ENNReal Topology RealInnerProductSpace

namespace Thesis

/-- The ambient Hilbert product of the classical coordinate columns. -/
@[expose] def packedClassicalAmbientGradient {n q : ℕ} (u : Domain n → Ambient q)
    (x : Domain n) : AmbientGradientHilbert n q :=
  packAmbientGradient (fun j => fderiv ℝ u x (EuclideanSpace.single j 1))

/-- The signed weak divergence equation for the actual flux and source. -/
@[expose] def HasWeakPackedDivergenceEq {n q : ℕ} (U : Set (Domain n))
    (P : Domain n → AmbientGradientHilbert n q) (f : Domain n → Ambient q) : Prop :=
  ∀ (ψ : Domain n → Ambient q), ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
    (∫ x, inner ℝ (P x) (packedClassicalAmbientGradient ψ x)) = -(∫ x, inner ℝ (f x) (ψ x))

theorem HasWeakPackedDivergenceEq.mono {n q : ℕ} {U V : Set (Domain n)}
    {P : Domain n → AmbientGradientHilbert n q} {f : Domain n → Ambient q}
    (h : HasWeakPackedDivergenceEq U P f) (hVU : V ⊆ U) : HasWeakPackedDivergenceEq V P f :=
  fun ψ hS hc hs => h ψ hS hc (hs.trans hVU)

theorem weakPoissonOn_packed_indicators {n q : ℕ} {U : OpenDomain n}
    {D : Domain n → HarmonicMaps.Gradient n q} {f : Domain n → Ambient q}
    (h : HolderToCK.WeakPoissonOn U D f) :
    HasWeakPackedDivergenceEq U.val (fun x => packAmbientGradient (U.val.indicator D x))
      (U.val.indicator f) := by
  intro ψ hψ hc hSupp
  have h' := (h.2 ψ hψ hc hSupp).2.2
  have hL : (∫ x, inner ℝ (packAmbientGradient (U.val.indicator D x))
      (packedClassicalAmbientGradient ψ x)) =
      ∫ x in U.val, ∑ i : Fin n, inner ℝ (D x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1)) := by
    rw [← integral_indicator U.property.measurableSet]
    apply integral_congr_ae
    refine Eventually.of_forall fun x => ?_
    by_cases hx : x ∈ U.val
    · dsimp only
      rw [indicator_of_mem hx,indicator_of_mem hx,packedClassicalAmbientGradient,PiLp.inner_apply]
      simp only [packAmbientGradient_apply]
    · dsimp only
      rw [indicator_of_notMem hx,indicator_of_notMem hx]
      change inner ℝ (0 : AmbientGradientHilbert n q) _ = _
      rw [inner_zero_left]
  have hR : (∫ x, inner ℝ (U.val.indicator f x) (ψ x)) = ∫ x in U.val, inner ℝ (f x) (ψ x) := by
    rw [← integral_indicator U.property.measurableSet]
    apply integral_congr_ae
    refine Eventually.of_forall fun x => ?_
    by_cases hx : x ∈ U.val
    · dsimp only
      rw [indicator_of_mem hx,indicator_of_mem hx]
    · dsimp only
      rw [indicator_of_notMem hx,indicator_of_notMem hx,inner_zero_left]
  rw [hL,hR]
  exact h'

private theorem packedClassicalAmbientGradient_comp_inverse {n q : ℕ}
    {ψ : Domain n → Ambient q} (hψ : ContDiff ℝ ∞ ψ) (F : Domain n ≃ₜ Domain n)
    (hInv : ContDiff ℝ ∞ (F.symm : Domain n → Domain n)) (x : Domain n) :
    packedClassicalAmbientGradient (ψ ∘ F.symm) (F x) =
      ambientGradientPrecompose n q (fderiv ℝ F.symm (F x)) (packedClassicalAmbientGradient ψ x) := by
  rw [packedClassicalAmbientGradient,packedClassicalAmbientGradient,
    ambientGradientPrecompose_derivative_columns,
    fderiv_comp (F x) (hψ.differentiable (by simp) _) (hInv.differentiable (by simp) _),
    F.symm_apply_apply]
  rfl

private theorem ambientGradientPrecompose_pullback_inverse_id {n q : ℕ}
    (F : Domain n ≃ₜ Domain n) (hF : ContDiff ℝ ∞ (F : Domain n → Domain n))
    (hInv : ContDiff ℝ ∞ (F.symm : Domain n → Domain n))
    (D : Domain n → HarmonicMaps.Gradient n q) (x : Domain n) :
    ambientGradientPrecompose n q (fderiv ℝ F.symm (F x))
      (packAmbientGradient (ambientGradientPullback F D x)) = packAmbientGradient (D (F x)) := by
  have h := fderiv_symm_comp_fderiv_homeomorph F.symm hInv hF (F x)
  rw [Homeomorph.symm_symm,F.symm_apply_apply] at h
  rw [packAmbientGradient_pullback,ambientGradientPrecompose_comp,h,ambientGradientPrecompose_id]

/-- A volume-preserving smooth chart takes the original weak Laplacian to
the corresponding divergence form on its actual derivative columns. -/
theorem HasWeakPackedDivergenceEq.metric_pullback {n q : ℕ}
    {U V : Set (Domain n)} {D : Domain n → HarmonicMaps.Gradient n q} {g : Domain n → Ambient q}
    (h : HasWeakPackedDivergenceEq U (fun x => packAmbientGradient (D x)) g)
    (F : Domain n ≃ₜ Domain n) (hF : ContDiff ℝ ∞ (F : Domain n → Domain n))
    (hInv : ContDiff ℝ ∞ (F.symm : Domain n → Domain n))
    (hMP : MeasurePreserving F (volume : Measure (Domain n)) volume) (hV : MapsTo F V U) :
    HasWeakPackedDivergenceEq V
      (fun x => ambientGradientMetric n q (fderiv ℝ F.symm (F x))
        (packAmbientGradient (ambientGradientPullback F D x))) (g ∘ F) := by
  intro ψ hψ hc hs
  let φ : Domain n → Ambient q := ψ ∘ F.symm
  have hφ : ContDiff ℝ ∞ φ := hψ.comp hInv
  have hφEq : tsupport φ = F.symm ⁻¹' tsupport ψ := tsupport_comp_eq_preimage ψ F.symm
  have hφC : HasCompactSupport φ := by
    rw [HasCompactSupport,hφEq]
    exact F.symm.isCompact_preimage.2 hc
  have hφU : tsupport φ ⊆ U := by
    intro y hy
    rw [hφEq] at hy
    exact F.apply_symm_apply y ▸ hV (hs hy)
  have he := h φ hφ hφC hφU
  have hL : (∫ x, inner ℝ (packAmbientGradient (D x)) (packedClassicalAmbientGradient φ x)) =
      ∫ x, inner ℝ (packAmbientGradient (D (F x))) (packedClassicalAmbientGradient φ (F x)) :=
    (hMP.integral_comp F.toMeasurableEquiv.measurableEmbedding
      (fun x => inner ℝ (packAmbientGradient (D x)) (packedClassicalAmbientGradient φ x))).symm
  have hR : (∫ x, inner ℝ (g x) (φ x)) = ∫ x, inner ℝ ((g ∘ F) x) (ψ x) := by
    rw [← hMP.integral_comp F.toMeasurableEquiv.measurableEmbedding (fun x => inner ℝ (g x) (φ x))]
    simp only [φ,Function.comp_apply,F.symm_apply_apply]
  rw [hL,hR] at he
  convert he using 1
  apply integral_congr_ae
  refine Eventually.of_forall fun x => ?_
  change inner ℝ (ambientGradientMetric n q (fderiv ℝ F.symm (F x))
      (packAmbientGradient (ambientGradientPullback F D x))) (packedClassicalAmbientGradient ψ x) =
    inner ℝ (packAmbientGradient (D (F x))) (packedClassicalAmbientGradient (ψ ∘ F.symm) (F x))
  rw [inner_ambientGradientMetric,ambientGradientPrecompose_pullback_inverse_id F hF hInv,
    packedClassicalAmbientGradient_comp_inverse hψ F hInv]

private theorem tendsto_zero_eLpNorm_packAmbientGradient {n q : ℕ} {μ : Measure (Domain n)}
    {D : ℕ → Domain n → HarmonicMaps.Gradient n q}
    (hD : ∀ k (i : Fin n), MemLp (fun x => D k x i) 2 μ)
    (hLim : ∀ i, Tendsto (fun k => eLpNorm (fun x => D k x i) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun k => eLpNorm (fun x => packAmbientGradient (D k x)) 2 μ) atTop (𝓝 0) := by
  apply tendsto_eLpNorm_two_zero_of_integral_norm_sq (fun k => memLp_packAmbientGradient (hD k))
  simpa only [norm_packAmbientGradient_sq] using tendsto_integral_hsNormSq_zero hD hLim

/-- The weak packed pairing extends by strong graph approximation to
the zero extension of every actual zero-boundary test. -/
theorem HasWeakPackedDivergenceEq.of_zeroBoundary_test {n q : ℕ} {U : OpenDomain n}
    {A : Domain n → AmbientGradientHilbert n q} {f : Domain n → Ambient q}
    (h : HasWeakPackedDivergenceEq U.val A f)
    (hA : MemLp A 2 volume) (hf : MemLp f 2 volume)
    {v : Domain n → Ambient q} {D : Domain n → HarmonicMaps.Gradient n q}
    (hv : HasZeroBoundaryValues U v D) :
    (∫ x, inner ℝ (A x) (packAmbientGradient ((U.val.indicator D) x))) =
      -(∫ x, inner ℝ (f x) ((U.val.indicator v) x)) := by
  obtain ⟨φ,hS,hc,hV,hD⟩ := exists_global_smooth_approximation_of_zeroBoundary hv
  let w := U.val.indicator v
  let Y (x : Domain n) := packAmbientGradient ((U.val.indicator D) x)
  have hNative := memW12_univ_zeroExtension_of_zeroBoundary hv
  have hw : MemLp w 2 (volume : Measure (Domain n)) :=
    by simpa only [Measure.restrict_univ] using hNative.2.1
  have hZ (j : Fin n) : MemLp (fun x => (U.val.indicator D) x j) 2 (volume : Measure (Domain n)) :=
    by simpa only [Measure.restrict_univ] using hNative.2.2 j
  have hY : MemLp Y 2 (volume : Measure (Domain n)) := memLp_packAmbientGradient hZ
  have hVLp (k : ℕ) : MemLp (φ k) 2 volume := (hS k).continuous.memLp_of_hasCompactSupport (hc k).1
  let J (k : ℕ) (x : Domain n) := packedClassicalAmbientGradient (φ k) x
  have hCols (k : ℕ) (j : Fin n) : MemLp
      (fun x => fderiv ℝ (φ k) x (EuclideanSpace.single j 1)) 2 (volume : Measure (Domain n)) :=
    (((hS k).continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      ((hc k).1.fderiv_apply ℝ (EuclideanSpace.single j 1))
  have hJLp (k : ℕ) : MemLp (J k) 2 (volume : Measure (Domain n)) :=
    memLp_packAmbientGradient (hCols k)
  have hJ : Tendsto (fun k => eLpNorm (J k - Y) 2 (volume : Measure (Domain n))) atTop (𝓝 0) := by
    have hLim := tendsto_zero_eLpNorm_packAmbientGradient
      (fun k j => (hCols k j).sub (hZ j)) hD
    apply hLim.congr
    intro k
    congr 1
  have hInnerJ := StratificationTheory.Compactness.tendsto_integral_inner_of_L2_convergence hJLp hY hA hJ
  have hInnerV := StratificationTheory.Compactness.tendsto_integral_inner_of_L2_convergence hVLp hw hf hV
  have hAConv : Tendsto (fun k => ∫ x, inner ℝ (A x) (J k x)) atTop
      (𝓝 (∫ x, inner ℝ (A x) (Y x))) := by simpa only [real_inner_comm] using hInnerJ
  have hfConv : Tendsto (fun k => -(∫ x, inner ℝ (f x) (φ k x))) atTop
      (𝓝 (-(∫ x, inner ℝ (f x) (w x)))) := by simpa only [real_inner_comm] using hInnerV.neg
  exact tendsto_nhds_unique hAConv (hfConv.congr (fun k => (h (φ k) (hS k) (hc k).1 (hc k).2).symm))

end Thesis
