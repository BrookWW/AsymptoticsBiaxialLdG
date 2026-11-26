module

public import Thesis.Upstream.SmoothDifferenceQuotientLimit
import Thesis.Upstream.WeakLpBounds
import StratificationTheory.Compactness.HilbertWeakSubsequence
import StratificationTheory.Compactness.L2PairingConvergence
import HarmonicMaps.Analysis.VariableMollificationL2
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-! Identification of a weak coordinate derivative through bounded difference quotients. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Set
open scoped BigOperators ContDiff ENNReal Topology RealInnerProductSpace

namespace Thesis

/-- The distributional identity for one displayed coordinate derivative. -/
@[expose] def IsWeakAmbientCoordinatePartial {n q : ℕ} (U : Set (Domain n)) (i : Fin n)
    (v D : Domain n → Ambient q) : Prop :=
  ∀ (φ : Domain n → ℝ) (hφ : ContDiff ℝ ∞ φ),
    HasCompactSupport φ → tsupport φ ⊆ U →
      (∫ x in U, coordinateDerivative φ hφ i x • v x) = -(∫ x in U, φ x • D x)

private theorem integral_inner_set_eq_global_of_tsupport_subset {n q : ℕ}
    {U : Set (Domain n)} {v ψ : Domain n → Ambient q} (hψ : tsupport ψ ⊆ U) :
    (∫ x in U, inner ℝ (v x) (ψ x)) = ∫ x, inner ℝ (v x) (ψ x) := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  rw [image_eq_zero_of_notMem_tsupport (fun he => hx (hψ he)),inner_zero_right]

private theorem inner_twoLp_toLp_eq_integral {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {μ : Measure X}
    {v w : X → E} (hv : MemLp v 2 μ) (hw : MemLp w 2 μ) :
    inner ℝ (hv.toLp v) (hw.toLp w) = ∫ x, inner ℝ (v x) (w x) ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hv.coeFn_toLp,hw.coeFn_toLp] with x hx hy
  rw [hx,hy]

private theorem weakCoordinatePartial_from_differenceLimit
    {n q : ℕ} {U : Set (Domain n)}
    {v : Domain n → Ambient q} (hv : MemLp v 2 volume)
    (i : Fin n) {h : ℕ → ℝ} (h0 : Tendsto h atTop (𝓝 0)) (hNe : ∀ k, h k ≠ 0)
    (z : Lp (Ambient q) 2 (volume.restrict U))
    (hWeak : ∀ ψ : Lp (Ambient q) 2 (volume.restrict U),
      Tendsto (fun k => ∫ x in U, inner ℝ (ambientDifferenceQuotient i (h k) v x) (ψ x))
        atTop (𝓝 (∫ x in U, inner ℝ (z x) (ψ x)))) :
    IsWeakAmbientCoordinatePartial U i v z := by
  intro φ hφ hc hSub
  apply ext_inner_left ℝ
  intro c
  let ψ (x : Domain n) := φ x • c
  have hψ : ContDiff ℝ ∞ ψ := hφ.smul contDiff_const
  have hψS : tsupport ψ ⊆ tsupport φ := tsupport_smul_subset_left φ (fun _ : Domain n => c)
  have hψC : HasCompactSupport ψ := hc.of_isClosed_subset (isClosed_tsupport ψ) hψS
  have hψU : tsupport ψ ⊆ U := hψS.trans hSub
  let Dψ := coordinateDerivative ψ hψ i
  have hDψ (x : Domain n) : Dψ x = coordinateDerivative φ hφ i x • c :=
    congrArg (fun A : Domain n →L[ℝ] Ambient q => A (EuclideanSpace.single i 1))
      ((hφ.differentiable (by simp) x).hasFDerivAt.smul_const c).fderiv
  have hDψU : tsupport Dψ ⊆ U :=
    (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1)).trans hψU
  have hψLp : MemLp ψ 2 volume := hψ.continuous.memLp_of_hasCompactSupport hψC
  have hDψLp : MemLp Dψ 2 volume :=
    ((hψ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hψC.fderiv_apply ℝ (EuclideanSpace.single i 1))
  have hψR := hψLp.mono_measure (Measure.restrict_le_self : volume.restrict U ≤ volume)
  have hTestConv := tendsto_ambientDifferenceQuotient_smooth_L2 hψ hψC i
    (show Tendsto (fun k => -h k) atTop (𝓝 0) from by simpa only [neg_zero] using h0.neg)
    (fun k => neg_ne_zero.mpr (hNe k))
  have hStrong := StratificationTheory.Compactness.tendsto_integral_inner_of_L2_convergence
    (fun k => memLp_ambientDifferenceQuotient hψLp i (-h k)) hDψLp hv hTestConv
  have hStrong' : Tendsto
      (fun k => ∫ x, inner ℝ (v x) (ambientDifferenceQuotient i (-h k) ψ x))
      atTop (𝓝 (∫ x, inner ℝ (v x) (Dψ x))) := by
    simpa only [real_inner_comm] using hStrong
  have hWeak' : Tendsto
      (fun k => ∫ x in U, inner ℝ (ambientDifferenceQuotient i (h k) v x) (ψ x))
      atTop (𝓝 (∫ x in U, inner ℝ (z x) (ψ x))) := by
    let P := hψR.toLp ψ
    have hE (f : Domain n → Ambient q) :
        (∫ x in U, inner ℝ (f x) (P x)) = ∫ x in U, inner ℝ (f x) (ψ x) := by
      apply integral_congr_ae
      filter_upwards [hψR.coeFn_toLp] with x hx
      rw [hx]
    simpa only [hE] using hWeak P
  have hBoth : (∫ x, inner ℝ (v x) (Dψ x)) = -(∫ x in U, inner ℝ (z x) (ψ x)) :=
    tendsto_nhds_unique hStrong' ((hWeak'.neg).congr (fun k => by
      rw [integral_inner_set_eq_global_of_tsupport_subset hψU]
      exact (integral_inner_ambientDifferenceQuotient_right hv hψLp i (h k)).symm))
  rw [← integral_inner_set_eq_global_of_tsupport_subset hDψU] at hBoth
  have hφLp : MemLp φ 2 volume := hφ.continuous.memLp_of_hasCompactSupport hc
  have hφDLp : MemLp (coordinateDerivative φ hφ i) 2 volume :=
    ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hc.fderiv_apply ℝ (EuclideanSpace.single i 1))
  have hvR := hv.mono_measure (Measure.restrict_le_self : volume.restrict U ≤ volume)
  have hLInt : Integrable (fun x => coordinateDerivative φ hφ i x • v x) (volume.restrict U) :=
    memLp_one_iff_integrable.1 (hvR.smul (r := 1) (hφDLp.mono_measure Measure.restrict_le_self))
  have hRInt : Integrable (fun x => φ x • z x) (volume.restrict U) :=
    memLp_one_iff_integrable.1 ((Lp.memLp z).smul (r := 1) (hφLp.mono_measure Measure.restrict_le_self))
  have hL : (∫ x in U, inner ℝ (v x) (Dψ x)) =
      inner ℝ c (∫ x in U, coordinateDerivative φ hφ i x • v x) := by
    rw [← integral_inner (𝕜 := ℝ) hLInt]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      change inner ℝ (v x) (Dψ x) = inner ℝ c (coordinateDerivative φ hφ i x • v x)
      rw [hDψ,real_inner_smul_right,real_inner_smul_right,real_inner_comm (v x) c]
  have hR : (∫ x in U, inner ℝ (z x) (ψ x)) = inner ℝ c (∫ x in U, φ x • z x) := by
    rw [← integral_inner (𝕜 := ℝ) hRInt]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      change inner ℝ (z x) (φ x • c) = inner ℝ c (φ x • z x)
      rw [real_inner_smul_right,real_inner_smul_right,real_inner_comm (z x) c]
  rw [hL,hR,← inner_neg_right] at hBoth
  exact hBoth

/-- Uniform square and higher integral bounds on coordinate differences
produce the actual weak derivative with both bounds. -/
theorem exists_weakAmbientCoordinatePartial_of_differenceQuotient_bounds
    {n q : ℕ} {U : Set (Domain n)}
    {v : Domain n → Ambient q} (hv : MemLp v 2 volume)
    (i : Fin n) {h : ℕ → ℝ} (h0 : Tendsto h atTop (𝓝 0)) (hNe : ∀ k, h k ≠ 0)
    {C : ℝ} (hC : 0 ≤ C)
    (hBound : ∀ k, (∫ x in U, ‖ambientDifferenceQuotient i (h k) v x‖^2) ≤ C^2)
    {p : ℝ} (hp : 1 ≤ p) {M : ℝ≥0∞}
    (hLp : ∀ k, eLpNorm (ambientDifferenceQuotient i (h k) v)
      (ENNReal.ofReal p) (volume.restrict U) ≤ M) :
    ∃ D : Domain n → Ambient q, MemLp D 2 (volume.restrict U) ∧
      (∫ x in U, ‖D x‖^2) ≤ C^2 ∧ IsWeakAmbientCoordinatePartial U i v D ∧
      eLpNorm D (ENNReal.ofReal p) (volume.restrict U) ≤ M := by
  let μ := (volume : Measure (Domain n)).restrict U
  let δ (k : ℕ) := ambientDifferenceQuotient i (h k) v
  have hδ (k : ℕ) : MemLp (δ k) 2 μ :=
    (memLp_ambientDifferenceQuotient hv i (h k)).mono_measure Measure.restrict_le_self
  let F (k : ℕ) := (hδ k).toLp (δ k)
  have hFL (k : ℕ) : ‖F k‖ ≤ C := by
    apply le_of_sq_le_sq _ hC
    rw [show ‖F k‖ = (eLpNorm (δ k) 2 μ).toReal from Lp.norm_toLp _ _,
      ← integral_norm_sq_eq_eLpNorm_two_toReal_sq (hδ k)]
    exact hBound k
  letI : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  obtain ⟨κ,z,hκ,hZ,hWeak⟩ := StratificationTheory.Compactness.exists_weakly_convergent_subsequence F C hFL
  have hConv (ψ : Lp (Ambient q) 2 μ) :
      Tendsto (fun k => ∫ x in U, inner ℝ (ambientDifferenceQuotient i (h (κ k)) v x) (ψ x))
        atTop (𝓝 (∫ x in U, inner ℝ (z x) (ψ x))) := by
    let hp : MemLp (ψ : Domain n → Ambient q) 2 μ := Lp.memLp ψ
    have hEq (k : ℕ) : inner ℝ (F (κ k)) ψ =
        ∫ x in U, inner ℝ (ambientDifferenceQuotient i (h (κ k)) v x) (ψ x) := by
      have he := inner_twoLp_toLp_eq_integral (hδ (κ k)) hp
      rw [Lp.toLp_coeFn ψ] at he
      exact he
    rw [← L2.inner_def]
    exact (hWeak ψ).congr hEq
  have hHigher : eLpNorm z (ENNReal.ofReal p) μ ≤ M := by
    apply eLpNorm_le_of_weak_L2_limit hp (fun k => F (κ k)) z hWeak
    intro k
    exact (eLpNorm_congr_ae (hδ (κ k)).coeFn_toLp).trans_le (hLp (κ k))
  refine ⟨z,Lp.memLp z,?_,?_,hHigher⟩
  · rw [integral_norm_sq_eq_eLpNorm_two_toReal_sq (Lp.memLp z),← Lp.norm_def]
    exact pow_le_pow_left₀ (norm_nonneg _) hZ 2
  · exact weakCoordinatePartial_from_differenceLimit hv i (h0.comp hκ.tendsto_atTop)
      (fun k => hNe (κ k)) z hConv

/-- A uniform square bound also gives the actual weak derivative and
its square bound alone. -/
theorem exists_weakAmbientCoordinatePartial_of_differenceQuotient_bound
    {n q : ℕ} {U : Set (Domain n)}
    {v : Domain n → Ambient q} (hv : MemLp v 2 volume)
    (i : Fin n) {h : ℕ → ℝ} (h0 : Tendsto h atTop (𝓝 0)) (hNe : ∀ k, h k ≠ 0)
    {C : ℝ} (hC : 0 ≤ C)
    (hBound : ∀ k, (∫ x in U, ‖ambientDifferenceQuotient i (h k) v x‖^2) ≤ C^2) :
    ∃ D : Domain n → Ambient q, MemLp D 2 (volume.restrict U) ∧
      (∫ x in U, ‖D x‖^2) ≤ C^2 ∧ IsWeakAmbientCoordinatePartial U i v D := by
  obtain ⟨D,hD,hN,hWeak,_⟩ := exists_weakAmbientCoordinatePartial_of_differenceQuotient_bounds
    hv i h0 hNe hC hBound (p := 2) (by norm_num) (M := ⊤) (fun _ => le_top)
  exact ⟨D,hD,hN,hWeak⟩

end Thesis
