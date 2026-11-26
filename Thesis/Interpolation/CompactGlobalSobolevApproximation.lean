module

public import Thesis.MeasureGeometry.PlanarSobolevApproximation
import HarmonicMaps.Analysis.SobolevMollificationGradient

/-! Compactly supported smooth approximation of a global weak graph. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set
open scoped ContDiff ENNReal Topology

namespace Thesis

private theorem integrable_of_memLp_two_support_compact {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    {F : Domain n → E} (hF : MemLp F 2 volume) {K : Set (Domain n)} (hK : IsCompact K)
    (hSup : Function.support F ⊆ K) : Integrable F volume := by
  letI : IsFiniteMeasure ((volume : Measure (Domain n)).restrict K) :=
    isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  apply (integrableOn_iff_integrable_of_support_subset hSup).mp
  exact (hF.mono_measure Measure.restrict_le_self).integrable (by norm_num)

private theorem tsupport_globalMollification_subset {n q : ℕ}
    (v : Domain n → Ambient q) (hV : IntegrableOn v (univ : Set (Domain n)))
    {K : Set (Domain n)} (hSupport : Function.support v ⊆ K)
    (ρ : ℝ) (h : PositiveRadius) (hρ : h.val ≤ ρ) :
    tsupport (euclideanMollification ⟨univ, isOpen_univ⟩ v hV h) ⊆ cthickening ρ K := by
  apply closure_minimal _ isClosed_cthickening
  intro x hx
  by_contra hn
  apply hx
  rw [euclideanMollification_eq_sampling_integral ⟨univ, isOpen_univ⟩ v hV h x (subset_univ _)]
  calc
    _ = ∫ y in ball (0 : Domain n) 1, (0 : Ambient q) := by
      apply setIntegral_congr_fun measurableSet_ball
      intro y hy
      have hDist : dist x (x - h.val • y) ≤ ρ := by
        rw [dist_eq_norm, sub_sub_cancel, norm_smul, Real.norm_of_nonneg h.property.le]
        have hyN := mem_ball_zero_iff.mp hy
        exact (mul_le_of_le_one_right h.property.le hyN.le).trans hρ
      have hNo : x - h.val • y ∉ K := fun hyK =>
        hn (closedBall_subset_cthickening hyK ρ (mem_closedBall.mpr hDist))
      have hZero : v (x - h.val • y) = 0 := by
        by_contra hn
        exact hNo (hSupport hn)
      change fixedMollifierKernel n y • v (x - h.val • y) = 0
      rw [hZero, smul_zero]
    _ = _ := integral_zero _ _

/-- A global weak graph supported in a compact subset of an open set has
smooth approximants compactly supported in that open set. -/
theorem exists_compact_global_sobolev_approximation {n q : ℕ}
    (U : OpenDomain n) {w : Domain n → Ambient q} {D : Domain n → HarmonicMaps.Gradient n q}
    (hw : MemW12 (⟨univ, isOpen_univ⟩ : OpenDomain n) w D)
    (K : Set (Domain n)) (hK : IsCompact K) (hKU : K ⊆ U.val)
    (hW : Function.support w ⊆ K) (hD : ∀ j : Fin n, Function.support (fun x => D x j) ⊆ K)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ f : Domain n → Ambient q, ∃ hf : ContDiff ℝ ∞ f,
      HasCompactSupport f ∧ tsupport f ⊆ U.val ∧ eLpNorm (f - w) 2 (volume.restrict U.val) < ε ∧
      ∀ j : Fin n, eLpNorm (fun x => coordinateDerivative f hf j x - D x j) 2 (volume.restrict U.val) < ε := by
  let Ω : OpenDomain n := ⟨univ, isOpen_univ⟩
  have hWI : IntegrableOn w Ω.val := by
    simpa only [Ω, Measure.restrict_univ, IntegrableOn] using
      integrable_of_memLp_two_support_compact (by simpa only [Measure.restrict_univ] using hw.2.1) hK hW
  have hDI (j : Fin n) : IntegrableOn (fun x => D x j) Ω.val := by
    simpa only [Ω, Measure.restrict_univ, IntegrableOn] using
      integrable_of_memLp_two_support_compact (by simpa only [Measure.restrict_univ] using hw.2.2 j) hK (hD j)
  obtain ⟨ρ, hρ, hρU⟩ := hK.exists_cthickening_subset_open U.property hKU
  let s (k : ℕ) : PositiveRadius := ⟨ρ / ((k : ℝ) + 1), div_pos hρ (by positivity)⟩
  have hs (k : ℕ) : (s k).val ≤ ρ := by
    change ρ / ((k : ℝ) + 1) ≤ ρ
    exact div_le_self hρ.le (by linarith only [show (0 : ℝ) ≤ k from Nat.cast_nonneg k])
  have hsLimit : Tendsto s atTop (comap (fun t : PositiveRadius => t.val) (𝓝 (0 : ℝ))) := by
    apply tendsto_comap_iff.mpr
    change Tendsto (fun k : ℕ => ρ / ((k : ℝ) + 1)) atTop (𝓝 0)
    simpa [div_eq_mul_inv] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul ρ
  let f (k : ℕ) := euclideanMollification Ω w hWI (s k)
  have hf (k : ℕ) : ContDiff ℝ ∞ (f k) := euclideanMollification_contDiff Ω w hWI (s k)
  have hClass (k : ℕ) (j : Fin n) (x : Domain n) :
      coordinateDerivative (f k) (hf k) j x = euclideanMollification Ω (fun y => D y j) (hDI j) (s k) x := by
    exact hw.1.kernelConvolution_coordinateDerivative hWI (scaledMollifierKernel_contDiff n (s k))
      (scaledMollifierKernel_hasCompactSupport n (s k)) x (fun _ _ => mem_univ _) j
  have hMap := (tendsto_eLpNorm_euclideanMollification_sub Ω w hWI hw.2.1 U.property.measurableSet
    (subset_univ _)).comp hsLimit
  have hCol (j : Fin n) := (tendsto_eLpNorm_euclideanMollification_sub Ω (fun x => D x j) (hDI j)
    (hw.2.2 j) U.property.measurableSet (subset_univ _)).comp hsLimit
  have hAll : ∀ᶠ k in atTop, ∀ j : Fin n, eLpNorm
      (fun x => euclideanMollification Ω (fun y => D y j) (hDI j) (s k) x - D x j) 2
      (volume.restrict U.val) < ε := Filter.eventually_all.2 fun j => (hCol j).eventually_lt_const hε
  obtain ⟨k, hk, hkCols⟩ := ((hMap.eventually_lt_const hε).and hAll).exists
  have hSupp : tsupport (f k) ⊆ cthickening ρ K :=
    tsupport_globalMollification_subset w hWI hW ρ (s k) (hs k)
  refine ⟨f k, hf k, (hK.cthickening (r := ρ)).of_isClosed_subset isClosed_closure hSupp,
    hSupp.trans hρU, hk, ?_⟩
  intro j
  simp_rw [hClass k j]
  exact hkCols j

end Thesis

end
