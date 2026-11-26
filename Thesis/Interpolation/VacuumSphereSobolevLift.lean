module

public import Thesis.Interpolation.QuaternionSphereCompactness
import StratificationTheory.Foundation.SphereAEClasses

/-! Sobolev lifting of the actual vacuum data on the two-sphere. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set StratificationTheory
open scoped ContDiff ENNReal NNReal Matrix.Norms.Frobenius Topology

namespace Thesis

/-- Smooth density on the two-dimensional source sphere, in the native
vacuum Sobolev coordinates. The strong density result gives the displayed
map convergence and convergence of the tangential Dirichlet energies. -/
@[expose] def External.SmoothVacuumSphereDensity (a : BulkCoefficients) : Prop :=
  ∀ (base : UnitBoundarySphere 3) (Q : UnitBoundarySphere 3 → vacuum a)
    (hQ : MemSphereW12 (by decide : 2 ≤ 3) (fun θ => frobeniusCoordinateEquiv (Q θ).val)),
    ∃ (Qj : ℕ → C(UnitBoundarySphere 3, vacuum a))
      (hj : ∀ k, MemSphereW12 (by decide : 2 ≤ 3) (fun θ => frobeniusCoordinateEquiv (Qj k θ).val)),
      (∀ k, ContDiffOn ℝ ∞ (fun x : Domain 3 => (Qj k (sphereRadialDirection base x)).val)
        ({0}ᶜ : Set (Domain 3))) ∧
      Tendsto (fun k => eLpNorm (fun θ => frobeniusCoordinateEquiv (Qj k θ).val -
        frobeniusCoordinateEquiv (Q θ).val) 2 (unitBoundarySurface 3)) atTop (𝓝 0) ∧
      Tendsto (fun k => vacuumSphereGradientEnergy (by decide : 2 ≤ 3) (Qj k) (hj k))
        atTop (𝓝 (vacuumSphereGradientEnergy (by decide : 2 ≤ 3) Q hQ))

/-- The lift retains the same actual vacuum field almost everywhere and the
tangential derivative bound of the smooth covering maps. -/
theorem exists_quaternionSobolevLift_of_vacuumSphere (a : BulkCoefficients)
    (hDense : External.SmoothVacuumSphereDensity a) (base : UnitBoundarySphere 3)
    (Q : UnitBoundarySphere 3 → vacuum a)
    (hQ : MemSphereW12 (by decide : 2 ≤ 3) (fun θ => frobeniusCoordinateEquiv (Q θ).val)) :
    ∃ (v : UnitBoundarySphere 3 → Sphere3)
      (hv : MemSphereW12 (by decide : 2 ≤ 3) (fun θ => (v θ).val)),
      (∀ᵐ θ ∂unitBoundarySurface 3, cover a (v θ) = (Q θ).val) ∧
      8 * vacuumRadius a ^ 2 * quaternionBoundaryEnergy (by decide : 2 ≤ 3) (fun θ => (v θ).val) hv ≤
        vacuumSphereGradientEnergy (by decide : 2 ≤ 3) Q hQ := by
  classical
  obtain ⟨Qj, hj, hjSmooth, hjL, hjE⟩ := hDense base Q hQ
  have hJ (k : ℕ) := exists_quaternionSobolevLift_of_smooth_vacuumSphere a base (Qj k) (hjSmooth k)
  choose v hv _ hCover hE using hJ
  let B := 8 * vacuumRadius a ^ 2
  have hB : 0 < B := by dsimp only [B]; positivity [vacuumRadius_pos a]
  let E := vacuumSphereGradientEnergy (by decide : 2 ≤ 3) Q hQ
  have hE₀ : 0 ≤ E := by
    dsimp only [E, vacuumSphereGradientEnergy]
    exact integral_nonneg fun θ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hTail : ∀ᶠ k in atTop, vacuumSphereGradientEnergy (by decide : 2 ≤ 3) (Qj k) (hj k) < E + 1 :=
    hjE.eventually (Iio_mem_nhds (lt_add_one E))
  obtain ⟨N, hN⟩ := eventually_atTop.1 hTail
  let η (k : ℕ) := N + k
  have hη : StrictMono η := fun i j hij => Nat.add_lt_add_left hij N
  let C : ℝ≥0 := ⟨(E + 1) / B, div_nonneg (by linarith) hB.le⟩
  have hCe (k : ℕ) : quaternionBoundaryEnergy (by decide : 2 ≤ 3) (fun θ => (v (η k) θ).val)
      (hv (η k)) ≤ C := by
    have h := hE (η k)
    change quaternionBoundaryEnergy (by decide : 2 ≤ 3) (fun θ => (v (η k) θ).val) (hv (η k)) ≤
      (E + 1) / B
    apply (le_div_iff₀ hB).2
    rw [mul_comm]
    exact h.trans (hN (η k) (Nat.le_add_right _ _)).le
  have hCunit (k : ℕ) : ∀ᵐ θ ∂unitBoundarySurface 3, ‖(v (η k) θ).val‖ = 1 :=
    ae_of_all _ fun θ => mem_sphere_zero_iff_norm.1 (v (η k) θ).property
  obtain ⟨κ, z, hz, hκ, hzUnit, hvConv, hLim⟩ :=
    exists_quaternionSphere_Sobolev_subsequence base (fun k θ => (v (η k) θ).val)
      (fun k => hv (η k)) hCunit C hCe
  let ι := η ∘ κ
  have hι : StrictMono ι := hη.comp hκ
  let l (θ : UnitBoundarySphere 3) : Sphere3 :=
    if h : z θ ∈ sphere (0 : QuaternionCoordinates) 1 then ⟨z θ, h⟩ else v (ι 0) θ
  have hlJ : z =ᵐ[unitBoundarySurface 3] fun θ => (l θ).val := by
    filter_upwards [hzUnit] with θ hθ
    dsimp only [l]
    rw [dif_pos (mem_sphere_zero_iff_norm.2 hθ)]
  have hl : MemSphereW12 (by decide : 2 ≤ 3) (fun θ => (l θ).val) := memSphereW12_congr_ae
    (by decide : 2 ≤ 3) hz hlJ
  have hlE : quaternionBoundaryEnergy (by decide : 2 ≤ 3) (fun θ => (l θ).val) hl =
      quaternionBoundaryEnergy (by decide : 2 ≤ 3) z hz := by
    have hEq := (sphereGradient_characterization (by decide : 2 ≤ 3) z hz).2.2
      (fun θ => (l θ).val) hl hlJ
    simp only [quaternionBoundaryEnergy, hEq]
  refine ⟨l, hl, ?_, ?_⟩
  · let F (x : Ambient 4) := frobeniusCoordinateEquiv (ambientQuaternionCover a x)
    have hF : Continuous F := (frobeniusCoordinateEquiv.continuous).comp (contDiff_ambientQuaternionCover a).continuous
    have hF₀ (w : Sphere3) : F w.val = frobeniusCoordinateEquiv (cover a w) := by
      simp only [F, ambientQuaternionCover, cover]
    have hLQ := hjL.comp hι.tendsto_atTop
    have hIM := tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (fun k => (hv (ι k)).1.aestronglyMeasurable) hz.1.aestronglyMeasurable hvConv
    obtain ⟨s, hs, hsv⟩ := hIM.exists_seq_tendsto_ae
    have hIQ := tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (fun k => (hj (ι (s k))).1.aestronglyMeasurable) hQ.1.aestronglyMeasurable
      (hLQ.comp hs.tendsto_atTop)
    obtain ⟨t, ht, htQ⟩ := hIQ.exists_seq_tendsto_ae
    filter_upwards [hsv, htQ, hlJ] with θ hθv hθQ hθl
    have hFc := hF.continuousAt.tendsto.comp (hθv.comp ht.tendsto_atTop)
    have hFc' : Tendsto (fun k => frobeniusCoordinateEquiv (Qj (ι (s (t k))) θ).val)
        atTop (𝓝 (F (z θ))) := by
      apply hFc.congr
      intro k
      exact (hF₀ (v (ι (s (t k))) θ)).trans (congrArg frobeniusCoordinateEquiv (hCover _ θ))
    have htEq := tendsto_nhds_unique hFc' hθQ
    rw [hθl, hF₀] at htEq
    exact frobeniusCoordinateEquiv.injective htEq
  · rw [hlE]
    change B * quaternionBoundaryEnergy (by decide : 2 ≤ 3) z hz ≤ E
    rw [mul_comm B]
    apply (le_div_iff₀ hB).1
    have hCmp (k : ℕ) : ENNReal.ofReal (quaternionBoundaryEnergy (by decide : 2 ≤ 3)
        (fun θ => (v (ι k) θ).val) (hv (ι k))) ≤
        ENNReal.ofReal (vacuumSphereGradientEnergy (by decide : 2 ≤ 3) (Qj (ι k)) (hj (ι k)) / B) := by
      apply ENNReal.ofReal_le_ofReal
      apply (le_div_iff₀ hB).2
      rw [mul_comm]
      exact hE (ι k)
    have hT : Tendsto (fun k => ENNReal.ofReal
        (vacuumSphereGradientEnergy (by decide : 2 ≤ 3) (Qj (ι k)) (hj (ι k)) / B))
        atTop (𝓝 (ENNReal.ofReal (E / B))) :=
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp ((hjE.comp hι.tendsto_atTop).div_const B)
    have hBound := liminf_le_liminf (f := (atTop : Filter ℕ)) (Eventually.of_forall hCmp)
    rw [hT.liminf_eq] at hBound
    exact (ENNReal.ofReal_le_ofReal_iff (div_nonneg hE₀ hB.le)).1 (hLim.trans hBound)

end Thesis
