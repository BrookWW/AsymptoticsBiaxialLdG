module

public import Thesis.MeasureGeometry.WeightedSegmentNetwork
public import Thesis.MeasureGeometry.SegmentNetworkStationarity
public import Thesis.MeasureGeometry.JunctionNativeParity
public import Thesis.MeasureGeometry.MeridianTrace
import Thesis.Foundation.WeakGradient

/-! The frozen finite-network conclusions on the same logarithmic limit. -/

public section

noncomputable section

open Filter MeasureTheory Metric Set
open scoped ContDiff ENNReal Matrix.Norms.Frobenius Topology

namespace Thesis.MeasureGeometry

/-- Meridians of actual transverse disks detect the weight of their unique open edge. -/
@[expose] def SegmentMeridianCosts (a : BulkCoefficients) (K S Spt : Set Point)
    (Q₀ : Point → S0) {m : ℕ} (p q : Fin m → Point) (θ : Fin m → ℝ) : Prop :=
  ∀ (i : Fin m) (d : Plane → Point), IsSmoothDiskEmbedding d → d '' Disk ⊆ K →
    ∀ y ∈ ball (0 : Plane) 1, d '' Disk ∩ S = {d y} →
      d y ∈ openSegment ℝ (p i) (q i) →
      q i - p i ∉ LinearMap.range (fderiv ℝ d y).toLinearMap →
      Disjoint (d '' sphere (0 : Plane) 1) Spt →
      ∀ b : C(NativeCircle, vacuum a), (∀ z, (b z).val = Q₀ (d z.val)) →
        θ i = nativeVacuumCircleCost a b

/-- The local network clause with the literal conditions of Theorem 1.6. -/
@[expose] def LogarithmicSegmentNetworkConclusion (a : BulkCoefficients) (Ω : Set Point)
    (μ : Measure Point) (S : Set Point) (Q₀ : Point → S0) : Prop :=
  let Spts := singularSet (Ω \ S) Q₀
  ∀ K : Set Point, IsOpen K → CompactlyContained K Ω →
    ∃ (U : Set Point) (m : ℕ) (p q : Fin m → Point) (θ : Fin m → ℝ),
      let L := fun i : Fin m => segment ℝ (p i) (q i)
      let κ := kappaStar a
      IsOpen U ∧ closure K ⊆ U ∧ CompactlyContained U Ω ∧
      (∀ i, p i ≠ q i ∧ (θ i = κ ∨ θ i = 2*κ)) ∧
      S ∩ closure U = ⋃ i, L i ∧
      S ∩ closure K = ⋃ i, L i ∩ closure K ∧
      (∀ i j, i ≠ j → ∀ x ∈ L i ∩ L j,
        (x = p i ∨ x = q i) ∧ (x = p j ∨ x = q j)) ∧
      μ.restrict (closure K) =
        ∑ i, ENNReal.ofReal (θ i) • HausdorffOne.restrict (L i ∩ closure K) ∧
      (∀ d : Plane → Point, IsSmoothDiskEmbedding d → d '' Disk ⊆ K →
        ∀ y ∈ Metric.ball (0 : Plane) 1, d '' Disk ∩ S = {d y} →
          (∃ i, d y ∈ openSegment ℝ (p i) (q i) ∧
            q i - p i ∉ LinearMap.range (fderiv ℝ d y).toLinearMap) →
          Disjoint (d '' Metric.sphere (0 : Plane) 1) Spts →
          (∀ z ∈ Metric.sphere (0 : Plane) 1, Q₀ (d z) ∈ vacuum a) ∧
          ¬HasMeridianFilling a d Q₀) ∧
      ∀ x ∈ K,
        let I := incidentSegments p q x
        let v := outwardDirection p q x
        I.Nonempty →
          2 ≤ I.card ∧ (∑ i : ↥I, θ i • v i) = 0 ∧
          Even ((Finset.univ.filter fun i : ↥I => θ i = κ).card) ∧
          (I.card = 2 → ∀ i j : ↥I, i ≠ j → v i = -v j) ∧
          (I.card = 3 →
            (∀ i : ↥I, θ i = 2*κ) ∧
            (∃ P : Submodule ℝ Point, Module.finrank ℝ P = 2 ∧ ∀ i : ↥I, v i ∈ P) ∧
            ∀ i j : ↥I, i ≠ j → InnerProductGeometry.angle (v i) (v j) = 2*Real.pi/3)

theorem logarithmicSegmentNetwork_of_quantized_and_meridianCosts
    (hAA : External.AllardAlmgrenLocalStructure)
    (a : BulkCoefficients) {Ω : Set Point} (hΩ : IsOpen Ω) (μ : FiniteMeasure Point)
    (V : Measure (Point × LineProjection))
    (hAssoc : IsAssociatedVarifold Ω (Ω ∩ (μ : Measure Point).support) μ V)
    (hStat : IsStationaryVarifold Ω V)
    (hDensity : ∃ c > (0 : ℝ), ∀ x ∈ Ω ∩ (μ : Measure Point).support,
      ∃ θ ≥ c, Tendsto (oneDensity μ x) (𝓝[>] 0) (𝓝 θ))
    (hQuant : DensityQuantized a μ (Ω ∩ (μ : Measure Point).support))
    (Q₀ : Point → S0)
    (hVac : TakesVacuumValues a (Ω \ (μ : Measure Point).support) Q₀)
    (hLoc : LocallyFiniteIn (Ω \ (μ : Measure Point).support) (singularSet (Ω \ (μ : Measure Point).support) Q₀))
    (hSmooth : ContDiffOn ℝ ∞ Q₀
      ((Ω \ (μ : Measure Point).support) \ singularSet (Ω \ (μ : Measure Point).support) Q₀))
    (hMeridian : ∀ {K U : Set Point}, IsOpen K → K ⊆ U → CompactlyContained U Ω →
      ∀ {m : ℕ} (p q : Fin m → Point) (θ : Fin m → ℝ),
      (∀ i, p i ≠ q i ∧ (θ i = kappaStar a ∨ θ i = 2 * kappaStar a)) →
      (μ : Measure Point).support ∩ closure U = ⋃ i, segment ℝ (p i) (q i) →
      (∀ i j, i ≠ j → ∀ x ∈ segment ℝ (p i) (q i) ∩ segment ℝ (p j) (q j),
        (x = p i ∨ x = q i) ∧ (x = p j ∨ x = q j)) →
      (μ : Measure Point).restrict (closure K) =
        ∑ i, ENNReal.ofReal (θ i) • HausdorffOne.restrict (segment ℝ (p i) (q i) ∩ closure K) →
      SegmentMeridianCosts a K (μ : Measure Point).support
        (singularSet (Ω \ (μ : Measure Point).support) Q₀) Q₀ p q θ) :
    LogarithmicSegmentNetworkConclusion a Ω μ (μ : Measure Point).support Q₀ := by
  unfold LogarithmicSegmentNetworkConclusion
  intro Spts K hK hKΩ
  let S := (μ : Measure Point).support
  have hS : IsClosed S := (μ : Measure Point).isClosed_support
  have hPts : Spts ⊆ Ω \ S := fun _ hx => hx.1
  have hR : IsOpen ((Ω \ S) \ Spts) := isOpen_diff_singularSet Q₀
  obtain ⟨U, m, p, q, θ, hU, hKU, hUΩ, hθ, hCarrier, hKCarrier, hInt, hEach, hRepU, hRepK⟩ :=
    exists_weightedSegmentNetwork_of_rayPatches hKΩ
      (fun _ hx => exists_straightRayPatch hAA a hΩ μ V hAssoc hStat hDensity hQuant hx)
  have hKU' := subset_closure.trans hKU
  have hKΩ' := subset_closure.trans hKΩ.2
  have hn : ∀ i, p i ≠ q i := fun i => (hθ i).1
  have hθpos (i : Fin m) : 0 < θ i := by
    rcases (hθ i).2 with hi | hi <;> rw [hi] <;> linarith only [kappaStar_pos a]
  have hWeight := hMeridian hK hKU' hUΩ p q θ hθ hCarrier hInt hRepK
  refine ⟨U, m, p, q, θ, hU, hKU, hUΩ, hθ, hCarrier, hKCarrier, hInt, hRepK, ?_, ?_⟩
  · intro d hd hdK y hy hMeet hCross hDisjoint
    obtain ⟨i, hEdge, hTransverse⟩ := hCross
    obtain ⟨b, hb⟩ := exists_vacuumMeridianTrace a hVac hSmooth d hd (hdK.trans hKΩ') hy hMeet hDisjoint
    have hCost := hWeight i d hd hdK y hy hMeet hEdge hTransverse hDisjoint b hb
    have hPos : 0 < nativeVacuumCircleCost a b := hCost ▸ hθpos i
    refine ⟨?_, not_hasMeridianFilling_of_positive_cost a b hb hPos⟩
    intro z hz
    let z' : NativeCircle := ⟨z, hz⟩
    exact hb z' ▸ (b z').property
  · intro x hx I v hI
    have hFlux := sum_segment_endpointFlux_eq_zero hUΩ.2 hCarrier hn hEach hRepU hAssoc hStat
    have hBal := incident_balance_of_endpointFlux hU hn (fun i => (hθpos i).le) hFlux (hKU' hx)
    have hEven := even_incident_light_weights_of_meridian_cost_stereographic a hΩ hS hK hKU' hKΩ'
      hPts hLoc hR hSmooth.continuousOn hVac p q θ hn hθpos hCarrier hInt hWeight hx hI
    exact balanced_incident_geometry I hI (kappaStar_pos a) v (fun i => θ i)
      (norm_outwardDirection hn) (outwardDirection_injective_of_endpoint_intersections hn hInt)
      (fun i => (hθ i).2) hBal hEven

end Thesis.MeasureGeometry
