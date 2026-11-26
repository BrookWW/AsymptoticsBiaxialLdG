module

public import Thesis.Interpolation.ShellFamilyConnector
import Thesis.Variational.PenalizedGoodRadii
import StratificationTheory.Frozen.SphereSliceEnergy
import StratificationTheory.Foundation.PolarAETransport
import StratificationTheory.Foundation.AngularL2Membership

/-! One common comparison sphere for a vacuum weak limit and a penalized sequence. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set StratificationTheory
open scoped ENNReal Matrix.Norms.Frobenius Topology

namespace Thesis

/-- The radius selection retains the prescribed vacuum map and the actual
Sobolev traces for one further subsequence, with costs tending to zero. -/
theorem exists_goodRadius_annular_connectors (a : BulkCoefficients) (hProj : HasPenalizedProjectionLayer a)
    {Ω : Set Point} (hΩ : IsOpen Ω) (c : Point) {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hClosed : closedBall c R ⊆ Ω) (ε : ℕ → ElasticScale) (hε : Tendsto (fun k => (ε k : ℝ)) atTop (𝓝 0))
    (hSmall : ∀ k, (ε k : ℝ) < r) (u : ℕ → Point → S0) (D : ℕ → Point → Gradient)
    (v : Point → S0) (Dv : Point → Gradient)
    (hu : ∀ k, MemH1Loc Ω (u k) (D k)) (hv : MemH1Loc Ω v Dv) (hVac : TakesVacuumValues a Ω v)
    (M B : ℝ) (hM : 0 < M) (hB : 0 < B)
    (hNorm : ∀ k, ∀ᵐ x ∂volume.restrict (ball c R), ‖u k x‖ ≤ M)
    (hEnergy : ∀ k, energy a (ε k) (ball c R) (u k) (D k) ≤ ENNReal.ofReal B)
    (hStrong : Tendsto (fun k => eLpNorm (u k - v) 2 (volume.restrict (ball c R))) atTop (𝓝 0)) :
    ∃ (s : ℝ) (hs : s ∈ Ioo r R) (κ : ℕ → ℕ) (cost : ℕ → ℝ≥0∞),
      StrictMono κ ∧ Tendsto cost atTop (𝓝 0) ∧
      ∀ᶠ k in atTop, ∃ W : RadialAnnularConnector c s R hs.2 (u (κ k)) v,
        energy a (ε (κ k)) (radialAnnulus c W.radius s) W.toFun W.gradient ≤ cost k := by
  have hR : 0 < R := hr.trans hrR
  have hRV : CompactlyContained (ball c R) Ω := by
    unfold CompactlyContained
    rw [closure_ball c hR.ne']
    exact ⟨isCompact_closedBall _ _, hClosed⟩
  have hUB (k : ℕ) : MemH1 (ball c R) (u k) (D k) := hu k _ isOpen_ball hRV
  have hVB : MemH1 (ball c R) v Dv := hv _ isOpen_ball hRV
  have hTrace (k : ℕ) : ∃ H : RadialL2Trace r R, RepresentsRadialL2Trace c (u k) H :=
    (existsUnique_radialL2Trace_of_memH1Loc hΩ (hu k) c hr hrR hClosed).exists
  choose HU hHU using hTrace
  obtain ⟨HV, hHV, _⟩ := existsUnique_radialL2Trace_of_memH1Loc hΩ hv c (half_pos hr)
    (by linarith) hClosed
  have hσ : tensorSphereMeasure = (volume : Measure Point).toSphere :=
    euclideanHausdorffMeasure_unitSphere_eq_toSphere (by decide : 0 < 3)
  let U (k : ℕ) (s : ℝ) (θ : UnitTensorSphere) := u k (c + s • θ.val)
  let V (s : ℝ) (θ : UnitTensorSphere) := v (c + s • θ.val)
  let P (s : ℝ) : Prop :=
    (∀ k, ∃ hU : MemSphereH1 (U k s),
      (∀ᵐ θ ∂tensorSphereMeasure, ‖U k s θ‖ ≤ M) ∧
        ∀ δ : ElasticScale, (δ : ℝ) = (ε k : ℝ) / s →
          spherePenalizedEnergy a δ (U k s) hU ≤
            polarIntegralDensity c (fun x => energyDensity a (ε k) (u k x) (D k x)) s) ∧
    (MemSphereH1 (V s) ∧ ∀ᵐ θ ∂tensorSphereMeasure, V s θ ∈ vacuum a) ∧
    (∀ hsn : s ∈ Ioo r R, ∀ k, ∃ hU : MemLp (fun θ => frobeniusCoordinateEquiv (U k s θ)) 2 tensorSphereMeasure,
      HU k ⟨s, hsn.1.le, hsn.2.le⟩ = hU.toLp _) ∧
    (∀ hsn : s ∈ Ioo (r / 2) R, ∃ hV : MemLp (fun θ => frobeniusCoordinateEquiv (V s θ)) 2 tensorSphereMeasure,
      HV ⟨s, hsn.1.le, hsn.2.le⟩ = hV.toLp _)
  have hSub : Ioo r R ⊆ Ioo 0 R := fun _ hv => ⟨hr.trans hv.1, hv.2⟩
  have hUSlice := ae_all_iff.2 fun k => ae_restrict_of_ae_restrict_of_subset hSub
    (ae_scaled_spherePenalizedEnergy_le_coarea a (ε k) hΩ c hR hClosed (hu k) M (hNorm k))
  have hvNative := (memH1Loc_iff_memW12Loc ⟨Ω, hΩ⟩ v Dv).1 hv
  have hVSl := ae_restrict_of_ae_restrict_of_subset hSub
    (ae_sphereSobolev_and_gradientEnergy (by decide : 2 ≤ 3) hvNative hR hClosed)
  have hVacSl := ae_restrict_of_ae_restrict_of_subset hSub (ae_polar_slice_of_ae_ball
    (ae_restrict_of_ae_restrict_of_subset (ball_subset_closedBall.trans hClosed) hVac))
  have hAllTrace := (ae_all_iff.2 hHU).filter_mono (ae_mono (Measure.restrict_le_self (s := Ioo r R)))
  have hP : ∀ᵐ s ∂volume.restrict (Ioo r R), P s := by
    filter_upwards [hUSlice, hVSl, hVacSl, hAllTrace, hHV.filter_mono (ae_mono Measure.restrict_le_self)] with
      s hUs hVs hVacs hUT hVT
    refine ⟨hUs, ⟨hVs.choose, ?_⟩, ?_, hVT⟩
    · rwa [hσ]
    · intro hs k
      exact hUT k hs
  obtain ⟨s, hs, hsP, _, κ, hκ, hE, hL2⟩ := exists_good_polar_radius_of_penalized_energy_and_strongL2
    a ε c hr hrR hB u D v hUB hVB.1 hEnergy hStrong P hP
  obtain ⟨hUS, ⟨hVS, hVVac⟩, hUT, hVT⟩ := hsP
  choose hU hUbound hUE using hUS
  have hs₀ : 0 < s := hr.trans hs.1
  let δ (k : ℕ) : ElasticScale := ⟨(ε (κ k) : ℝ) / s, div_pos (ε (κ k)).property.1 hs₀,
    (div_lt_one hs₀).2 ((hSmall (κ k)).trans hs.1)⟩
  let A := 4 * B / (R - r)
  have hA : 0 < A := div_pos (by positivity) (sub_pos.2 hrR)
  have hBound (k : ℕ) : spherePenalizedEnergy a (δ k) (U (κ k) s) (hU (κ k)) ≤ A :=
    (hUE (κ k) (δ k) rfl).trans (hE k)
  have hHalf : r / 2 ≤ s / 2 := by linarith [hs.1]
  let H := restrict_radialL2Trace HV hHalf hs.2.le
  have hH := hHV.restrict hHalf hs.2.le
  let L (k : ℕ) := restrict_radialL2Trace (HU (κ k)) hs.1.le (show (s + R) / 2 ≤ R by linarith [hs.2])
  have hL (k : ℕ) := (hHU (κ k)).restrict hs.1.le (show (s + R) / 2 ≤ R by linarith [hs.2])
  have hHend : H ⟨s, by linarith, le_rfl⟩ = hVS.1.toLp (fun θ => frobeniusCoordinateEquiv (V s θ)) := by
    obtain ⟨hLp, hEq⟩ := hVT ⟨by linarith [hs.1], hs.2⟩
    exact hEq
  have hLend (k : ℕ) : L k ⟨s, le_rfl, by linarith [hs.2]⟩ = (hU (κ k)).1.toLp
      (fun θ => frobeniusCoordinateEquiv (U (κ k) s θ)) := by
    obtain ⟨hLp, hEq⟩ := hUT hs (κ k)
    exact hEq
  have hL2' : Tendsto (fun k => sphereL2DifferenceSq (U (κ k) s) (V s)) atTop (𝓝 0) := by
    simpa only [sphereL2DifferenceSq, U, V, hσ] using hL2
  obtain ⟨cost, hCost, hShell⟩ := exists_annular_connectors_of_common_sphere_data a hProj c hs₀ hs.2
    (ε ∘ κ) δ (hε.comp hκ.tendsto_atTop) (fun _ => rfl) (u ∘ κ) v (fun k => hU (κ k)) hVS
    M A hM hA (fun k => hUbound (κ k)) hVVac hBound hL2' H hH hHend L hL hLend
  exact ⟨s, hs, κ, cost, hκ, hCost, hShell⟩

end Thesis
