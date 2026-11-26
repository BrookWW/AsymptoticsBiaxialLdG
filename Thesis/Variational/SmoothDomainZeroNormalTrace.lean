module

public import Thesis.Variational.SmoothDomainTraceOperatorCore
public import Thesis.Variational.SmoothDomainNormalTrace
import Thesis.Variational.SmoothDomainSobolevDensity
public import HarmonicMaps.Analysis.SobolevDifference
import HarmonicMaps.Analysis.VariableMollificationL2

/-! A zero boundary class gives zero endpoints for the original normal traces
on every smooth epigraph chart. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set Topology
open scoped ContDiff ENNReal NNReal

namespace Thesis

variable {Ω : Set Point}

theorem nativeSobolevL2Point_sub (hΩ : IsOpen Ω)
    {u v : Point → Ambient 5} {D G : Point → HarmonicMaps.Gradient 3 5}
    (hu : MemW12 ⟨Ω,hΩ⟩ u D) (hv : MemW12 ⟨Ω,hΩ⟩ v G) :
    nativeSobolevL2Point hΩ (hu.sub hv) = nativeSobolevL2Point hΩ hu - nativeSobolevL2Point hΩ hv := by
  ext1 i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hu.2.1.toLp_sub hv.2.1
  · exact (hu.2.2 j).toLp_sub (hv.2.2 j)

theorem nativeSobolevL2Point_tendsto (hΩ : IsOpen Ω)
    {u : ℕ → Point → Ambient 5} {D : ℕ → Point → HarmonicMaps.Gradient 3 5}
    {v : Point → Ambient 5} {G : Point → HarmonicMaps.Gradient 3 5}
    (hu : ∀ n, MemW12 ⟨Ω,hΩ⟩ (u n) (D n)) (hv : MemW12 ⟨Ω,hΩ⟩ v G)
    (hU : Tendsto (fun n => eLpNorm (u n - v) 2 (volume.restrict Ω)) atTop (𝓝 0))
    (hD : ∀ j, Tendsto (fun n => eLpNorm (fun x => D n x j - G x j) 2 (volume.restrict Ω)) atTop (𝓝 0)) :
    Tendsto (fun n => nativeSobolevL2Point hΩ (hu n)) atTop (𝓝 (nativeSobolevL2Point hΩ hv)) := by
  apply ((PiLp.continuous_toLp 2 (fun _ : Fin 4 => Lp (Ambient 5) 2 (volume.restrict Ω))).tendsto _).comp
  apply tendsto_pi_nhds.mpr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' u (fun n => (hu n).2.1) v hv.2.1).2 hU
  · exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun n x => D n x j)
      (fun n => (hu n).2.2 j) (fun x => G x j) (hv.2.2 j)).2 (hD j)

private theorem integral_sq_wallBase_le_frontier
    (B : SmoothDomainEpigraphBox Ω) {f : Point → Ambient 5}
    (hF : MemLp (fun x : frontier Ω => f x) 2 (frontierSurfaceMeasure Ω)) :
    (∫ y in B.planeDomain.val, ‖f (B.normalParameter (y,0))‖ ^ 2) ≤
      (2 * (B.inverseLip : ℝ)) ^ 2 * ∫ x : frontier Ω, ‖f x‖ ^ 2 ∂frontierSurfaceMeasure Ω := by
  let σ := frontierSurfaceMeasure Ω
  let ν := Measure.map B.wallMap B.wallBaseMeasure
  let P := range B.wallMap
  let c := ((2 * B.inverseLip : ℝ≥0) : ℝ≥0∞)^2
  let g (x : frontier Ω) := ‖f x‖ ^ 2
  have hg : Integrable g σ := (memLp_two_iff_integrable_sq_norm hF.1).mp hF
  have hν : ν ≤ c • σ.restrict P := B.map_wallBase_le_surfaceMeasure
  have hPull :
      (∫ y in B.planeDomain.val, ‖f (B.normalParameter (y,0))‖ ^ 2) = ∫ x, g x ∂ν := by
    rw [B.measurableEmbedding_wallMap.integral_map]
    exact (B.wallBaseMeasure_coe.integral_comp (MeasurableEmbedding.subtype_coe B.planeDomain.property.measurableSet)
      (fun y : Plane => ‖f (B.normalParameter (y,0))‖ ^ 2)).symm
  rw [hPull]
  calc
    _ ≤ ∫ x, g x ∂(c • σ.restrict P) :=
      integral_mono_measure hν (Eventually.of_forall fun _ => sq_nonneg _)
        (hg.restrict.smul_measure (ENNReal.pow_ne_top ENNReal.coe_ne_top))
    _ = (2 * (B.inverseLip : ℝ)) ^ 2 * ∫ x in P, g x ∂σ := by
      rw [integral_smul_measure]
      simp only [c, ENNReal.toReal_pow, ENNReal.coe_toReal, NNReal.coe_mul, NNReal.coe_ofNat, smul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (integral_mono_measure Measure.restrict_le_self (Eventually.of_forall fun _ => sq_nonneg _) hg)
      (sq_nonneg _)

private theorem tendsto_norm_sq_zero_iff {E : Type*} [NormedAddCommGroup E] {u : ℕ → E} :
    Tendsto (fun n => ‖u n‖ ^ 2) atTop (𝓝 0) ↔ Tendsto u atTop (𝓝 0) := by
  constructor
  · intro h
    have hS := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp h
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hS
  · intro h
    simpa only [norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] using h.norm.pow 2

/-- For a bounded operator agreeing with restriction on smooth graphs, a
zero boundary class forces the actual lower endpoint of every normal-trace
curve to vanish. -/
theorem IsSmoothDomain.normalTrace_zero_of_boundaryExtension_zero
    (hΩ : IsSmoothDomain Ω) (T : SobolevL2Coordinates Ω →L[ℝ] SobolevTraceL2 Ω)
    (hT : ∀ {f : Point → Ambient 5} (hf : ContDiff ℝ ∞ f),
      T (nativeSobolevL2Point hΩ.1.1 (hΩ.memW12_of_smooth hf)) =
        (hΩ.memLp_continuous_frontier hf.continuous).toLp (fun x : frontier Ω => f x))
    {u : Point → Ambient 5} {D : Point → HarmonicMaps.Gradient 3 5}
    (hu : MemW12 ⟨Ω,hΩ.1.1⟩ u D) (hZero : T (nativeSobolevL2Point hΩ.1.1 hu) = 0)
    (B : SmoothDomainEpigraphBox Ω) {t : ℝ} (ht : 0 < t) (htR : t ≤ B.radius)
    (H : B.NormalTrace 5 t) (hH : B.RepresentsNormalTrace u H) :
    H ⟨0,le_rfl,ht.le⟩ = 0 := by
  obtain ⟨f,hf,hw,hFconv,hDconv⟩ := hΩ.exists_smooth_memW12_approximation hu
  let J (n : ℕ) := nativeSobolevL2Point hΩ.1.1 (hw n)
  let J₀ := nativeSobolevL2Point hΩ.1.1 hu
  let b (n : ℕ) := hΩ.memLp_continuous_frontier (hf n).continuous
  have hJ : Tendsto J atTop (𝓝 J₀) := nativeSobolevL2Point_tendsto hΩ.1.1 hw hu hFconv hDconv
  have hBconv : Tendsto (fun n => (b n).toLp (fun x : frontier Ω => f n x)) atTop (𝓝 0) := by
    have h := (T.continuous.tendsto J₀).comp hJ
    rw [show T J₀ = 0 from hZero] at h
    exact h.congr (fun n => hT (hf n))
  obtain ⟨C,hC,hN⟩ := B.exists_normalTrace_bound (q := 5) hΩ.1.1 ht htR
  choose Hn hRep _ using fun n => hN (hw n)
  let o : Icc (0 : ℝ) t := ⟨0,le_rfl,ht.le⟩
  have hBound (n : ℕ) :
      ‖Hn n o‖ ^ 2 ≤ (2 * (B.inverseLip : ℝ)) ^ 2 * ‖(b n).toLp (fun x : frontier Ω => f n x)‖ ^ 2 := by
    obtain ⟨hP,hEq⟩ := (hRep n).eq_raw_of_continuous (B := B) ht htR (hf n).continuous o
    rw [hEq, Lp.norm_toLp, Lp.norm_toLp, ← integral_norm_sq_eq_eLpNorm_two_toReal_sq hP,
      ← integral_norm_sq_eq_eLpNorm_two_toReal_sq (b n)]
    exact integral_sq_wallBase_le_frontier B (b n)
  have hHconv : Tendsto (fun n => Hn n o) atTop (𝓝 0) :=
    tendsto_norm_sq_zero_iff.mp (tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa only [mul_zero] using (tendsto_norm_sq_zero_iff.mpr hBconv).const_mul ((2 * (B.inverseLip : ℝ)) ^ 2))
      (fun _ => sq_nonneg _) hBound)
  have hDiffBound (n : ℕ) :
      ‖Hn n o - H o‖ ^ 2 ≤ C * ‖J n - J₀‖ ^ 2 := by
    obtain ⟨K,hK,hKB⟩ := hN ((hw n).sub hu)
    have hEq := (hK.unique (B := B) ht ((hRep n).sub (B := B) hH))
    rw [hEq] at hKB
    have h := hKB o
    rw [← nativeSobolevL2Point_norm_sq hΩ.1.1 ((hw n).sub hu),
      nativeSobolevL2Point_sub] at h
    exact h
  have hHlim : Tendsto (fun n => Hn n o - H o) atTop (𝓝 0) :=
    tendsto_norm_sq_zero_iff.mp (tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa only [mul_zero] using
        (tendsto_norm_sq_zero_iff.mpr (by simpa only [sub_self] using hJ.sub_const J₀)).const_mul C)
      (fun _ => sq_nonneg _) hDiffBound)
  have hEq := tendsto_nhds_unique (hHconv.sub_const (H o)) hHlim
  simpa only [zero_sub, neg_eq_zero] using hEq

end Thesis
