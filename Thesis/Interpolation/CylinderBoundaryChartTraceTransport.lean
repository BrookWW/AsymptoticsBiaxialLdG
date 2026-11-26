module

public import Thesis.Interpolation.CylinderBoundaryTrace
import Thesis.Interpolation.CylinderBoundaryMeasure
import Thesis.Interpolation.CylinderTraceStability
import Thesis.Interpolation.SobolevChartApproximation

/-! The sphere boundary class of a charted cylinder in its original physical face coordinates. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set StratificationTheory
open scoped ContDiff ENNReal NNReal Topology

namespace Thesis.MeasureGeometry

private theorem trace_limit_pullback_ae_eq {X Y E : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [NormedAddCommGroup E] {μ : Measure X} {ν : Measure Y} {θ : X → Y}
    (hθ : Measurable θ) {C : ℝ≥0∞} (hC : C ≠ ⊤) (hDom : Measure.map θ μ ≤ C • ν)
    {P : ℕ → Lp E 2 ν} {T : Lp E 2 ν} (hP : Tendsto P atTop (𝓝 T))
    {S : ℕ → Lp E 2 μ} {H : Lp E 2 μ} (hS : Tendsto S atTop (𝓝 H))
    (hAgree : ∀ k, (S k : X → E) =ᵐ[μ] (P k : Y → E) ∘ θ) :
    (H : X → E) =ᵐ[μ] (T : Y → E) ∘ θ := by
  let f : ℕ → X → E := fun k => (P k : Y → E) ∘ θ
  let g : X → E := (T : Y → E) ∘ θ
  have hf (k : ℕ) : MemLp (f k) 2 μ :=
    memLp_comp_of_map_le_smul hθ.aemeasurable hC hDom (Lp.memLp (P k))
  have hg : MemLp g 2 μ := memLp_comp_of_map_le_smul hθ.aemeasurable hC hDom (Lp.memLp T)
  have hConv : Tendsto (fun k => eLpNorm (f k - g) 2 μ) atTop (𝓝 0) := by
    have hRaw := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' P T).1 hP
    have h := tendsto_eLpNorm_comp_zero_of_map_le_smul
      (f := fun k => (P k : Y → E) - (T : Y → E))
      hθ.aemeasurable hC hDom
      (fun k => ((Lp.memLp (P k)).sub (Lp.memLp T)).aestronglyMeasurable) hRaw
    exact h
  have hLimit := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hf g hg).2 hConv
  have hEq (k : ℕ) : (hf k).toLp (f k) = S k :=
    Lp.ext ((hf k).coeFn_toLp.trans (hAgree k).symm)
  have hEnd : hg.toLp g = H := tendsto_nhds_unique (hLimit.congr hEq) hS
  exact hEnd ▸ hg.coeFn_toLp

private theorem terminal_face_trace_eq {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {q : ℕ} {R : ℝ} {F : Point ≃ₜ Point} {θ : X → UnitTensorSphere} {z : X → Point}
    (hθ : Measurable θ) {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hDom : Measure.map θ μ ≤ C • tensorSphereMeasure)
    (hRec : ∀ᵐ x ∂μ, F.symm (R • (θ x).val) = z x)
    {p : ℕ → Point → Ambient q} {g : Point → Ambient q}
    {P : ℕ → Lp (Ambient q) 2 tensorSphereMeasure} {T : Lp (Ambient q) 2 tensorSphereMeasure}
    (hPT : Tendsto P atTop (𝓝 T))
    (hPval : ∀ k, (P k : UnitTensorSphere → Ambient q) =ᵐ[tensorSphereMeasure]
      fun t => p k (R • t.val))
    (hTval : (T : UnitTensorSphere → Ambient q) =ᵐ[tensorSphereMeasure]
      fun t => g (F.symm (R • t.val)))
    {S : ℕ → Lp (Ambient q) 2 μ} {H : Lp (Ambient q) 2 μ} (hSH : Tendsto S atTop (𝓝 H))
    (hSval : ∀ k, (S k : X → Ambient q) =ᵐ[μ] fun x => p k (F (z x))) :
    (H : X → Ambient q) =ᵐ[μ] fun x => g (z x) := by
  have hQ : Measure.QuasiMeasurePreserving θ μ tensorSphereMeasure :=
    ⟨hθ, Measure.absolutelyContinuous_of_le_smul hDom⟩
  have hEq (k : ℕ) : (S k : X → Ambient q) =ᵐ[μ] (P k : UnitTensorSphere → Ambient q) ∘ θ := by
    filter_upwards [hSval k, hQ.ae_eq (hPval k), hRec] with x hF hP hr
    have hx := congrArg F hr
    rw [F.apply_symm_apply] at hx
    change S k x = P k (θ x)
    rw [hF, ← hx]
    exact hP.symm
  have hH := trace_limit_pullback_ae_eq hθ hC hDom hPT hSH hEq
  filter_upwards [hH, hQ.ae_eq hTval, hRec] with x h₁ h₂ h₃
  change T (θ x) = g (F.symm (R • (θ x).val)) at h₂
  change H x = T (θ x) at h₁
  rw [h₂, h₃] at h₁
  exact h₁

end Thesis.MeasureGeometry

namespace Thesis

open MeasureGeometry

/-- A native sphere trace under a bi-Lipschitz chart yields the original
horizontal and lateral L² traces of the same cylinder field and all
three prescribed terminal classes. -/
theorem cylinderBoundaryChartTraceTransport : External.CylinderBoundaryChartTraceTransport := by
  intro q B c R lo hi hR hI F hFLip hInv hU u Du hu g T hT hTVal
  let U := translatedAxisCylinderDomain B c R lo hi
  let a := R / 2
  let tR : Icc a R := ⟨R, half_le_self hR.le, le_rfl⟩
  have ha : 0 < a := half_pos hR
  have haR : a < R := half_lt_self hR
  obtain ⟨J, hJ, p, hp, hLip, hpW, hpMap, hpGrad, G, hG, hGMap, hGGrad⟩ :=
    exists_smooth_chart_graph_approximation F hFLip hInv U hR hU u Du hu
  choose P hP hPVal using fun k : ℕ =>
    exists_nativeSphereTrace_of_continuousOn_closedBall ha.le haR (hp k).continuous.continuousOn
  have hPT : Tendsto (fun k => P k tR) atTop (𝓝 (T tR)) :=
    nativeSphereTrace_tendsto_of_strong_graph ha haR hpW hJ hpMap hpGrad hP hT tR
  let v (k : ℕ) := p k ∘ F
  have hvLip (k : ℕ) : ∃ K : ℝ≥0, LipschitzWith K (v k) := by
    obtain ⟨K, hK⟩ := hLip k
    exact ⟨K * 20, hK.comp hFLip⟩
  choose Hn Sn hHn hSn hHnVal hSnVal using fun k : ℕ =>
    exists_cylinderBoundaryL2Traces_of_continuousOn_closed B c hR hI
      ((hp k).continuous.comp F.continuous).continuousOn
  obtain ⟨H, hH, _⟩ := exists_cylinderHeight_trace_with_estimate B c hI u Du hu
  obtain ⟨S, hS, hSconv⟩ := exists_cylinderSide_trace_of_strong_lipschitz_graph B c hR
    hG hu hvLip hGMap hGGrad Sn hSn
  have hDisk (t : Icc lo hi) (ht : t.val = lo ∨ t.val = hi) :
    (H t : Plane → Ambient q) =ᵐ[volume.restrict (ball (0 : Plane) R)]
      fun y => g (c + axisChart B (y, t.val)) := by
    let z (y : Plane) := c + axisChart B (y, t.val)
    let θ (y : Plane) := cylinderBoundaryDirection F (z y)
    obtain ⟨C, hC, hDom, hRec⟩ :=
      map_cylinder_disk_boundary_direction_le B c hR hI ht F hInv hU
    have hθ : Measurable θ := (measurable_cylinderBoundaryDirection F).comp
      ((continuous_const.add ((continuous_axisChart B).comp (continuous_id.prodMk continuous_const))).measurable)
    have hHconv := cylinderHeightTrace_tendsto_of_strong_graph B c hI
      hG hu hGMap hGGrad hHn hH t
    exact terminal_face_trace_eq (z := z) hθ hC hDom
      ((ae_restrict_mem measurableSet_ball).mono hRec) hPT
      (fun k => hPVal k tR) hTVal hHconv (fun k => hHnVal k t)
  refine ⟨H, S, hH, hS, hDisk ⟨lo, le_rfl, hI.le⟩ (Or.inl rfl),
    hDisk ⟨hi, hI.le, le_rfl⟩ (Or.inr rfl), ?_⟩
  let z (y : NativeCircle × ℝ) := c + axisChart B (R • y.1.val, y.2)
  let θ (y : NativeCircle × ℝ) := cylinderBoundaryDirection F (z y)
  obtain ⟨C, hC, hDom, hRec⟩ := map_cylinder_wall_boundary_direction_le B c hR hI F hInv hU
  have hz : Continuous z := by
    have h := show Continuous (fun y : NativeCircle × ℝ => (R • y.1.val, y.2)) by fun_prop
    exact continuous_const.add ((continuous_axisChart B).comp h)
  have hθ : Measurable θ := (measurable_cylinderBoundaryDirection F).comp hz.measurable
  have hSconv' : Tendsto (fun k => Sn k tR) atTop (𝓝 (S tR)) :=
    ((continuous_eval_const tR).tendsto S).comp hSconv
  exact terminal_face_trace_eq (z := z) hθ hC hDom
    ((ae_cylinderSideTraceMeasure_height_mem lo hi).mono hRec) hPT
    (fun k => hPVal k tR) hTVal hSconv' (fun k => hSnVal k tR)

end Thesis

end
