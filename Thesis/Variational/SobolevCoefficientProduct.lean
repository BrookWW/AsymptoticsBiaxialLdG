module

public import Thesis.Variational.H10SobolevEmbedding
import Thesis.Variational.H10StrongApproximation
import Thesis.Upstream.Rellich
import HarmonicMaps.Analysis.SobolevL2Closure
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-! Bounded operator coefficients with first derivatives in L³ act on the
actual zero-trace H¹ graph by the weak product rule. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Set Topology
open scoped ContDiff ENNReal NNReal Matrix.Norms.Frobenius

namespace Thesis

local instance coefficientProductTensorENorm : ContinuousENorm S0 :=
  @SeminormedAddGroup.toContinuousENorm S0 inferInstance

local instance coefficientProductTensorENormed : ENormedAddMonoid S0 :=
  NormedAddGroup.toENormedAddMonoid

local instance coefficientProductOperatorNormed : NormedAddCommGroup (S0 →L[ℝ] S0) :=
  ContinuousLinearMap.toNormedAddCommGroup (σ₁₂ := RingHom.id ℝ)

local instance coefficientProductOperatorSpace : NormedSpace ℝ (S0 →L[ℝ] S0) :=
  ContinuousLinearMap.toNormedSpace (σ₁₂ := RingHom.id ℝ)

theorem ennreal_holderTriple_three_six_two : ENNReal.HolderTriple 3 6 2 := by
  constructor
  change (3 : ℝ≥0∞)⁻¹ + (6 : ℝ≥0∞)⁻¹ = (2 : ℝ≥0∞)⁻¹
  rw [show (3 : ℝ≥0∞) = ENNReal.ofReal 3 by norm_num,
    show (6 : ℝ≥0∞) = ENNReal.ofReal 6 by norm_num,
    show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num]
  rw [← ENNReal.ofReal_inv_of_pos (by norm_num : 0 < (3 : ℝ)),
    ← ENNReal.ofReal_inv_of_pos (by norm_num : 0 < (6 : ℝ)),
    ← ENNReal.ofReal_inv_of_pos (by norm_num : 0 < (2 : ℝ)),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  norm_num

local instance coefficientProductHolder : ENNReal.HolderTriple 3 6 2 := ennreal_holderTriple_three_six_two

local instance coefficientProductHolderBounded : ENNReal.HolderTriple ⊤ 2 2 :=
  ENNReal.HolderTriple.symm

/-- Hölder's inequality for the pointwise application of an operator
coefficient to a tensor field. -/
theorem eLpNorm_pointwise_operator_apply_le {μ : Measure Point} {p q r : ℝ≥0∞}
    [ENNReal.HolderTriple p q r] {B : Point → S0 →L[ℝ] S0} {u : Point → S0}
    (hB : AEStronglyMeasurable B μ) (hu : AEStronglyMeasurable u μ) :
    eLpNorm (fun x => B x (u x)) r μ ≤ eLpNorm B p μ * eLpNorm u q μ := by
  have h := eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm (p := p) (q := q) (r := r)
    hB hu (fun A : S0 →L[ℝ] S0 => fun v : S0 => A v) 1
    (Eventually.of_forall fun x => by rw [one_mul]; exact (B x).le_opNNNorm _)
  simpa only [ENNReal.coe_one,one_mul] using h

theorem memLp_pointwise_operator_apply {μ : Measure Point} {p q r : ℝ≥0∞}
    [ENNReal.HolderTriple p q r] {B : Point → S0 →L[ℝ] S0} {u : Point → S0}
    (hB : MemLp B p μ) (hu : MemLp u q μ) :
    MemLp (fun x => B x (u x)) r μ :=
  ⟨(continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable (hB.1.prodMk hu.1),
    (eLpNorm_pointwise_operator_apply_le hB.1 hu.1).trans_lt
      (ENNReal.mul_lt_top hB.eLpNorm_lt_top hu.eLpNorm_lt_top)⟩

private theorem tendsto_eLpNorm_operator_apply_zero {μ : Measure Point} {p q r : ℝ≥0∞}
    [ENNReal.HolderTriple p q r] {B : Point → S0 →L[ℝ] S0} {u : ℕ → Point → S0}
    (hB : MemLp B p μ) (hu : ∀ n, AEStronglyMeasurable (u n) μ)
    (h : Tendsto (fun n => eLpNorm (u n) q μ) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun x => B x (u n x)) r μ) atTop (𝓝 0) := by
  have hM := ENNReal.Tendsto.const_mul h (Or.inr hB.eLpNorm_ne_top)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa only [mul_zero] using hM) (fun _ => zero_le)
  exact fun n => eLpNorm_pointwise_operator_apply_le hB.1 (hu n)

private theorem memH1_of_L2_graph_limit {U : Set Point} (hU : IsOpen U)
    [IsFiniteMeasure (volume.restrict U)]
    {f : ℕ → Point → S0} {D : ℕ → Point → Gradient} {v : Point → S0} {G : Point → Gradient}
    (hf : ∀ n, MemH1 U (f n) (D n)) (hv : MemLp v 2 (volume.restrict U))
    (hG : ∀ j, MemLp (fun x => G x j) 2 (volume.restrict U))
    (hF : Tendsto (fun n => eLpNorm (f n - v) 2 (volume.restrict U)) atTop (𝓝 0))
    (hD : ∀ j, Tendsto (fun n => eLpNorm (fun x => D n x j - G x j) 2 (volume.restrict U)) atTop (𝓝 0)) :
    MemH1 U v G := by
  let O : OpenDomain 3 := ⟨U,hU⟩
  apply (memH1_iff_memW12 O v G).2
  apply MemW12.of_L2_limit (fun n => (memH1_iff_memW12 O _ _).1 (hf n))
    ((frobeniusCoordinateEquiv_memLp_iff _ _ _).2 hv)
    (fun j => (frobeniusCoordinateEquiv_memLp_iff _ _ _).2 (hG j))
  · apply hF.congr
    intro n
    apply eLpNorm_congr_norm_ae
    exact Eventually.of_forall fun x => by
      change ‖f n x - v x‖ = ‖frobeniusCoordinateEquiv (f n x) - frobeniusCoordinateEquiv (v x)‖
      rw [← map_sub, LinearIsometryEquiv.norm_map]
  · intro j
    apply (hD j).congr
    intro n
    apply eLpNorm_congr_norm_ae
    exact Eventually.of_forall fun x => by
      change ‖D n x j - G x j‖ = ‖frobeniusCoordinateEquiv (D n x j) - frobeniusCoordinateEquiv (G x j)‖
      rw [← map_sub, LinearIsometryEquiv.norm_map]

/-- The exact weak product rule for applying a bounded smooth coefficient to
a zero-trace Sobolev field. The coefficient derivative is measured in L³. -/
theorem memH1_of_smoothCoefficient_apply_h10
    {U : Set Point} (hU : IsBoundedDomain U) (w : H10 U) {B : Point → S0 →L[ℝ] S0}
    (hB : ContDiffOn ℝ 1 B U) (hBound : MemLp B ⊤ (volume.restrict U))
    (hDeriv : ∀ i, MemLp (coordDeriv i B) 3 (volume.restrict U)) :
    MemH1 U (fun x => B x (h10Value w x))
      (fun x i => (coordDeriv i B x) (h10Value w x) + B x (h10Gradient w x i)) := by
  let μ := volume.restrict U
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr hU.2.2.measure_lt_top.ne
  obtain ⟨_,hSob⟩ := exists_h10_sobolevL6_bound
  have hW6 := (hSob hU.1.measurableSet w).1
  have hW2 : MemLp (h10Value w) 2 μ := Lp.memLp w.val.1
  have hG2 (i : Fin 3) : MemLp (fun x => h10Gradient w x i) 2 μ := Lp.memLp (w.val.2 i)
  obtain ⟨f,hf,hVal,h6,hCol⟩ := w.exists_smooth_approximation_L6 hU.1
  let v (n : ℕ) (x : Point) := B x (f n x)
  let D (n : ℕ) (x : Point) (i : Fin 3) := coordDeriv i B x (f n x) + B x (coordDeriv i (f n) x)
  let u (x : Point) := B x (h10Value w x)
  let G (x : Point) (i : Fin 3) := coordDeriv i B x (h10Value w x) + B x (h10Gradient w x i)
  have hF2 (n : ℕ) : MemLp (f n) 2 μ := (hf n).2.2.2.1
  have hF6 (n : ℕ) : MemLp (f n) 6 μ :=
    ((hf n).1.continuous.memLp_of_hasCompactSupport (hf n).2.1).mono_measure Measure.restrict_le_self
  have hDf (n : ℕ) (i : Fin 3) : MemLp (coordDeriv i (f n)) 2 μ := (hf n).2.2.2.2.1 i
  have hVSob (n : ℕ) : MemH1 U (v n) (D n) := by
    refine ⟨memLp_pointwise_operator_apply hBound (hF2 n),
      fun i => (memLp_pointwise_operator_apply (hDeriv i) (hF6 n)).add
        (memLp_pointwise_operator_apply hBound (hDf n i)), ?_⟩
    have hC : ContDiffOn ℝ 1 (v n) U := hB.clm_apply (((hf n).1.of_le (by simp)).contDiffOn)
    apply (isWeakGradient_of_contDiffOn hU.1 hC).congr_ae EventuallyEq.rfl
    filter_upwards [ae_restrict_mem hU.1.measurableSet] with x hx
    funext i
    have hb := ((hB x hx).contDiffAt (hU.1.mem_nhds hx)).differentiableAt one_ne_zero
    have hF := (hf n).1.differentiable (by simp) x
    change fderiv ℝ (fun x => B x (f n x)) x (axis i) =
      coordDeriv i B x (f n x) + B x (coordDeriv i (f n) x)
    have hProd := congrArg (fun L : Point →L[ℝ] S0 => L (axis i)) (fderiv_clm_apply hb hF)
    refine hProd.trans ?_
    change B x (coordDeriv i (f n) x) + (coordDeriv i B x) (f n x) = _
    exact add_comm _ _
  refine memH1_of_L2_graph_limit hU.1 hVSob (memLp_pointwise_operator_apply hBound hW2)
    (fun i => (memLp_pointwise_operator_apply (hDeriv i) hW6).add
      (memLp_pointwise_operator_apply hBound (hG2 i))) ?_ ?_
  · apply (tendsto_eLpNorm_operator_apply_zero (r := 2) hBound (fun n => ((hF2 n).sub hW2).1) hVal).congr
    intro n
    congr 1
    funext x
    simp only [Pi.sub_apply,v,map_sub]
  · intro i
    let X (n : ℕ) (x : Point) := coordDeriv i B x (f n x - h10Value w x)
    let Y (n : ℕ) (x : Point) := B x (coordDeriv i (f n) x - h10Gradient w x i)
    have hx n := memLp_pointwise_operator_apply (r := 2) (hDeriv i) ((hF6 n).sub hW6)
    have hy n := memLp_pointwise_operator_apply (r := 2) hBound ((hDf n i).sub (hG2 i))
    have hX : Tendsto (fun n => eLpNorm (X n) 2 μ) atTop (𝓝 0) :=
      tendsto_eLpNorm_operator_apply_zero (hDeriv i) (fun n => ((hF6 n).sub hW6).1) h6
    have hY : Tendsto (fun n => eLpNorm (Y n) 2 μ) atTop (𝓝 0) :=
      tendsto_eLpNorm_operator_apply_zero hBound (fun n => ((hDf n i).sub (hG2 i)).1) (hCol i)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa only [add_zero] using hX.add hY) (fun _ => zero_le)
    intro n
    have hE : (fun x => D n x i - G x i) = X n + Y n := by
      funext x
      simp only [X,Y,D,G,Pi.add_apply,map_sub]
      abel
    change eLpNorm (fun x => D n x i - G x i) 2 μ ≤ eLpNorm (X n) 2 μ + eLpNorm (Y n) 2 μ
    rw [hE]
    exact eLpNorm_add_le (hx n).1 (hy n).1 (by norm_num)

end Thesis
