module

public import Thesis.Variational.H10FractionalEmbedding
public import Thesis.Upstream.MinimizingSobolev
import HarmonicMaps.Analysis.SobolevL2Closure
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-! The actual weak graph and its compactly supported approximation
on a finite-volume open set. -/

public section

noncomputable section

open Filter MeasureTheory Set Topology
open scoped BigOperators ContDiff ENNReal Matrix.Norms.Frobenius

namespace Thesis

private theorem h1Deviation_swap {U : Set Point} (u v : Point → S0) (D E : Point → Gradient) :
    h1Deviation U u v D E = h1Deviation U v u E D := by
  unfold h1Deviation
  apply lintegral_congr
  intro x
  have hD : (∑ j : Fin 3, ‖D x j-E x j‖^2) = ∑ j : Fin 3, ‖E x j-D x j‖^2 :=
    Finset.sum_congr rfl fun _ _ => congrArg (fun r : ℝ => r^2) (norm_sub_rev _ _)
  rw [norm_sub_rev (u x) (v x),hD]

private theorem eLpNorm_frobenius_sub_eq {μ : Measure Point} (u v : Point → S0) :
    eLpNorm (frobeniusField u - frobeniusField v) 2 μ = eLpNorm (u-v) 2 μ := by
  apply eLpNorm_congr_norm_ae
  refine Eventually.of_forall fun x => ?_
  change ‖frobeniusCoordinateEquiv (u x)-frobeniusCoordinateEquiv (v x)‖ = ‖u x-v x‖
  rw [← map_sub,LinearIsometryEquiv.norm_map]

private theorem tendsto_normLp_difference_of_ae_representatives {μ : Measure Point}
    {p : ℕ → Lp S0 2 μ} {u : Lp S0 2 μ} (hp : Tendsto p atTop (𝓝 u))
    {φ : ℕ → Point → S0} (hφ : ∀ n, (p n : Point → S0) =ᵐ[μ] φ n) :
    Tendsto (fun n => eLpNorm (φ n - (u : Point → S0)) 2 μ) atTop (𝓝 0) := by
  have hT := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' p u).mp hp
  exact hT.congr (fun n => eLpNorm_congr_ae ((hφ n).sub EventuallyEq.rfl))

/-- The frozen zero-trace graph supplies the original Sobolev value and
all its weak columns, approximated strongly by one compactly supported
smooth sequence. -/
theorem H10.exists_strongH1_smooth_approximation {U : Set Point} (hU : IsOpen U)
    [IsFiniteMeasure (volume.restrict U)] (v : H10 U) :
    ∃ φ : ℕ → Point → S0, (∀ n, ContDiff ℝ ∞ (φ n) ∧ HasCompactSupport (φ n) ∧ tsupport (φ n) ⊆ U) ∧
      StrongH1 U φ (fun n => ClassicalGradient (φ n)) (h10Value v) (h10Gradient v) := by
  obtain ⟨p,φ,hp,hφ⟩ := H10.exists_smooth_graph_approximation v
  let Ω : HarmonicMaps.OpenDomain 3 := ⟨U,hU⟩
  let μ := volume.restrict U
  let u := h10Value v
  let D := h10Gradient v
  let G (n : ℕ) := ClassicalGradient (φ n)
  have hMem (n : ℕ) : MemH1 U (φ n) (G n) := by
    obtain ⟨hS,hComp,hSupp,_,_⟩ := hφ n
    exact (hasZeroTrace_of_contDiff_hasCompactSupport hU hS hComp hSupp).1
  have hV : Tendsto (fun n => eLpNorm (frobeniusField (φ n)-frobeniusField u) 2 μ) atTop (𝓝 0) := by
    have h := tendsto_normLp_difference_of_ae_representatives
      ((continuous_fst.tendsto v.val).comp hp) (fun k => (hφ k).2.2.2.1)
    refine h.congr fun n => ?_
    exact (eLpNorm_frobenius_sub_eq (φ n) u).symm
  have hD (j : Fin 3) : Tendsto (fun n => eLpNorm
      (fun x => frobeniusGradient (G n) x j - frobeniusGradient D x j) 2 μ) atTop (𝓝 0) := by
    have h := tendsto_normLp_difference_of_ae_representatives
      (((continuous_apply j).comp continuous_snd).tendsto v.val |>.comp hp) (fun k => (hφ k).2.2.2.2 j)
    refine h.congr fun n => ?_
    exact (eLpNorm_frobenius_sub_eq (fun x => G n x j) (fun x => D x j)).symm
  have hu : MemLp (frobeniusField u) 2 μ :=
    (frobeniusCoordinateEquiv_memLp_iff _ _ _).mpr (Lp.memLp v.val.1)
  have hDG (j : Fin 3) : MemLp (fun x => frobeniusGradient D x j) 2 μ :=
    (frobeniusCoordinateEquiv_memLp_iff _ _ _).mpr (Lp.memLp (v.val.2 j))
  have hNative (n : ℕ) : HarmonicMaps.MemW12 Ω (frobeniusField (φ n)) (frobeniusGradient (G n)) :=
    (memH1_iff_memW12 Ω _ _).mp (hMem n)
  have hSob : MemH1 U u D := (memH1_iff_memW12 Ω _ _).mpr
    (HarmonicMaps.MemW12.of_L2_limit hNative hu hDG hV hD)
  refine ⟨φ,fun n => ⟨(hφ n).1,(hφ n).2.1,(hφ n).2.2.1⟩,hMem,hSob,?_⟩
  have hPow {f : ℕ → ℝ≥0∞} (hF : Tendsto f atTop (𝓝 0)) :
      Tendsto (fun n => f n ^ 2) atTop (𝓝 0) := by
    simpa only [pow_two,zero_mul] using
      ENNReal.Tendsto.mul hF (Or.inr ENNReal.zero_ne_top) hF (Or.inr ENNReal.zero_ne_top)
  have hSum := tendsto_finsetSum Finset.univ (fun j _ => hPow (hD j))
  have hS := (hPow hV).add hSum
  simp only [Finset.sum_const_zero,add_zero] at hS
  apply hS.congr
  intro n
  rw [h1Deviation_swap (φ n) u (G n) D]
  exact (h1Deviation_eq_sq_eLpNorm U u (φ n) D (G n)
    ((hNative n).2.1.aestronglyMeasurable.sub hu.aestronglyMeasurable)
    (fun j => ((hNative n).2.2 j).aestronglyMeasurable.sub (hDG j).aestronglyMeasurable)).symm

/-- The value and derivative represented by an element of the (H^1_0)
graph have the intrinsic zero trace of the theorem statement. -/
theorem H10.hasZeroTrace {U : Set Point} (hU : IsOpen U)
    [IsFiniteMeasure (volume.restrict U)] (v : H10 U) :
    HasZeroTrace U (h10Value v) (h10Gradient v) := by
  obtain ⟨φ,hφ,hMem,hSob,hLim⟩ := H10.exists_strongH1_smooth_approximation hU v
  refine ⟨hSob,fun δ hδ => ?_⟩
  obtain ⟨n,hn⟩ := (hLim.eventually (Iio_mem_nhds hδ)).exists
  refine ⟨φ n,(hφ n).1,(hφ n).2.1,(hφ n).2.2,?_⟩
  rw [h1Deviation_swap]
  exact hn

end Thesis
