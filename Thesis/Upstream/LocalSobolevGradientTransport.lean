module

public import Thesis.Upstream.GlobalCompactSobolevTransport
public import Thesis.Variational.LocalEllipticNormalGradient
import HarmonicMaps.Analysis.VariableMollificationL2
import StratificationTheory.Foundation.SmoothOpenDomainSobolevPullback

/-! Quantitative Sobolev transport and smooth multiplication on bounded patches. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Set StratificationTheory
open scoped BigOperators ContDiff ENNReal

namespace Thesis

theorem ambient_lpNorm_two_sq {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    {μ : Measure X} {f : X → E} (hf : MemLp f 2 μ) :
    (lpNorm f 2 μ)^2 = ∫ x, ‖f x‖^2 ∂μ := by
  rw [← toReal_eLpNorm hf.1,integral_norm_sq_eq_eLpNorm_two_toReal_sq hf]

theorem ambient_lpNorm_comp_measurePreserving {X Y E : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [NormedAddCommGroup E] {μ : Measure X} {ν : Measure Y} {F : X → Y}
    (hF : MeasurePreserving F μ ν) {f : Y → E} {p : ℝ≥0∞} (hf : MemLp f p ν) :
    lpNorm (f ∘ F) p μ = lpNorm f p ν := by
  rw [← toReal_eLpNorm (hf.comp_measurePreserving hF).1,← toReal_eLpNorm hf.1,
    eLpNorm_comp_measurePreserving hf.1 hF]

theorem ambient_lpNorm_two_mono_measure {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    {μ ν : Measure X} {f : X → E} (hf : MemLp f 2 ν) (hμ : μ ≤ ν) :
    lpNorm f 2 μ ≤ lpNorm f 2 ν := by
  rw [← toReal_eLpNorm (hf.mono_measure hμ).1,← toReal_eLpNorm hf.1]
  exact ENNReal.toReal_mono hf.eLpNorm_ne_top (eLpNorm_mono_measure f hμ)

theorem exists_uniform_abs_bound_on_compact {X ι : Type*} [TopologicalSpace X] [Fintype ι]
    {K : Set X} (hK : IsCompact K) (a : ι → X → ℝ) (ha : ∀ j, Continuous (a j)) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ j x, x ∈ K → |a j x| ≤ L := by
  classical
  choose M hM using fun j => hK.exists_bound_of_continuousOn (ha j).continuousOn
  let L := ∑ j : ι, max (M j) 0
  refine ⟨L,Finset.sum_nonneg (fun _ _ => le_max_right _ _),fun j x hx => ?_⟩
  rw [← Real.norm_eq_abs]
  exact (hM j x hx).trans <| (le_max_left _ _).trans
    (Finset.single_le_sum (f := fun i => max (M i) 0) (fun _ _ => le_max_right _ _) (Finset.mem_univ j))

theorem memW12_of_ambient_coordinate_partials {n q : ℕ} (V : OpenDomain n)
    [IsFiniteMeasure ((volume : Measure (Domain n)).restrict V.val)]
    {u : Domain n → Ambient q} {D : Domain n → HarmonicMaps.Gradient n q}
    (hu : MemLp u 2 (volume.restrict V.val))
    (hD : ∀ i, MemLp (fun x => D x i) 2 (volume.restrict V.val))
    (h : ∀ i, IsWeakAmbientCoordinatePartial V.val i u (fun x => D x i)) :
    MemW12 V u D :=
  ⟨⟨IntegrableOn.locallyIntegrableOn (hu.integrable (by norm_num)),
    fun i => IntegrableOn.locallyIntegrableOn ((hD i).integrable (by norm_num)),h⟩,hu,hD⟩

private theorem coordinate_fderiv_norm_bound {n : ℕ}
    {F : Domain n → Domain n} {x : Domain n} {L : ℝ} (h : ‖fderiv ℝ F x‖ ≤ L)
    (i j : Fin n) : |(fderiv ℝ F x (EuclideanSpace.single i 1)) j| ≤ L := by
  simpa only [Real.norm_eq_abs] using
    (PiLp.norm_apply_le (fderiv ℝ F x (EuclideanSpace.single i 1)) j).trans
      (((fderiv ℝ F x).le_opNorm (EuclideanSpace.single i 1)).trans
        (by rwa [PiLp.norm_single,norm_one,mul_one]))

/-- A smooth volume-preserving coordinate map transports the first weak
graph and bounds each displayed derivative by the original column bounds. -/
theorem exists_memW12_local_volumePreserving_pullback {n q : ℕ}
    (F : Domain n ≃ₜ Domain n) (hF : ContDiff ℝ ∞ (F : Domain n → Domain n))
    (V W : OpenDomain n) (hBound : Bornology.IsBounded V.val)
    (hInto : MapsTo F V.val W.val)
    (hMP : MeasurePreserving F (volume.restrict V.val) (volume.restrict W.val)) :
    ∃ L : ℝ, 0 ≤ L ∧
      ∀ {u : Domain n → Ambient q} {D : Domain n → HarmonicMaps.Gradient n q},
        MemW12 W u D → ∀ E : ℝ,
        (∀ j : Fin n, lpNorm (fun x => D x j) 2 (volume.restrict W.val) ≤ E) →
        MemW12 V (u ∘ F) (ambientGradientPullback F D) ∧
          lpNorm (u ∘ F) 2 (volume.restrict V.val) = lpNorm u 2 (volume.restrict W.val) ∧
          ∀ i, lpNorm (fun x => ambientGradientPullback F D x i) 2 (volume.restrict V.val) ≤ L*E := by
  obtain ⟨M,hM⟩ := hBound.isCompact_closure.exists_bound_of_continuousOn
    (hF.continuous_fderiv (by simp)).continuousOn
  let K := max M 0
  have hK : 0 ≤ K := le_max_right _ _
  have hDK (x : Domain n) (hx : x ∈ V.val) : ‖fderiv ℝ F x‖ ≤ K :=
    (hM x (subset_closure hx)).trans (le_max_left _ _)
  refine ⟨(n : ℝ)*K, by positivity,?_⟩
  intro u D hu E hE
  refine ⟨?_,ambient_lpNorm_comp_measurePreserving hMP hu.2.1,fun i => ?_⟩
  · apply memW12_smooth_open_domain_pullback hu V F hF.contDiffOn hInto K hDK 1 ENNReal.one_ne_top
    rw [one_smul,hMP.map_eq]
  · let d (j : Fin n) (x : Domain n) := D (F x) j
    let a (j : Fin n) (x : Domain n) := fderiv ℝ F x (EuclideanSpace.single i 1) j
    have hd (j : Fin n) : MemLp (d j) 2 (volume.restrict V.val) := (hu.2.2 j).comp_measurePreserving hMP
    have ha (j : Fin n) : Continuous (a j) :=
      (EuclideanSpace.proj j).continuous.comp ((hF.continuous_fderiv (by simp)).clm_apply continuous_const)
    have hB (j : Fin n) (x : Domain n) (hx : x ∈ V.val) : |a j x| ≤ K :=
      coordinate_fderiv_norm_bound (hDK x hx) i j
    have hLp (j : Fin n) : MemLp (fun x => a j x • d j x) 2 (volume.restrict V.val) :=
      (hd j).smul (r := (2 : ℝ≥0∞)) (contDiff_norm_bound_memLp_top V.property.measurableSet (ha j) (hB j))
    have hNorm (j : Fin n) : lpNorm (fun x => a j x • d j x) 2 (volume.restrict V.val) ≤ K*E := by
      refine (lpNorm_smul_restrict_le V.property.measurableSet (hd j) hK (hB j)).trans ?_
      rw [show d j = (fun x => D x j) ∘ F from rfl,ambient_lpNorm_comp_measurePreserving hMP (hu.2.2 j)]
      exact mul_le_mul_of_nonneg_left (hE j) hK
    have h := (lpNorm_finsetSum_le_card_mul Finset.univ (fun j _ => hLp j) (fun j _ => hNorm j)).2
    simpa only [ambientGradientPullback,Finset.card_univ,Fintype.card_fin,mul_assoc] using h

/-- The gradient column obtained by pulling a weak derivative through the
inverse chart agrees pointwise with the original displayed column. -/
theorem ambientGradientPullback_symm_pullback {n q : ℕ}
    (F : Domain n ≃ₜ Domain n) (hF : ContDiff ℝ ∞ (F : Domain n → Domain n))
    (hInv : ContDiff ℝ ∞ (F.symm : Domain n → Domain n))
    (D : Domain n → HarmonicMaps.Gradient n q) (x : Domain n) (j : Fin n) :
    ambientGradientPullback F.symm (ambientGradientPullback F D) x j = D x j := by
  have hK : (fderiv ℝ F (F.symm x)).comp (fderiv ℝ F.symm x) =
      ContinuousLinearMap.id ℝ (Domain n) :=
    fderiv_symm_comp_fderiv_homeomorph F.symm hInv hF x
  have he : packAmbientGradient (ambientGradientPullback F.symm (ambientGradientPullback F D) x) =
      packAmbientGradient (D x) := by
    rw [packAmbientGradient_pullback,packAmbientGradient_pullback,ambientGradientPrecompose_comp,hK,
      ambientGradientPrecompose_id,F.apply_symm_apply]
  exact congrArg (fun z : AmbientGradientHilbert n q => z j) he

end Thesis
