module

public import Thesis.Variational.DirichletPoissonWeak
public import Thesis.Variational.SmoothDomainGlobalPoissonH2
import Thesis.Variational.DirichletPoissonEnergy
import Thesis.Variational.H10StrongApproximation
import Thesis.Upstream.WeakPoissonCoordinates
import Thesis.Upstream.AmbientZeroTraceExtension
import HarmonicMaps.Analysis.SobolevAECongruence
import HarmonicMaps.Analysis.VariableMollificationL2

/-! The global weak (H^2) estimate for the pure Dirichlet Laplacian. -/

public section

noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators ENNReal Matrix.Norms.Frobenius

namespace Thesis

local instance dirichletPoissonH2ContinuousENorm : ContinuousENorm S0 :=
  @SeminormedAddGroup.toContinuousENorm S0 inferInstance

/-- The original zero-trace graph in ambient coordinates with any
chosen almost-everywhere value representative and literal forcing. -/
theorem h10_ambientDirichletPoissonData_of_ae_representative {U : Set Point}
    (hU : IsOpen U) [IsFiniteMeasure (volume.restrict U)]
    (w : H10 U) {f v : Point → S0}
    (hf : MemLp f 2 (volume.restrict U)) (hv : h10Value w =ᵐ[volume.restrict U] v)
    (hEq : ∀ z : H10 U, h10PrincipalPart U w z = ∫ x in U, frobeniusS0 (f x) (h10Value z x)) :
    AmbientDirichletPoissonData U (U.indicator (frobeniusField v))
      (U.indicator (frobeniusGradient (h10Gradient w))) (U.indicator (frobeniusField f)) := by
  let O : HarmonicMaps.OpenDomain 3 := ⟨U,hU⟩
  have hTrace := H10.hasZeroTrace hU w
  have hNative := (hasZeroTrace_iff_hasZeroBoundaryValues O _ _).mp hTrace
  have hVal : frobeniusField (h10Value w) =ᵐ[volume.restrict U] frobeniusField v :=
    hv.mono fun _ hx => congrArg (fun z : S0 => frobeniusCoordinateEquiv z) hx
  have hNative' := hNative.congr_ae hVal EventuallyEq.rfl
  have hWeak := isWeakPoisson_of_H10_pairing hU hf (u := w)
    (fun z => (h10PrincipalPart_apply w z).symm.trans (hEq z))
  obtain ⟨_,hPoisson⟩ := hWeak.to_frobenius hU hTrace.1.memH1Loc
  simp only [traceFreeSymmetricPart_of_S0] at hPoisson
  have hForcing : MemLp (frobeniusField f) 2 (volume.restrict U) :=
    (frobeniusCoordinateEquiv_memLp_iff (volume.restrict U) 2 f).2 hf
  exact ⟨memW12_univ_zeroExtension_of_zeroBoundary hNative',
    HarmonicMaps.memLp_zeroExtension hU.measurableSet hForcing,
    fun x hx => ⟨indicator_of_notMem hx _,indicator_of_notMem hx _⟩,
    weakPoissonOn_packed_indicators hPoisson⟩

theorem h10_ambientDirichletPoissonData {U : Set Point}
    (hU : IsOpen U) [IsFiniteMeasure (volume.restrict U)]
    (w : H10 U) (g : Lp S0 2 (volume.restrict U))
    (hEq : ∀ v : H10 U,
      h10PrincipalPart U w v = ∫ x in U, frobeniusS0 (g x) (h10Value v x)) :
    AmbientDirichletPoissonData U (U.indicator (frobeniusField (h10Value w)))
      (U.indicator (frobeniusGradient (h10Gradient w))) (U.indicator (frobeniusField g)) :=
  h10_ambientDirichletPoissonData_of_ae_representative hU w (Lp.memLp g) EventuallyEq.rfl hEq

private theorem ambient_h10PoissonSize_sq {U : Set Point} (hU : MeasurableSet U)
    (w : H10 U) (g : Lp S0 2 (volume.restrict U)) :
    (ambientPoissonL2Size (U.indicator (frobeniusGradient (h10Gradient w)))
      (U.indicator (frobeniusField g)))^2 =
        ‖h10GradientCoordinates U w‖^2 + ‖g‖^2 := by
  let D := frobeniusGradient (h10Gradient w)
  let f := frobeniusField g
  have hD : (fun x => HarmonicMaps.hsNormSq (U.indicator D x)) =
      U.indicator (fun x => HarmonicMaps.hsNormSq (D x)) := by
    funext x
    by_cases hx : x ∈ U
    · simp only [indicator_of_mem hx]
    · simp [indicator_of_notMem hx,HarmonicMaps.hsNormSq]
  have hF : (fun x => ‖U.indicator f x‖^2) = U.indicator (fun x => ‖g x‖^2) := by
    funext x
    by_cases hx : x ∈ U
    · simp only [indicator_of_mem hx,f,frobeniusField,LinearIsometryEquiv.norm_map]
    · simp [indicator_of_notMem hx]
  rw [ambientPoissonL2Size_sq,hD,hF,integral_indicator hU,integral_indicator hU]
  congr 1
  · have hLp (j : Fin 3) : MemLp (fun x => D x j) 2 (volume.restrict U) :=
      (frobeniusCoordinateEquiv_memLp_iff (volume.restrict U) 2 _).2 (Lp.memLp (w.val.2 j))
    rw [norm_h10GradientCoordinates_eq,Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    unfold HarmonicMaps.hsNormSq
    rw [integral_finsetSum _ (fun j _ => (memLp_two_iff_integrable_sq_norm (hLp j).1).1 (hLp j))]
    apply Finset.sum_congr rfl
    intro j _
    simp only [D,frobeniusGradient,LinearIsometryEquiv.norm_map]
    change (∫ x in U, ‖w.val.2 j x‖^2) = _
    rw [HarmonicMaps.integral_norm_sq_eq_eLpNorm_two_toReal_sq (Lp.memLp (w.val.2 j)),Lp.norm_def]
  · rw [HarmonicMaps.integral_norm_sq_eq_eLpNorm_two_toReal_sq (Lp.memLp g),Lp.norm_def]

/-- The original gradient columns of a weak Dirichlet solution have actual
weak gradients on the entire smooth domain. The domain fixes the constant
before the solution and forcing are chosen. -/
theorem exists_H10_dirichletPoisson_secondWeakGradient {U : Set Point} (hU : IsSmoothDomain U) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (w : H10 U) (g : Lp S0 2 (volume.restrict U)),
        (∀ v : H10 U, h10PrincipalPart U w v = ∫ x in U, frobeniusS0 (g x) (h10Value v x)) →
        ∃ H : Point → Fin 3 → Gradient,
          (∀ j, MemH1 U (fun x => h10Gradient w x j) (fun x => H x j)) ∧
          (∑ j : Fin 3, ∑ i : Fin 3, ∫ x in U, ‖H x j i‖^2) ≤ C^2*‖g‖^2 := by
  letI : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.mpr hU.1.2.2.measure_lt_top.ne
  let O : HarmonicMaps.OpenDomain 3 := ⟨U,hU.1.1⟩
  obtain ⟨C,hC,hH2⟩ := exists_smoothDomain_global_secondWeakColumns (q := 5) hU
  obtain ⟨K,hK,hGradient⟩ := exists_H10_dirichletPoisson_gradientBound hU.1.1.measurableSet hU.1.2.2
  let M := Real.sqrt (K^2+1)
  have hM : 0 ≤ M := Real.sqrt_nonneg _
  refine ⟨3*(C*M),by positivity,?_⟩
  intro w g hEq
  let D := frobeniusGradient (h10Gradient w)
  let D₀ := U.indicator D
  let f₀ := U.indicator (frobeniusField g)
  let E := ambientPoissonL2Size D₀ f₀
  have hE : 0 ≤ E := ambientPoissonL2Size_nonneg _ _
  have hEN : E ≤ M*‖g‖ := by
    apply (sq_le_sq₀ hE (mul_nonneg hM (norm_nonneg _))).1
    rw [show E^2 = ‖h10GradientCoordinates U w‖^2 + ‖g‖^2 from
      ambient_h10PoissonSize_sq hU.1.1.measurableSet w g,mul_pow,Real.sq_sqrt (by positivity),add_mul,one_mul]
    have h := pow_le_pow_left₀ (norm_nonneg _) (hGradient w g hEq) 2
    rw [mul_pow] at h
    exact add_le_add h le_rfl
  obtain ⟨G,hG⟩ := hH2 (h10_ambientDirichletPoissonData hU.1.1 w g hEq)
  let H (x : Point) (j i : Fin 3) := frobeniusCoordinateEquiv.symm (G x j i)
  have hGraph (j : Fin 3) : MemH1 U (fun x => h10Gradient w x j) (fun x => H x j) := by
    apply (memH1_iff_memW12 O _ _).2
    have hw : (fun x => D₀ x j) =ᵐ[volume.restrict U] fun x => D x j := by
      filter_upwards [ae_restrict_mem hU.1.1.measurableSet] with x hx
      change U.indicator D x j = _
      rw [indicator_of_mem hx]
    have hh := (hG j).1.congr_ae hw (EventuallyEq.rfl)
    change HarmonicMaps.MemW12 O (fun x => D x j) (fun x i => frobeniusCoordinateEquiv (H x j i))
    have hCols : (fun x i => frobeniusCoordinateEquiv (H x j i)) = fun x => G x j :=
      funext fun x => funext fun i => frobeniusCoordinateEquiv.apply_symm_apply (G x j i)
    rw [hCols]
    exact hh
  refine ⟨H,hGraph,?_⟩
  have hOne (j i : Fin 3) :
      (∫ x in U, ‖H x j i‖^2) ≤ ((C*M)*‖g‖)^2 := by
    simp only [H,LinearIsometryEquiv.norm_map]
    rw [← ambient_lpNorm_two_sq ((hG j).1.2.2 i)]
    apply pow_le_pow_left₀ lpNorm_nonneg _ 2
    exact ((hG j).2 i).trans
      ((mul_le_mul_of_nonneg_left hEN hC).trans_eq (mul_assoc _ _ _).symm)
  calc
    _ ≤ ∑ _j : Fin 3, ∑ _i : Fin 3, ((C*M)*‖g‖)^2 :=
      Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun i _ => hOne j i))
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat]; ring

end Thesis
