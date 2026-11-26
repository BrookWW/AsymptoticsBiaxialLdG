module

public import Thesis.Interpolation.FiniteL2TraceEstimate
public import Thesis.Interpolation.QuaternionAmbientCollar
import StratificationTheory.Foundation.AmbientRadialTrace
import StratificationTheory.Foundation.AngularL2Membership
import HarmonicMaps.Analysis.L2TranslationContinuity

/-! The actual radial trace and quantitative endpoint bound of a Euclidean ball. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set StratificationTheory
open scoped BigOperators ContDiff ENNReal Topology

namespace Thesis

/-- The unweighted native polar collar has the reciprocal inner-radius
Jacobian as its squared L² bound. The endpoint does not affect the class. -/
theorem memLp_native_ball_closed_radial_product {n : ℕ} (hn : 0 < n)
    {E : Type*} [NormedAddCommGroup E] {f : Domain n → E} {a R : ℝ} (ha : 0 < a)
    (hf : MemLp f 2 (volume.restrict (ball (0 : Domain n) R))) :
    let F (p : UnitBoundarySphere n × ℝ) := f (p.2 • p.1.val)
    let μ := (unitBoundarySurface n).prod (volume.restrict (Icc a R))
    MemLp F 2 μ ∧ (∫ p, ‖F p‖ ^ 2 ∂μ) ≤ (a ^ (n - 1))⁻¹ * ∫ x in ball (0 : Domain n) R, ‖f x‖ ^ 2 := by
  intro F μ
  let f₀ := (ball (0 : Domain n) R).indicator f
  have h₀ : MemLp f₀ 2 volume := memLp_zeroExtension measurableSet_ball hf
  have hProd := memLp_two_radial_product_ball_and_norm hn (c := (0 : Domain n))
    (a := a) (b := R) (R := R + 1) ha (lt_add_one R)
    (h₀.mono_measure (Measure.restrict_le_self (s := ball (0 : Domain n) (R + 1))))
  let G (p : UnitBoundarySphere n × ℝ) := f₀ (p.2 • p.1.val)
  have hG : MemLp G 2 μ := by simpa only [G, zero_add] using hProd.1
  have hEq : G =ᵐ[μ] F := by
    have hRay : ∀ᵐ r ∂volume.restrict (Icc a R), r ∈ Ioo a R := by
      rw [← Measure.restrict_congr_set Ioo_ae_eq_Icc]
      exact ae_restrict_mem measurableSet_Ioo
    filter_upwards [Measure.quasiMeasurePreserving_snd.ae hRay] with p hp
    change f₀ (p.2 • p.1.val) = f (p.2 • p.1.val)
    apply Set.indicator_of_mem
    rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg (ha.trans hp.1).le,
      mem_sphere_zero_iff_norm.mp p.1.property, mul_one]
    exact hp.2
  have hF := hG.ae_eq hEq
  refine ⟨hF, ?_⟩
  have hBound : eLpNorm F 2 μ ≤ ENNReal.ofReal ((a ^ (n - 1))⁻¹) ^ (1 / 2 : ℝ) *
      eLpNorm f 2 (volume.restrict (ball (0 : Domain n) R)) := by
    rw [← eLpNorm_congr_ae hEq, ← eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_ball]
    have hR : eLpNorm G 2 μ ≤ ENNReal.ofReal ((a ^ (n - 1))⁻¹) ^ (1 / 2 : ℝ) *
        eLpNorm f₀ 2 (volume.restrict (ball (0 : Domain n) (R + 1))) := by
      simpa only [G, zero_add] using hProd.2
    exact hR.trans (mul_le_mul_right (eLpNorm_mono_measure _ Measure.restrict_le_self) _)
  have hn₀ : 0 ≤ (a ^ (n - 1))⁻¹ := inv_nonneg.mpr (pow_nonneg ha.le _)
  have hBFinite : ENNReal.ofReal ((a ^ (n - 1))⁻¹) ^ (1 / 2 : ℝ) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
  have hReal := ENNReal.toReal_mono (ENNReal.mul_ne_top hBFinite hf.eLpNorm_ne_top) hBound
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal hn₀, ← Real.sqrt_eq_rpow] at hReal
  have hPow := pow_le_pow_left₀ ENNReal.toReal_nonneg hReal 2
  rw [mul_pow, Real.sq_sqrt hn₀] at hPow
  rw [integral_norm_sq_eq_eLpNorm_two_toReal_sq hF, integral_norm_sq_eq_eLpNorm_two_toReal_sq hf]
  exact hPow

private theorem ball_radial_test_support_local {φ : ℝ → ℝ} {a R : ℝ} (haR : a < R)
    (hφ : HasCompactSupport φ) (hSupp : tsupport φ ⊆ Ioo a R) :
    ∃ b : ℝ, a < b ∧ b < R ∧ tsupport φ ⊆ Ioo a b := by
  let K := tsupport φ ∪ {a}
  have hK : IsCompact K := hφ.union isCompact_singleton
  have hAt : a ∈ K := Or.inr rfl
  obtain ⟨m, hmK, hm⟩ := hK.exists_isGreatest ⟨a, hAt⟩
  have hm₀ := hm hAt
  have hm₁ : m < R := by
    rcases hmK with h | h
    · exact (hSupp h).2
    · rw [mem_singleton_iff] at h
      exact h ▸ haR
  let b := (m + R) / 2
  have hmb : m < b := by dsimp only [b]; linarith only [hm₁]
  refine ⟨b, hm₀.trans_lt hmb, by dsimp only [b]; linarith only [hm₁], ?_⟩
  intro t ht
  exact ⟨(hSupp ht).1, (hm (Or.inl ht)).trans_lt hmb⟩

private theorem ball_radial_full_time_weak {n q : ℕ} (hn : 0 < n)
    {u : Domain n → Ambient q} {D : Domain n → HarmonicMaps.Gradient n q}
    {a R : ℝ} (ha : 0 < a) (haR : a < R) (hu : MemW12 (ballDomain (0 : Domain n) R) u D)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ Ioo a R) :
    ∀ᵐ θ ∂unitBoundarySurface n,
      (∫ t in Icc a R, deriv φ t • u (t • θ.val)) =
        -(∫ t in Icc a R, φ t • ∑ i : Fin n, θ.val i • D (t • θ.val) i) := by
  obtain ⟨b, hab, hbR, hs'⟩ := ball_radial_test_support_local haR hc hs
  have hW := (radial_product_weak_identity_of_memW12_ball hn ha hab hbR hu).2.2 φ hφ hc hs'
  filter_upwards [hW] with θ h
  have hCut {ψ : ℝ → ℝ} (hψ : tsupport ψ ⊆ Ioo a b) (v : ℝ → Ambient q) :
      (∫ t in Icc a b, ψ t • v t) = ∫ t in Icc a R, ψ t • v t := by
    have hGlobal (d : ℝ) (hd : b ≤ d) : (∫ t in Icc a d, ψ t • v t) = ∫ t, ψ t • v t := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro t ht
      have hZero : ψ t = 0 := image_eq_zero_of_notMem_tsupport fun ht' =>
        ht ⟨(hψ ht').1.le, (hψ ht').2.le.trans hd⟩
      rw [hZero, zero_smul]
    rw [hGlobal b le_rfl, hGlobal R hbR.le]
  rw [← hCut (tsupport_deriv_subset.trans hs') (fun t => u (t • θ.val)),
    ← hCut hs' (fun t => ∑ i : Fin n, θ.val i • D (t • θ.val) i)]
  simpa only [zero_add] using h

/-- The actual radial L² curve on a ball has the stated estimate at the real
boundary endpoint as well as all interior radii. -/
theorem exists_native_ball_radial_trace_with_estimate {n q : ℕ} (hn : 0 < n)
    {u : Domain n → Ambient q} {D : Domain n → HarmonicMaps.Gradient n q}
    {a R : ℝ} (ha : 0 < a) (haR : a < R) (hu : MemW12 (ballDomain (0 : Domain n) R) u D) :
    ∃ H : C(Icc a R, Lp (Ambient q) 2 (unitBoundarySurface n)),
      (∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo a R,
        ∃ hLp : MemLp (fun θ : UnitBoundarySphere n => u (t • θ.val)) 2 (unitBoundarySurface n),
          H ⟨t, ht.1.le, ht.2.le⟩ = hLp.toLp _) ∧
      ∀ t : Icc a R, ‖H t‖ ^ 2 ≤
        (2 / (R - a)) * ((a ^ (n - 1))⁻¹ * ∫ x in ball (0 : Domain n) R, ‖u x‖ ^ 2) +
        2 * (R - a) * ((a ^ (n - 1))⁻¹ * ∫ x in ball (0 : Domain n) R, hsNormSq (D x)) := by
  let σ := unitBoundarySurface n
  let μ := σ.prod (volume.restrict (Icc a R))
  let F (p : UnitBoundarySphere n × ℝ) := u (p.2 • p.1.val)
  let G (p : UnitBoundarySphere n × ℝ) := ∑ i : Fin n, p.1.val i • D (p.2 • p.1.val) i
  letI : IsFiniteMeasure σ := by
    dsimp only [σ, unitBoundarySurface]
    rw [euclideanHausdorffMeasure_unitSphere_eq_toSphere hn]
    infer_instance
  letI : MeasurableSpace.CountablyGenerated (UnitBoundarySphere n) := BorelSpace.countablyGenerated
  letI : IsSeparable σ := inferInstance
  obtain ⟨hF, hFBound⟩ := memLp_native_ball_closed_radial_product hn ha hu.2.1
  have hD (i : Fin n) := memLp_native_ball_closed_radial_product hn ha (hu.2.2 i)
  have hG : MemLp G 2 μ := by
    have hT (i : Fin n) : MemLp (fun p : UnitBoundarySphere n × ℝ => p.1.val i) ⊤ μ := by
      have hC : Continuous (fun p : UnitBoundarySphere n × ℝ => p.1.val i) :=
        (EuclideanSpace.proj i).continuous.comp (continuous_subtype_val.comp continuous_fst)
      apply memLp_top_of_bound hC.measurable.aestronglyMeasurable 1
      exact ae_of_all _ fun p => (PiLp.norm_apply_le p.1.val i).trans_eq
        (mem_sphere_zero_iff_norm.mp p.1.property)
    have hSum := memLp_finsetSum Finset.univ (fun i (_ : i ∈ Finset.univ) => ((hD i).1).smul (r := 2) (hT i))
    simpa only [G, Finset.sum_apply, Pi.smul_apply'] using hSum
  have hDInt (i : Fin n) : Integrable (fun p : UnitBoundarySphere n × ℝ => ‖D (p.2 • p.1.val) i‖ ^ 2) μ :=
    (hD i).1.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
  have hGPoint (p : UnitBoundarySphere n × ℝ) : ‖G p‖ ^ 2 ≤ hsNormSq (D (p.2 • p.1.val)) := by
    have h := norm_sq_sum_gradient_le (D (p.2 • p.1.val)) p.1.val
    have hNorm := mem_sphere_zero_iff_norm.mp p.1.property
    simpa only [G, hNorm, one_pow, one_mul] using h
  have hGbound : (∫ p, ‖G p‖ ^ 2 ∂μ) ≤ (a ^ (n - 1))⁻¹ * ∫ x in ball (0 : Domain n) R, hsNormSq (D x) := by
    calc
      _ ≤ ∫ p : UnitBoundarySphere n × ℝ, ∑ i : Fin n, ‖D (p.2 • p.1.val) i‖ ^ 2 ∂μ :=
        integral_mono (hG.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0))
          (integrable_finsetSum _ fun i _ => hDInt i) hGPoint
      _ = ∑ i : Fin n, ∫ p : UnitBoundarySphere n × ℝ, ‖D (p.2 • p.1.val) i‖ ^ 2 ∂μ :=
        integral_finsetSum _ (fun i _ => hDInt i)
      _ ≤ ∑ i : Fin n, (a ^ (n - 1))⁻¹ * ∫ x in ball (0 : Domain n) R, ‖D x i‖ ^ 2 :=
        Finset.sum_le_sum (fun i _ => (hD i).2)
      _ = _ := by
        have hI (i : Fin n) : IntegrableOn (fun x => ‖D x i‖ ^ 2) (ball (0 : Domain n) R) :=
          (hu.2.2 i).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
        rw [← Finset.mul_sum, ← integral_finsetSum _ (fun i _ => hI i)]
        rfl
  obtain ⟨H, hH, hBound⟩ := exists_finite_L2_trace_with_endpoint_estimate σ haR hF hG
    (fun φ hφ hc hs => ball_radial_full_time_weak hn ha haR hu φ hφ hc hs)
  refine ⟨H, hH, fun t => (hBound t).trans ?_⟩
  exact add_le_add (mul_le_mul_of_nonneg_left hFBound (by positivity [sub_pos.mpr haR]))
    (mul_le_mul_of_nonneg_left hGbound (by linarith only [haR]))

end Thesis

end
