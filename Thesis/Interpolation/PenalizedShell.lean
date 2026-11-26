module

public import Thesis.Variational.StrongComparison
public import StratificationTheory.Frozen.SphereGradientCharacterization
import Thesis.Foundation.VacuumTarget
import HarmonicMaps.Analysis.SobolevPostcompositionLocal
import StratificationTheory.Foundation.AngularL2Membership
import StratificationTheory.Foundation.CylinderPostcomposition
import StratificationTheory.Foundation.RadialPiecewiseSobolevData
import StratificationTheory.Foundation.RadialPiecewiseTrace
import StratificationTheory.Foundation.SphereAEClasses
import StratificationTheory.Frozen.RadialTraceGluing
import StratificationTheory.Frozen.SphereRadialBallExtension
import StratificationTheory.Interpolation.ProjectedLuckhausAnnularConnector
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-! The projected Luckhaus connector in the annular geometry of the thesis. -/

public section

set_option autoImplicit false
noncomputable section

open Filter MeasureTheory Set Metric
open scoped Topology ENNReal BigOperators ContDiff Matrix.Norms.Frobenius

namespace Thesis

abbrev UnitTensorSphere := sphere (0 : Point) 1

abbrev tensorSphereMeasure : Measure UnitTensorSphere := Measure.euclideanHausdorffMeasure 2

/-- The actual H¹ sphere class of a symmetric traceless tensor map. -/
abbrev MemSphereH1 (u : UnitTensorSphere → S0) :=
  StratificationTheory.MemSphereW12 (by decide : 2 ≤ 3) (fun θ => frobeniusCoordinateEquiv (u θ))

/-- The unhalved squared tangential-gradient integral on the unit sphere. -/
@[expose] def sphereGradientEnergy (u : UnitTensorSphere → S0) (hu : MemSphereH1 u) : ℝ :=
  ∫ θ : UnitTensorSphere, ∑ i : Fin 3,
    ‖StratificationTheory.sphereGradient (by decide : 2 ≤ 3)
      (fun η => frobeniusCoordinateEquiv (u η)) hu i θ‖ ^ 2 ∂tensorSphereMeasure

@[expose] def sphereL2DifferenceSq (u v : UnitTensorSphere → S0) : ℝ :=
  ∫ θ : UnitTensorSphere, ‖u θ - v θ‖ ^ 2 ∂tensorSphereMeasure

/-- An annular Sobolev map and its two prescribed sphere classes. The raw
slices represent the same trace on the whole closed interval of radii. -/
structure SphereAnnularLayer (r s : ℝ) (hrs : r ≤ s) (inner outer : UnitTensorSphere → S0)
    (hInner : MemSphereH1 inner) (hOuter : MemSphereH1 outer) where
  toFun : Point → S0
  gradient : Point → Gradient
  sobolev : MemH1 (radialAnnulus 0 r s) toFun gradient
  trace : RadialL2Trace r s
  traceData : RepresentsRadialL2Trace 0 toFun trace
  inner_eq : trace ⟨r, le_rfl, hrs⟩ =
    hInner.1.toLp (fun θ => frobeniusCoordinateEquiv (inner θ))
  outer_eq : trace ⟨s, hrs, le_rfl⟩ =
    hOuter.1.toLp (fun θ => frobeniusCoordinateEquiv (outer θ))

theorem nonneg_sphereGradientEnergy (u : UnitTensorSphere → S0) (hu : MemSphereH1 u) :
    0 ≤ sphereGradientEnergy u hu :=
  integral_nonneg (fun _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))

theorem nonneg_sphereL2DifferenceSq (u v : UnitTensorSphere → S0) :
    0 ≤ sphereL2DifferenceSq u v := integral_nonneg (fun _ => sq_nonneg _)

private theorem annular_parameter_bounds {ℓ : ℝ} (hℓ : 0 < ℓ) (hℓsmall : ℓ < 1 / 9) :
    let η := ℓ / (1 - ℓ)
    0 < η ∧ η < 1 / 8 ∧ ℓ ≤ η ∧ η ≤ 2 * ℓ := by
  intro η
  have hden : 0 < 1 - ℓ := by linarith only [hℓsmall]
  refine ⟨div_pos hℓ hden, (div_lt_iff₀ hden).mpr ?_, (le_div_iff₀ hden).mpr ?_,
    (div_le_iff₀ hden).mpr ?_⟩
  · linarith only [hℓsmall]
  · nlinarith only [sq_nonneg ℓ]
  · have hprod := mul_nonneg hℓ.le (show (0 : ℝ) ≤ 1 - 2 * ℓ by linarith only [hℓsmall])
    nlinarith only [hprod]

private theorem ordinary_luckhaus_scalar_estimates
    {A D B C ℓ : ℝ} (hA : 0 ≤ A) (hAB : A ≤ B) (hD : 0 ≤ D) (hDB : D ≤ B * ℓ ^ 8)
    (hB : 0 < B) (hC : 0 < C) (hℓ : 0 < ℓ) (hℓsmall : ℓ < 1 / 9) :
    let η := ℓ / (1 - ℓ)
    C * η ^ (1 - (3 : ℤ)) * Real.sqrt A * Real.sqrt D + C * η ^ (-(3 : ℤ)) * D
        ≤ 2 * C * B * ℓ ^ 2 ∧ η * A + η⁻¹ * D ≤ 3 * B * ℓ := by
  intro η
  obtain ⟨hη, _, hℓη, hηℓ⟩ := annular_parameter_bounds hℓ hℓsmall
  have hℓ1 : ℓ ≤ 1 := by linarith only [hℓsmall]
  have hInv : η⁻¹ ≤ ℓ⁻¹ := (inv_le_inv₀ hη hℓ).mpr hℓη
  have hSqrtD : Real.sqrt D ≤ Real.sqrt B * ℓ ^ 4 := by
    refine (Real.sqrt_le_sqrt hDB).trans_eq ?_
    rw [Real.sqrt_mul hB.le, show ℓ ^ 8 = (ℓ ^ 4) ^ 2 by ring,
      Real.sqrt_sq (by positivity)]
  have hSqrt : Real.sqrt A * Real.sqrt D ≤ B * ℓ ^ 4 := by
    have h := mul_le_mul (Real.sqrt_le_sqrt hAB) hSqrtD
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    rwa [← mul_assoc, ← pow_two, Real.sq_sqrt hB.le] at h
  have hℓpow (m : ℕ) : ℓ ^ m ≤ 1 := pow_le_one₀ hℓ.le hℓ1
  have hηnonneg : 0 ≤ η⁻¹ := inv_nonneg.mpr hη.le
  have hFirst : C * η⁻¹ ^ 2 * Real.sqrt A * Real.sqrt D ≤ C * B * ℓ ^ 2 := by
    calc
      _ = C * (η⁻¹ ^ 2 * (Real.sqrt A * Real.sqrt D)) := by ring
      _ ≤ C * (ℓ⁻¹ ^ 2 * (B * ℓ ^ 4)) := by
        apply mul_le_mul_of_nonneg_left _ hC.le
        exact mul_le_mul (pow_le_pow_left₀ hηnonneg hInv 2) hSqrt
          (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (by positivity)
      _ = _ := by field_simp
  have hSecond : C * η⁻¹ ^ 3 * D ≤ C * B * ℓ ^ 2 := by
    calc
      _ = C * (η⁻¹ ^ 3 * D) := by ring
      _ ≤ C * (ℓ⁻¹ ^ 3 * (B * ℓ ^ 8)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul (pow_le_pow_left₀ hηnonneg hInv 3) hDB hD (by positivity)) hC.le
      _ = C * B * ℓ ^ 2 * ℓ ^ 3 := by field_simp
      _ ≤ _ := mul_le_of_le_one_right (by positivity) (hℓpow 3)
  have hMixed : η⁻¹ * D ≤ B * ℓ := by
    calc
      _ ≤ ℓ⁻¹ * (B * ℓ ^ 8) := mul_le_mul hInv hDB hD (by positivity)
      _ = B * ℓ * ℓ ^ 6 := by field_simp
      _ ≤ _ := mul_le_of_le_one_right (by positivity) (hℓpow 6)
  constructor
  · have hp₂ : η ^ (1 - (3 : ℤ)) = η⁻¹ ^ 2 := by norm_num [zpow_neg, inv_pow]; rfl
    have hp₃ : η ^ (-(3 : ℤ)) = η⁻¹ ^ 3 := by norm_num [zpow_neg, inv_pow]; rfl
    rw [hp₂, hp₃]
    linarith only [hFirst, hSecond]
  · have hAA := mul_le_mul hηℓ hAB hA (by positivity : 0 ≤ 2 * ℓ)
    linarith only [hAA, hMixed]

/-- The ordinary projected connector at thickness `ℓ` joins two vacuum
sphere traces on the annulus from `(1 - ℓ) * R` to `R`. The quantitatively
bounded squared separation is of order `ℓ ^ 8`. -/
theorem exists_ordinary_vacuum_annular_layer (a : BulkCoefficients) (B : ℝ) (hB : 0 < B) :
    ∃ δ C : ℝ, 0 < δ ∧ δ ≤ 1 / 9 ∧ 0 < C ∧
      ∀ (R ℓ : ℝ) (hR : 0 < R) (hℓ : 0 < ℓ) (hℓδ : ℓ < δ)
        (u v : UnitTensorSphere → S0) (hu : MemSphereH1 u) (hv : MemSphereH1 v),
        (∀ᵐ θ ∂tensorSphereMeasure, u θ ∈ vacuum a) →
        (∀ᵐ θ ∂tensorSphereMeasure, v θ ∈ vacuum a) →
        sphereGradientEnergy u hu + sphereGradientEnergy v hv ≤ B →
        sphereL2DifferenceSq u v ≤ B * ℓ ^ 8 →
        ∃ W : SphereAnnularLayer ((1 - ℓ) * R) R
            (by nlinarith only [hR, hℓ, mul_pos hR hℓ]) u v hu hv,
          TakesVacuumValues a (radialAnnulus 0 ((1 - ℓ) * R) R) W.toFun ∧
          dirichletEnergy (radialAnnulus 0 ((1 - ℓ) * R) R) W.gradient ≤
            ENNReal.ofReal (C * R * ℓ) := by
  let N := vacuumCompactSmoothEmbeddedTarget a
  obtain ⟨ρ, L, hρ, hL, hConnector⟩ :=
    StratificationTheory.Interpolation.exists_projected_luckhaus_annulus_operator
      (n := 3) (by decide) N
  obtain ⟨d, hd, hdSmall⟩ := exists_pos_mul_lt (sq_pos_of_pos hρ) (2 * L * B)
  let δ := min (1 / 9 : ℝ) d
  refine ⟨δ, 24 * L * B, lt_min (by norm_num) hd, min_le_left _ _, by positivity, ?_⟩
  intro R ℓ hR hℓ hℓδ u v hu hv huN hvN hGrad hDiff
  have hℓsmall : ℓ < 1 / 9 := hℓδ.trans_le (min_le_left _ _)
  let η := ℓ / (1 - ℓ)
  obtain ⟨hη, hηsmall, _, _⟩ := annular_parameter_bounds hℓ hℓsmall
  have huN' : ∀ᵐ θ ∂tensorSphereMeasure, frobeniusCoordinateEquiv (u θ) ∈ N.carrierSet :=
    huN.mono fun θ h => by
      rw [vacuumCompactSmoothEmbeddedTarget_carrierSet]
      exact mem_image_of_mem _ h
  have hvN' : ∀ᵐ θ ∂tensorSphereMeasure, frobeniusCoordinateEquiv (v θ) ∈ N.carrierSet :=
    hvN.mono fun θ h => by
      rw [vacuumCompactSmoothEmbeddedTarget_carrierSet]
      exact mem_image_of_mem _ h
  let F (θ : UnitTensorSphere) := frobeniusCoordinateEquiv (u θ)
  let G (θ : UnitTensorSphere) := frobeniusCoordinateEquiv (v θ)
  let A := sphereGradientEnergy u hu + sphereGradientEnergy v hv
  let D := sphereL2DifferenceSq u v
  have hASum :
      (∫ θ : UnitTensorSphere, ∑ i : Fin 3,
        (‖StratificationTheory.sphereGradient (by decide : 2 ≤ 3) F hu i θ‖ ^ 2 +
          ‖StratificationTheory.sphereGradient (by decide : 2 ≤ 3) G hv i θ‖ ^ 2)
        ∂tensorSphereMeasure) = A := by
    simp only [Finset.sum_add_distrib]
    rw [integral_add]
    · rfl
    · exact integrable_finsetSum Finset.univ fun i _ =>
        (Lp.memLp (StratificationTheory.sphereGradient (by decide : 2 ≤ 3) F hu i)).integrable_norm_pow
          (by decide : (2 : ℕ) ≠ 0)
    · exact integrable_finsetSum Finset.univ fun i _ =>
        (Lp.memLp (StratificationTheory.sphereGradient (by decide : 2 ≤ 3) G hv i)).integrable_norm_pow
          (by decide : (2 : ℕ) ≠ 0)
  have hDSq : (∫ θ : UnitTensorSphere, ‖G θ - F θ‖ ^ 2 ∂tensorSphereMeasure) = D := by
    apply integral_congr_ae
    exact Eventually.of_forall fun θ => by
      change ‖frobeniusCoordinateEquiv (v θ) - frobeniusCoordinateEquiv (u θ)‖ ^ 2 =
        ‖u θ - v θ‖ ^ 2
      rw [← map_sub, frobeniusCoordinateEquiv.norm_map, norm_sub_rev]
  have hScalar := ordinary_luckhaus_scalar_estimates
    (add_nonneg (nonneg_sphereGradientEnergy u hu) (nonneg_sphereGradientEnergy v hv))
    hGrad (nonneg_sphereL2DifferenceSq u v) hDiff hB hL hℓ hℓsmall
  have hℓsq : ℓ ^ 2 ≤ d := by
    have h1 : ℓ ≤ 1 := by linarith only [hℓsmall]
    exact (by nlinarith only [mul_nonneg hℓ.le (sub_nonneg.mpr h1)] : ℓ ^ 2 ≤ ℓ).trans
      (hℓδ.le.trans (min_le_right _ _))
  have hTube :
      L * η ^ (1 - (3 : ℤ)) * Real.sqrt A * Real.sqrt D + L * η ^ (-(3 : ℤ)) * D < ρ ^ 2 :=
    hScalar.1.trans_lt ((mul_le_mul_of_nonneg_left hℓsq (by positivity)).trans_lt hdSmall)
  have hAnn := hConnector R η hR hη hηsmall F G hu hv huN' hvN'
  dsimp only at hAnn
  rw [hASum, hDSq] at hAnn
  obtain ⟨w, Dw, K, hw, hwN, hE, hK, hKI, hKO, _⟩ := hAnn hTube
  have hRadius : R / (1 + η) = (1 - ℓ) * R := by
    dsimp only [η]
    have hℓne : 1 - ℓ ≠ 0 := by linarith only [hℓsmall]
    have hden : 1 + ℓ / (1 - ℓ) = (1 - ℓ)⁻¹ := by field_simp; ring
    rw [hden, div_inv_eq_mul, mul_comm]
  let r := (1 - ℓ) * R
  have hrR : r ≤ R := by dsimp only [r]; nlinarith only [mul_pos hR hℓ]
  let V : HarmonicMaps.OpenDomain 3 := ⟨radialAnnulus 0 r R, isOpen_radialAnnulus 0 r R⟩
  have hVSet : V.val = {x : Point | r < ‖x‖ ∧ ‖x‖ < R} := by
    change {x : Point | r < ‖x - 0‖ ∧ ‖x - 0‖ < R} = _
    simp only [sub_zero]
  let z (x : Point) := frobeniusCoordinateEquiv.symm (w x)
  let J (x : Point) (i : Fin 3) := frobeniusCoordinateEquiv.symm (Dw x i)
  have hz : frobeniusField z = w := funext fun x => frobeniusCoordinateEquiv.apply_symm_apply _
  have hJ : frobeniusGradient J = Dw := funext fun x => funext fun i =>
    frobeniusCoordinateEquiv.apply_symm_apply _
  have hwV : HarmonicMaps.MemW12 V w Dw := by
    have hDomain : V = ⟨{x : Point | r < ‖x‖ ∧ ‖x‖ < R},
        isOpen_Ioo.preimage continuous_norm⟩ := Subtype.ext hVSet
    rw [hDomain, show r = R / (1 + η) from hRadius.symm]
    exact hw
  have hTrace : ∃ H : RadialL2Trace r R, RepresentsRadialL2Trace 0 z H ∧
      H ⟨r, le_rfl, hrR⟩ = hu.1.toLp F ∧ H ⟨R, hrR, le_rfl⟩ = hv.1.toLp G := by
    have he : ∃ H : RadialL2Trace (R / (1 + η)) R,
        (∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (R / (1 + η)) R,
          ∃ hslice : MemLp (fun θ : UnitTensorSphere => w (t • θ.val)) 2 tensorSphereMeasure,
            H ⟨t, ht.1.le, ht.2.le⟩ = hslice.toLp (fun θ => w (t • θ.val))) ∧
        ∃ hle : R / (1 + η) ≤ R,
          H ⟨R / (1 + η), le_rfl, hle⟩ = hu.1.toLp F ∧ H ⟨R, hle, le_rfl⟩ = hv.1.toLp G :=
      ⟨K, hK, hRadius.le.trans hrR, hKI, hKO⟩
    rw [hRadius] at he
    obtain ⟨H, hH, _, hI, hO⟩ := he
    refine ⟨H, ?_, hI, hO⟩
    unfold RepresentsRadialL2Trace
    dsimp only
    rw [hz]
    simp only [zero_add]
    exact hH
  obtain ⟨H, hH, hI, hO⟩ := hTrace
  let W : SphereAnnularLayer r R hrR u v hu hv :=
    ⟨z, J, (memH1_iff_memW12 V _ _).mpr (by simpa only [hz, hJ] using hwV), H, hH, hI, hO⟩
  refine ⟨W, ?_, ?_⟩
  · have hNV : ∀ᵐ x ∂volume.restrict V.val, w x ∈ N.carrierSet := by
      rw [hVSet, show r = R / (1 + η) from hRadius.symm]
      exact hwN
    exact hNV.mono fun x hx => (mem_vacuumCompactSmoothEmbeddedTarget_iff.mp hx)
  · have hInt : Integrable (fun x => HarmonicMaps.hsNormSq (Dw x)) (volume.restrict V.val) :=
      HarmonicMaps.integrable_hsNormSq_of_memLp_columns hwV.2.2
    have hE' : (∫ x in V.val, HarmonicMaps.hsNormSq (Dw x)) ≤ 24 * L * B * R * ℓ := by
      have hb : (∫ x in V.val, HarmonicMaps.hsNormSq (Dw x)) ≤ 8 * L * R * (η * A + η⁻¹ * D) := by
        rw [hVSet, show r = R / (1 + η) from hRadius.symm]
        simpa only [show (3 : ℕ) - 2 = 1 by decide, pow_one] using hE
      exact hb.trans ((mul_le_mul_of_nonneg_left hScalar.2 (by positivity)).trans_eq (by ring))
    change dirichletEnergy V.val J ≤ _
    rw [dirichletEnergy_eq_half_upstream, hJ, HarmonicMaps.dirichletEnergy_eq_ofReal_integral hInt]
    calc
      _ ≤ ENNReal.ofReal (∫ x in V.val, HarmonicMaps.hsNormSq (Dw x)) := by
        simpa only [one_mul] using mul_le_mul_left
          (show ENNReal.ofReal (1 / 2 : ℝ) ≤ 1 by norm_num) _
      _ ≤ _ := ENNReal.ofReal_le_ofReal hE'

private def restrict_trace {a b a' b' : ℝ} (H : RadialL2Trace a b)
    (ha : a ≤ a') (hb : b' ≤ b) : RadialL2Trace a' b' :=
  H.comp ⟨fun t => ⟨t.val, ha.trans t.property.1, t.property.2.trans hb⟩,
    continuous_subtype_val.subtype_mk _⟩

private theorem represents_restrict_trace {a b a' b' : ℝ} {u : Point → S0}
    {H : RadialL2Trace a b} (hH : RepresentsRadialL2Trace 0 u H) (ha : a ≤ a') (hb : b' ≤ b) :
    RepresentsRadialL2Trace 0 u (restrict_trace H ha hb) := by
  unfold RepresentsRadialL2Trace at *
  filter_upwards [hH] with t ht ht'
  exact ht ⟨ha.trans_lt ht'.1, ht'.2.trans_le hb⟩

private theorem glued_radial_trace {a r b : ℝ} (ha : 0 < a) (har : a < r) (hrb : r < b)
    (u v : Point → S0) (H : RadialL2Trace a r) (K : RadialL2Trace r b)
    (hH : RepresentsRadialL2Trace 0 u H) (hK : RepresentsRadialL2Trace 0 v K)
    (hEq : H ⟨r, har.le, le_rfl⟩ = K ⟨r, le_rfl, hrb.le⟩) :
    ∃ J : RadialL2Trace a b,
      RepresentsRadialL2Trace 0 (fun x => if ‖x - (0 : Point)‖ < r then u x else v x) J ∧
      J ⟨a, le_rfl, (har.trans hrb).le⟩ = H ⟨a, le_rfl, har.le⟩ ∧
      J ⟨b, (har.trans hrb).le, le_rfl⟩ = K ⟨b, hrb.le, le_rfl⟩ := by
  obtain ⟨J, hLeft, hRight, hJ⟩ := StratificationTheory.exists_radial_trace_piecewise
    (0 : Point) tensorSphereMeasure ha har hrb (frobeniusField u) (frobeniusField v) H K hH hK hEq
  refine ⟨J, ?_, hLeft ⟨a, le_rfl, har.le⟩, hRight ⟨b, hrb.le, le_rfl⟩⟩
  have hPoint :
      frobeniusField (fun x => if ‖x - (0 : Point)‖ < r then u x else v x) =
      fun x => if ‖x - (0 : Point)‖ < r then frobeniusField u x else frobeniusField v x := by
    funext x
    simp only [frobeniusField]
    split_ifs <;> rfl
  unfold RepresentsRadialL2Trace
  dsimp only
  rw [hPoint]
  exact hJ

private theorem memH1_radial_ball_annulus {r s : ℝ} (hr : 0 < r) (hrs : r < s)
    (u v : Point → S0) (D G : Point → Gradient)
    (hu : MemH1 (ball 0 r) u D) (hv : MemH1 (radialAnnulus 0 r s) v G)
    (H : RadialL2Trace (r / 2) r) (K : RadialL2Trace r s)
    (hH : RepresentsRadialL2Trace 0 u H) (hK : RepresentsRadialL2Trace 0 v K)
    (hEq : H ⟨r, by linarith only [hr], le_rfl⟩ = K ⟨r, le_rfl, hrs.le⟩) :
    MemH1 (ball 0 s) (fun x => if ‖x - (0 : Point)‖ < r then u x else v x)
      (fun x i => if ‖x - (0 : Point)‖ < r then D x i else G x i) := by
  let B := HarmonicMaps.ballDomain (0 : Point) r
  let A : HarmonicMaps.OpenDomain 3 := ⟨radialAnnulus 0 r s, isOpen_radialAnnulus 0 r s⟩
  let Br := HarmonicMaps.ballDomain (0 : Point) s
  have hMiddle : (r + s) / 2 ≤ s := by linarith only [hrs]
  let K' := restrict_trace K (le_refl r) hMiddle
  have hK' := represents_restrict_trace hK (le_refl r) hMiddle
  obtain ⟨hW, _⟩ := StratificationTheory.memW12_radial_trace_gluing (by decide : 2 ≤ 3)
    (0 : Point) hr hrs (frobeniusField u) (frobeniusField v) (frobeniusGradient D)
    (frobeniusGradient G) ((memH1_iff_memW12 B _ _).1 hu) ((memH1_iff_memW12 A _ _).1 hv)
    H K' hH hK' hEq
  apply (memH1_iff_memW12 Br _ _).2
  have hF : frobeniusField (fun x => if ‖x - (0 : Point)‖ < r then u x else v x) =
      fun x => if ‖x - (0 : Point)‖ < r then frobeniusField u x else frobeniusField v x := by
    funext x
    simp only [frobeniusField]
    split_ifs <;> rfl
  have hJ : frobeniusGradient (fun x i => if ‖x - (0 : Point)‖ < r then D x i else G x i) =
      fun x i => if ‖x - (0 : Point)‖ < r then frobeniusGradient D x i else frobeniusGradient G x i := by
    funext x i
    simp only [frobeniusGradient]
    split_ifs <;> rfl
  simpa only [hF, hJ] using hW

private theorem exists_annular_ball_extension {r s : ℝ} (hr : 0 < r) (hrs : r < s)
    {u v : UnitTensorSphere → S0} {hu : MemSphereH1 u} {hv : MemSphereH1 v}
    (W : SphereAnnularLayer r s hrs.le u v hu hv) :
    ∃ (w : Point → S0) (D : Point → Gradient) (J : RadialL2Trace (r / 2) s),
      MemH1 (ball 0 s) w D ∧ RepresentsRadialL2Trace 0 w J ∧
      J ⟨s, by linarith only [hr, hrs], le_rfl⟩ = hv.1.toLp (fun θ => frobeniusCoordinateEquiv (v θ)) ∧
      ∀ x, r ≤ ‖x - (0 : Point)‖ → w x = W.toFun x ∧ D x = W.gradient x := by
  let F (θ : UnitTensorSphere) := frobeniusCoordinateEquiv (u θ)
  obtain ⟨f, Df, hf, hRad, _, _, _, _⟩ :=
    StratificationTheory.exists_radial_ball_sobolev_extension
      (n := 3) (by decide) F hu hr
  let f₀ (x : Point) := frobeniusCoordinateEquiv.symm (f x)
  let D₀ (x : Point) (j : Fin 3) := frobeniusCoordinateEquiv.symm (Df x j)
  have hf₂ : frobeniusField f₀ = f := funext fun x => frobeniusCoordinateEquiv.apply_symm_apply _
  have hD₂ : frobeniusGradient D₀ = Df := funext fun x => funext fun j =>
    frobeniusCoordinateEquiv.apply_symm_apply _
  have hf₀ : MemH1 (ball 0 r) f₀ D₀ :=
    (memH1_iff_memW12 (HarmonicMaps.ballDomain 0 r) _ _).2 (by simpa only [hf₂, hD₂] using hf)
  let H : RadialL2Trace (r / 2) r := ContinuousMap.const _ (hu.1.toLp F)
  have ha : 0 < r / 2 := half_pos hr
  have har : r / 2 < r := by linarith only [hr]
  have hH : RepresentsRadialL2Trace 0 f₀ H := by
    unfold RepresentsRadialL2Trace
    apply Eventually.of_forall
    intro t ht
    have hEq : (fun θ : UnitTensorSphere => frobeniusField f₀ (0 + t • θ.val)) = F := by
      funext θ
      rw [hf₂, zero_add]
      exact hRad ⟨t, ha.trans ht.1⟩ θ
    let hSlice := hu.1.ae_eq (EventuallyEq.of_eq hEq.symm)
    exact ⟨hSlice, MemLp.toLp_congr hu.1 hSlice (EventuallyEq.of_eq hEq.symm)⟩
  have hEq : H ⟨r, har.le, le_rfl⟩ = W.trace ⟨r, le_rfl, hrs.le⟩ := W.inner_eq.symm
  obtain ⟨J, hJ, _, hJOuter⟩ :=
    glued_radial_trace ha har hrs f₀ W.toFun H W.trace hH W.traceData hEq
  let w (x : Point) := if ‖x - (0 : Point)‖ < r then f₀ x else W.toFun x
  let D (x : Point) (j : Fin 3) := if ‖x - (0 : Point)‖ < r then D₀ x j else W.gradient x j
  refine ⟨w, D, J, memH1_radial_ball_annulus hr hrs _ _ _ _ hf₀ W.sobolev H W.trace
    hH W.traceData hEq, hJ, hJOuter.trans W.outer_eq, ?_⟩
  intro x hx
  constructor
  · exact if_neg (not_lt_of_ge hx)
  · funext j
    exact if_neg (not_lt_of_ge hx)

/-- Adjacent H¹ sphere layers glue to the stated Sobolev annulus and add
their full penalized energies. The inner sphere extension is used to obtain
the weak derivative identity across the common trace. -/
theorem glue_sphere_annular_layers (a : BulkCoefficients) (ε : ElasticScale)
    {l r s : ℝ} (hl : 0 < l) (hlr : l < r) (hrs : r < s)
    {u v w : UnitTensorSphere → S0} {hu : MemSphereH1 u} {hv : MemSphereH1 v} {hw : MemSphereH1 w}
    (U : SphereAnnularLayer l r hlr.le u v hu hv) (V : SphereAnnularLayer r s hrs.le v w hv hw) :
    ∃ W : SphereAnnularLayer l s (hlr.trans hrs).le u w hu hw,
      energy a ε (radialAnnulus 0 l s) W.toFun W.gradient =
        energy a ε (radialAnnulus 0 l r) U.toFun U.gradient +
          energy a ε (radialAnnulus 0 r s) V.toFun V.gradient := by
  obtain ⟨f, D, H, hF, hH, hEndpoint, hOut⟩ := exists_annular_ball_extension hl hlr U
  have hHalf : l / 2 ≤ r / 2 := by linarith only [hlr]
  let H' : RadialL2Trace (r / 2) r := restrict_trace H hHalf le_rfl
  have hH' := represents_restrict_trace hH hHalf (le_refl r)
  have hr : 0 < r := hl.trans hlr
  have hMatch : H' ⟨r, by linarith only [hr], le_rfl⟩ = V.trace ⟨r, le_rfl, hrs.le⟩ :=
    hEndpoint.trans V.inner_eq.symm
  let g (x : Point) := if ‖x - (0 : Point)‖ < r then f x else V.toFun x
  let G (x : Point) (j : Fin 3) := if ‖x - (0 : Point)‖ < r then D x j else V.gradient x j
  have hA : radialAnnulus 0 l s ⊆ ball 0 s := fun _ hx => mem_ball_iff_norm.mpr hx.2
  have hg : MemH1 (radialAnnulus 0 l s) g G :=
    (memH1_radial_ball_annulus hr hrs _ _ _ _ hF V.sobolev H' V.trace hH' V.traceData hMatch).mono hA
  obtain ⟨J, hRaw, hLeft, hRight⟩ :=
    glued_radial_trace hl hlr hrs U.toFun V.toFun U.trace V.trace U.traceData V.traceData
      (U.outer_eq.trans V.inner_eq.symm)
  have hJ : RepresentsRadialL2Trace 0 g J := by
    unfold RepresentsRadialL2Trace at *
    filter_upwards [hRaw] with t ht ht'
    obtain ⟨hLp, hSlice⟩ := ht ht'
    have hEq0 (θ : UnitTensorSphere) :
        ‖(0 : Point) + t • θ.val - 0‖ = t := by
      have hUnit : ‖θ.val‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using θ.property
      rw [zero_add, sub_zero, norm_smul, Real.norm_of_nonneg (hl.trans ht'.1).le, hUnit, mul_one]
    have hEq (θ : UnitTensorSphere) :
        (if ‖(0 : Point) + t • θ.val - 0‖ < r then U.toFun (0 + t • θ.val)
          else V.toFun (0 + t • θ.val)) =
        g (0 + t • θ.val) := by
      dsimp only [g]
      split_ifs with h
      · have hRad : l ≤ ‖(0 : Point) + t • θ.val - 0‖ := by
          rw [hEq0 θ]
          exact ht'.1.le
        exact (hOut _ hRad).1.symm
      · rfl
    let hLp' := hLp.ae_eq (Eventually.of_forall fun θ => congrArg frobeniusCoordinateEquiv (hEq θ))
    exact ⟨hLp', hSlice.trans (MemLp.toLp_congr hLp hLp'
      (Eventually.of_forall fun θ => congrArg frobeniusCoordinateEquiv (hEq θ)))⟩
  let W : SphereAnnularLayer l s (hlr.trans hrs).le u w hu hw :=
    ⟨g, G, hg, J, hJ, hLeft.trans U.inner_eq, hRight.trans V.outer_eq⟩
  refine ⟨W, ?_⟩
  have hPartition : radialAnnulus 0 l s =ᵐ[(volume : Measure Point)]
      (radialAnnulus 0 l r ∪ radialAnnulus 0 r s : Set Point) := by
    filter_upwards [StratificationTheory.ae_norm_sub_ne_radius (0 : Point) hr] with x hx
    apply propext
    refine ⟨fun hx' => ?_, fun h => ?_⟩
    · rcases lt_or_gt_of_ne hx with h | h
      · exact Or.inl ⟨hx'.1, h⟩
      · exact Or.inr ⟨h, hx'.2⟩
    · rcases h with h | h
      · exact ⟨h.1, h.2.trans hrs⟩
      · exact ⟨hlr.trans h.1, h.2⟩
  have hDisjoint : Disjoint (radialAnnulus 0 l r) (radialAnnulus 0 r s) :=
    Set.disjoint_left.mpr fun _ hx hy => (not_lt_of_gt hx.2) hy.1
  have hInner : energy a ε (radialAnnulus 0 l r) g G =
      energy a ε (radialAnnulus 0 l r) U.toFun U.gradient := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem (isOpen_radialAnnulus 0 l r).measurableSet] with x hx
    have h := hOut x hx.1.le
    have hgEq : g x = U.toFun x := (if_pos hx.2).trans h.1
    have hGEq : G x = U.gradient x := funext fun j =>
      (if_pos hx.2).trans (congrFun h.2 j)
    rw [hgEq, hGEq]
  have hOuter : energy a ε (radialAnnulus 0 r s) g G =
      energy a ε (radialAnnulus 0 r s) V.toFun V.gradient := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem (isOpen_radialAnnulus 0 r s).measurableSet] with x hx
    have hgEq : g x = V.toFun x := if_neg hx.1.not_gt
    have hGEq : G x = V.gradient x := funext fun _ => if_neg hx.1.not_gt
    rw [hgEq, hGEq]
  change energy a ε (radialAnnulus 0 l s) g G = _
  unfold energy
  rw [Measure.restrict_congr_set hPartition,
    lintegral_union (isOpen_radialAnnulus 0 r s).measurableSet hDisjoint]
  exact congrArg₂ (· + ·) hInner hOuter

/-- A penalized projection layer followed by an ordinary vacuum layer
gives the exact thickness `h + (1 - h) * ℓ` and a linear energy bound. -/
theorem exists_penalized_two_layer_shell (a : BulkCoefficients) (B : ℝ) (hB : 0 < B) :
    ∃ δ C : ℝ, 0 < δ ∧ δ ≤ 1 / 9 ∧ 0 < C ∧
      ∀ (ε : ElasticScale) (h ℓ : ℝ) (hh : 0 < h) (hh₁ : h < 1) (hℓ : 0 < ℓ) (hℓδ : ℓ < δ)
        (u p v : UnitTensorSphere → S0) (hu : MemSphereH1 u) (hp : MemSphereH1 p) (hv : MemSphereH1 v),
        (∀ᵐ θ ∂tensorSphereMeasure, p θ ∈ vacuum a) →
        (∀ᵐ θ ∂tensorSphereMeasure, v θ ∈ vacuum a) →
        sphereGradientEnergy v hv + sphereGradientEnergy p hp ≤ B →
        sphereL2DifferenceSq v p ≤ B * ℓ ^ 8 →
        ∀ (W₁ : SphereAnnularLayer (1 - h) 1 (by linarith only [hh]) p u hp hu)
          (C₁ : ℝ), 0 ≤ C₁ →
          energy a ε (radialAnnulus 0 (1 - h) 1) W₁.toFun W₁.gradient ≤ ENNReal.ofReal (C₁ * h) →
          let ν := h + (1 - h) * ℓ
          0 < ν ∧ ν < 1 ∧ ∃ hRadius : 1 - ν ≤ 1,
            ∃ W : SphereAnnularLayer (1 - ν) 1 hRadius v u hv hu,
              energy a ε (radialAnnulus 0 (1 - ν) 1) W.toFun W.gradient ≤
                ENNReal.ofReal (max C C₁ * ν) := by
  obtain ⟨δ, C, hδ, hδsmall, hC, hInner⟩ := exists_ordinary_vacuum_annular_layer a B hB
  refine ⟨δ, C, hδ, hδsmall, hC, ?_⟩
  intro ε h ℓ hh hh₁ hℓ hℓδ u p v hu hp hv hpN hvN hGrad hGap W₁ C₁ hC₁ hE₁ ν
  let R : ℝ := 1 - h
  let r : ℝ := (1 - ℓ) * R
  have hR : 0 < R := sub_pos.mpr hh₁
  have hR₁ : R < 1 := by dsimp only [R]; linarith only [hh]
  have hℓ₁ : ℓ < 1 := hℓδ.trans_le (hδsmall.trans (by norm_num))
  have hr : 0 < r := mul_pos (sub_pos.mpr hℓ₁) hR
  have hrR : r < R :=
    (mul_lt_mul_of_pos_right (by linarith only [hℓ] : 1 - ℓ < 1) hR).trans_eq (one_mul R)
  have hRadius : r = 1 - ν := by dsimp only [r, R, ν]; ring
  have hν : 0 < ν := by dsimp only [ν]; positivity
  have hν₁ : ν < 1 := by rw [hRadius] at hr; linarith
  obtain ⟨W₂, hW₂N, hE₂⟩ := hInner R ℓ hR hℓ hℓδ v p hv hp hvN hpN hGrad hGap
  obtain ⟨W, hW⟩ := glue_sphere_annular_layers a ε hr hrR hR₁ W₂ W₁
  have hE : energy a ε (radialAnnulus 0 r 1) W.toFun W.gradient ≤
      ENNReal.ofReal (max C C₁ * ν) := by
    rw [hW, energy_eq_dirichlet_of_takesVacuumValues a ε W₂.gradient hW₂N]
    calc
      _ ≤ ENNReal.ofReal (C * R * ℓ) + ENNReal.ofReal (C₁ * h) := add_le_add hE₂ hE₁
      _ = ENNReal.ofReal (C * R * ℓ + C₁ * h) :=
        (ENNReal.ofReal_add (by positivity) (by positivity)).symm
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        have hA : C * R * ℓ ≤ max C C₁ * R * ℓ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hR.le) hℓ.le
        have hB' : C₁ * h ≤ max C C₁ * h := mul_le_mul_of_nonneg_right (le_max_right _ _) hh.le
        dsimp only [R, ν] at *
        linarith only [hA, hB']
  have hResult : ∃ hle : r ≤ 1, ∃ V : SphereAnnularLayer r 1 hle v u hv hu,
      energy a ε (radialAnnulus 0 r 1) V.toFun V.gradient ≤ ENNReal.ofReal (max C C₁ * ν) :=
    ⟨(hrR.trans hR₁).le, W, hE⟩
  rw [hRadius] at hResult
  exact ⟨hν, hν₁, hResult⟩

/-- The prescribed thickness of the penalized outer layer. -/
@[expose] def projectionShellThickness (ε : ElasticScale) : ℝ :=
  Real.sqrt (ε : ℝ) * Real.log ((ε : ℝ)⁻¹)

/-- The fraction of the remaining radius used by the ordinary layer. -/
@[expose] def ordinaryShellFraction (ε : ElasticScale) (σ : ℝ) : ℝ :=
  (Real.sqrt (projectionShellThickness ε) + σ) ^ (1 / 4 : ℝ)

/-- The full thickness in Proposition Luckhaus2. -/
@[expose] def penalizedShellThickness (ε : ElasticScale) (σ : ℝ) : ℝ :=
  projectionShellThickness ε + (1 - projectionShellThickness ε) * ordinaryShellFraction ε σ

theorem projectionShellThickness_pos (ε : ElasticScale) : 0 < projectionShellThickness ε :=
  mul_pos (Real.sqrt_pos.2 ε.property.1)
    (Real.log_pos ((one_lt_inv₀ ε.property.1).2 ε.property.2))

theorem tendsto_projectionShellThickness {ι : Type*} {l : Filter ι}
    (ε : ι → ElasticScale) (hε : Tendsto (fun i => (ε i : ℝ)) l (𝓝 0)) :
    Tendsto (fun i => projectionShellThickness (ε i)) l (𝓝 0) := by
  have hRight : Tendsto (fun i => (ε i : ℝ)) l (𝓝[>] 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hε
      (Eventually.of_forall fun i => (ε i).property.1)
  have h := ((tendsto_log_mul_rpow_nhdsGT_zero (by norm_num : 0 < (1 / 2 : ℝ))).comp hRight).neg
  simpa only [Function.comp_def, neg_zero, projectionShellThickness, Real.log_inv, Real.sqrt_eq_rpow,
    mul_neg, mul_comm] using h

theorem tendsto_ordinaryShellFraction {ι : Type*} {l : Filter ι}
    (ε : ι → ElasticScale) (σ : ι → ℝ)
    (hε : Tendsto (fun i => (ε i : ℝ)) l (𝓝 0)) (hσ : Tendsto σ l (𝓝 0)) :
    Tendsto (fun i => ordinaryShellFraction (ε i) (σ i)) l (𝓝 0) := by
  have h : Tendsto (fun i => Real.sqrt (projectionShellThickness (ε i)) + σ i) l (𝓝 0) := by
    simpa only [Real.sqrt_zero, zero_add] using ((tendsto_projectionShellThickness ε hε).sqrt.add hσ)
  simpa only [ordinaryShellFraction, Real.zero_rpow (by norm_num : (1 / 4 : ℝ) ≠ 0)] using
    h.rpow_const (Or.inr (by norm_num : 0 ≤ (1 / 4 : ℝ)))

theorem tendsto_penalizedShellThickness {ι : Type*} {l : Filter ι}
    (ε : ι → ElasticScale) (σ : ι → ℝ)
    (hε : Tendsto (fun i => (ε i : ℝ)) l (𝓝 0)) (hσ : Tendsto σ l (𝓝 0)) :
    Tendsto (fun i => penalizedShellThickness (ε i) (σ i)) l (𝓝 0) := by
  have h := tendsto_projectionShellThickness ε hε
  simpa only [penalizedShellThickness, sub_zero, mul_zero, zero_add] using
    h.add ((tendsto_const_nhds (x := (1 : ℝ))).sub h |>.mul (tendsto_ordinaryShellFraction ε σ hε hσ))

/-- The integral of the scaled bulk density on the unit sphere. -/
@[expose] def sphereScaledBulkEnergy (a : BulkCoefficients) (ε : ElasticScale) (u : UnitTensorSphere → S0) : ℝ :=
  ∫ θ : UnitTensorSphere, (ε : ℝ)⁻¹ ^ 2 * bulkPotential a (u θ) ∂tensorSphereMeasure

@[expose] def spherePenalizedEnergy (a : BulkCoefficients) (ε : ElasticScale)
    (u : UnitTensorSphere → S0) (hu : MemSphereH1 u) : ℝ :=
  (1 / 2 : ℝ) * sphereGradientEnergy u hu + sphereScaledBulkEnergy a ε u

@[expose] def sphereShellBudget (a : BulkCoefficients) (ε : ElasticScale) (σ : ℝ)
    (u v : UnitTensorSphere → S0) (hu : MemSphereH1 u) (hv : MemSphereH1 v) : ℝ :=
  sphereGradientEnergy u hu + sphereScaledBulkEnergy a ε u + sphereGradientEnergy v hv +
    σ⁻¹ ^ 2 * sphereL2DifferenceSq u v

/-- The projection-layer conclusion of Luckhauslemma, with its simultaneous
vacuum trace, annular trace, tangential bound, energy bound and mismatch bound.
The last inequality is the squared form of its L² estimate. -/
@[expose] def HasPenalizedProjectionLayer (a : BulkCoefficients) : Prop :=
  ∀ C₀ : ℝ, 0 < C₀ → ∃ η₁ ε₁ C : ℝ,
    η₁ ∈ Ioo 0 1 ∧ ε₁ ∈ Ioo 0 1 ∧ 0 < C ∧
    ∀ (η : ℝ), η ∈ Ioo 0 η₁ →
      ∀ (ε : ElasticScale), (ε : ℝ) < ε₁ →
        ∀ (u : UnitTensorSphere → S0) (hu : MemSphereH1 u),
          (∀ᵐ θ ∂tensorSphereMeasure, ‖u θ‖ ≤ C₀) →
          spherePenalizedEnergy a ε u hu ≤ η * Real.log ((ε : ℝ)⁻¹) →
          ∃ (p : UnitTensorSphere → S0) (hp : MemSphereH1 p),
            (∀ᵐ θ ∂tensorSphereMeasure, p θ ∈ vacuum a) ∧
            (1 / 2 : ℝ) * sphereGradientEnergy p hp ≤ C * spherePenalizedEnergy a ε u hu ∧
            sphereL2DifferenceSq u p ≤ C ^ 2 * projectionShellThickness ε * spherePenalizedEnergy a ε u hu ∧
            ∃ hRadius : 1 - projectionShellThickness ε ≤ 1,
              ∃ W : SphereAnnularLayer (1 - projectionShellThickness ε) 1 hRadius p u hp hu,
                energy a ε (radialAnnulus 0 (1 - projectionShellThickness ε) 1) W.toFun W.gradient ≤
                  ENNReal.ofReal (C * projectionShellThickness ε * spherePenalizedEnergy a ε u hu)

theorem nonneg_sphereScaledBulkEnergy (a : BulkCoefficients) (ε : ElasticScale)
    (u : UnitTensorSphere → S0) : 0 ≤ sphereScaledBulkEnergy a ε u :=
  integral_nonneg fun _ => mul_nonneg (sq_nonneg _) (bulkPotential_nonneg a _)

private theorem sphereShellBudget_bounds (a : BulkCoefficients) (ε : ElasticScale) {σ C : ℝ}
    (hσ : 0 < σ) {u v : UnitTensorSphere → S0} {hu : MemSphereH1 u} {hv : MemSphereH1 v}
    (hBudget : sphereShellBudget a ε σ u v hu hv ≤ C) :
    spherePenalizedEnergy a ε u hu ≤ C ∧
    sphereGradientEnergy v hv ≤ C ∧ sphereL2DifferenceSq u v ≤ C * σ ^ 2 := by
  have hU := nonneg_sphereGradientEnergy u hu
  have hV := nonneg_sphereGradientEnergy v hv
  have hBulk := nonneg_sphereScaledBulkEnergy a ε u
  have hGap := mul_nonneg (sq_nonneg σ⁻¹) (nonneg_sphereL2DifferenceSq u v)
  unfold sphereShellBudget at hBudget
  refine ⟨?_, ?_, ?_⟩
  · unfold spherePenalizedEnergy
    linarith
  · linarith
  · have h : σ⁻¹ ^ 2 * sphereL2DifferenceSq u v ≤ C := by linarith
    have hp := mul_le_mul_of_nonneg_right h (sq_nonneg σ)
    have hCancel : σ⁻¹ ^ 2 * sphereL2DifferenceSq u v * σ ^ 2 = sphereL2DifferenceSq u v := by
      field_simp
    rwa [hCancel] at hp

private theorem integrable_sphereL2Difference {u v : UnitTensorSphere → S0}
    (hu : MemSphereH1 u) (hv : MemSphereH1 v) :
    Integrable (fun θ => ‖u θ - v θ‖ ^ 2) tensorSphereMeasure := by
  have hU := (frobeniusCoordinateEquiv_memLp_iff tensorSphereMeasure 2 u).mp hu.1
  have hV := (frobeniusCoordinateEquiv_memLp_iff tensorSphereMeasure 2 v).mp hv.1
  exact (hU.sub hV).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)

private theorem sphereL2DifferenceSq_triangle {u p v : UnitTensorSphere → S0}
    (hu : MemSphereH1 u) (hp : MemSphereH1 p) (hv : MemSphereH1 v) :
    sphereL2DifferenceSq v p ≤ 2 * (sphereL2DifferenceSq u p + sphereL2DifferenceSq u v) := by
  unfold sphereL2DifferenceSq
  have hUp := integrable_sphereL2Difference hu hp
  have hUv := integrable_sphereL2Difference hu hv
  calc
    _ ≤ ∫ θ : UnitTensorSphere, 2 * (‖u θ - p θ‖ ^ 2 + ‖u θ - v θ‖ ^ 2) ∂tensorSphereMeasure := by
      apply integral_mono (integrable_sphereL2Difference hv hp) ((hUp.add hUv).const_mul 2)
      intro θ
      change ‖v θ - p θ‖ ^ 2 ≤ 2 * (‖u θ - p θ‖ ^ 2 + ‖u θ - v θ‖ ^ 2)
      have h := dist_triangle (v θ) (u θ) (p θ)
      rw [dist_eq_norm, dist_eq_norm, dist_eq_norm, norm_sub_rev (v θ) (u θ)] at h
      have hs := pow_le_pow_left₀ (norm_nonneg _) h 2
      nlinarith only [hs, sq_nonneg (‖u θ - p θ‖ - ‖u θ - v θ‖)]
    _ = _ := by rw [integral_const_mul, integral_add hUp hUv]

universe u

/-- Proposition Luckhaus2 from the projection-layer lemma. The energy
constant is selected before the scale and mismatch families. -/
theorem eventually_luckhaus2_of_penalizedProjectionLayer
    (a : BulkCoefficients) (hLayer : HasPenalizedProjectionLayer a)
    (C₀ C₁ : ℝ) (hC₀ : 0 < C₀) (hC₁ : 0 < C₁) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {ι : Type u} (l : Filter ι) (ε : ι → ElasticScale) (σ : ι → ℝ),
        Tendsto (fun i => (ε i : ℝ)) l (𝓝 0) →
        Tendsto σ l (𝓝 0) → (∀ i, 0 < σ i) →
        ∀ (U V : ι → UnitTensorSphere → S0) (hU : ∀ i, MemSphereH1 (U i)) (hV : ∀ i, MemSphereH1 (V i)),
          (∀ i, ∀ᵐ θ ∂tensorSphereMeasure, ‖U i θ‖ ≤ C₀) →
          (∀ i, ∀ᵐ θ ∂tensorSphereMeasure, V i θ ∈ vacuum a) →
          (∀ i, sphereShellBudget a (ε i) (σ i) (U i) (V i) (hU i) (hV i) ≤ C₁) →
          ∀ᶠ i in l,
            let ν := penalizedShellThickness (ε i) (σ i)
            0 < ν ∧ ν < 1 ∧ ∃ hRadius : 1 - ν ≤ 1,
              ∃ W : SphereAnnularLayer (1 - ν) 1 hRadius (V i) (U i) (hV i) (hU i),
                energy a (ε i) (radialAnnulus 0 (1 - ν) 1) W.toFun W.gradient ≤ ENNReal.ofReal (C * ν) := by
  obtain ⟨η₁, ε₁, L, hη₁, hε₁, hL, hProject⟩ := hLayer C₀ hC₀
  let B : ℝ := (2 * L + 1) * C₁ + 2 * (L ^ 2 + 1) * C₁
  have hB : 0 < B := by dsimp only [B]; positivity
  obtain ⟨δ, C, hδ, _, hC, hShell⟩ := exists_penalized_two_layer_shell a B hB
  refine ⟨max C (L * C₁), lt_of_lt_of_le hC (le_max_left _ _), ?_⟩
  intro ι l ε σ hε hσ hσpos U V hU hV hUBound hVac hBudget
  have hη : η₁ / 2 ∈ Ioo 0 η₁ := ⟨half_pos hη₁.1, by linarith only [hη₁.1]⟩
  have hlogScale : 0 < Real.exp (-(C₁ / (η₁ / 2))) := Real.exp_pos _
  filter_upwards [hε.eventually_lt_const hε₁.1, hε.eventually_lt_const hlogScale,
    (tendsto_projectionShellThickness ε hε).eventually_lt_const (by norm_num : (0 : ℝ) < 1),
    (tendsto_ordinaryShellFraction ε σ hε hσ).eventually_lt_const hδ]
    with i hεsmall hεlog hHsmall hℓsmall
  let h := projectionShellThickness (ε i)
  let s := Real.sqrt h + σ i
  let ℓ := ordinaryShellFraction (ε i) (σ i)
  have hh : 0 < h := projectionShellThickness_pos _
  have hs : 0 < s := add_pos (Real.sqrt_pos.2 hh) (hσpos i)
  have hℓ : 0 < ℓ := Real.rpow_pos_of_pos hs _
  have hℓ₈ : ℓ ^ 8 = s ^ 2 := by
    change ((s ^ (1 / 4 : ℝ)) ^ (8 : ℕ)) = s ^ 2
    rw [← Real.rpow_natCast, ← Real.rpow_mul hs.le]
    norm_num [Real.rpow_two]
  let P := spherePenalizedEnergy a (ε i) (U i) (hU i)
  obtain ⟨hP, hDV, hGapU⟩ := sphereShellBudget_bounds a (ε i) (hσpos i) (hBudget i)
  have hLog := Real.log_lt_log (ε i).property.1 hεlog
  rw [Real.log_exp] at hLog
  have hSmallEnergy : P ≤ η₁ / 2 * Real.log ((ε i : ℝ)⁻¹) := by
    rw [Real.log_inv]
    apply hP.trans
    have hAux : C₁ / (η₁ / 2) ≤ -Real.log (ε i : ℝ) := by linarith
    exact (div_le_iff₀ hη.1).mp hAux |>.trans_eq (mul_comm _ _)
  obtain ⟨p, hp, hpN, hDP, hGapP, _, W₁, hCost₁⟩ :=
    hProject (η₁ / 2) hη (ε i) hεsmall (U i) (hU i) (hUBound i) hSmallEnergy
  have hCost : energy a (ε i) (radialAnnulus 0 (1 - h) 1) W₁.toFun W₁.gradient ≤
      ENNReal.ofReal ((L * C₁) * h) := by
    refine hCost₁.trans (ENNReal.ofReal_le_ofReal ?_)
    calc
      _ ≤ L * h * C₁ := mul_le_mul_of_nonneg_left hP (by positivity)
      _ = _ := by ring
  have hDeriv : sphereGradientEnergy (V i) (hV i) + sphereGradientEnergy p hp ≤ B := by
    have h := mul_le_mul_of_nonneg_left hP hL.le
    have hb : 0 ≤ 2 * (L ^ 2 + 1) * C₁ := by positivity
    dsimp only [B, P] at *
    linarith only [h, hDV, hDP, hb]
  have hGap : sphereL2DifferenceSq (V i) p ≤ B * ℓ ^ 8 := by
    have hI : sphereL2DifferenceSq (U i) p ≤ L ^ 2 * h * C₁ :=
      hGapP.trans (mul_le_mul_of_nonneg_left hP (by positivity))
    have hJ := sphereL2DifferenceSq_triangle (hU i) hp (hV i)
    have hhs : h ≤ s ^ 2 := by
      have hS : Real.sqrt h ≤ s := le_add_of_nonneg_right (hσpos i).le
      have hi := pow_le_pow_left₀ (Real.sqrt_nonneg _) hS 2
      rwa [Real.sq_sqrt hh.le] at hi
    have hσs : σ i ^ 2 ≤ s ^ 2 :=
      pow_le_pow_left₀ (hσpos i).le (le_add_of_nonneg_left (Real.sqrt_nonneg _)) 2
    have hB' : 2 * (L ^ 2 + 1) * C₁ ≤ B := by
      dsimp only [B]
      exact le_add_of_nonneg_left (by positivity)
    rw [hℓ₈]
    calc
      _ ≤ 2 * (L ^ 2 * h * C₁ + C₁ * σ i ^ 2) := hJ.trans
        (mul_le_mul_of_nonneg_left (add_le_add hI hGapU) (by norm_num))
      _ ≤ 2 * (L ^ 2 * s ^ 2 * C₁ + C₁ * s ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hhs (sq_nonneg _)) hC₁.le)
          (mul_le_mul_of_nonneg_left hσs hC₁.le)) (by norm_num)
      _ = (2 * (L ^ 2 + 1) * C₁) * s ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hB' (sq_nonneg _)
  exact hShell (ε i) h ℓ hh hHsmall hℓ hℓsmall (U i) p (V i) (hU i) hp (hV i)
    hpN (hVac i) hDeriv hGap W₁ (L * C₁) (by positivity) hCost

/-- The family form of Proposition Luckhaus2. The admissible threshold
may depend on the mismatch family, while the energy constant is fixed first. -/
theorem luckhaus2_of_penalizedProjectionLayer
    (a : BulkCoefficients) (hLayer : HasPenalizedProjectionLayer a)
    (C₀ C₁ : ℝ) (hC₀ : 0 < C₀) (hC₁ : 0 < C₁) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (σ : ElasticScale → ℝ),
        Tendsto σ (comap (fun ε : ElasticScale => (ε : ℝ)) (𝓝[>] 0)) (𝓝 0) →
        (∀ ε, 0 < σ ε) →
        ∀ (U V : ElasticScale → UnitTensorSphere → S0)
          (hU : ∀ ε, MemSphereH1 (U ε)) (hV : ∀ ε, MemSphereH1 (V ε)),
          (∀ ε, ∀ᵐ θ ∂tensorSphereMeasure, ‖U ε θ‖ ≤ C₀) →
          (∀ ε, ∀ᵐ θ ∂tensorSphereMeasure, V ε θ ∈ vacuum a) →
          (∀ ε, sphereShellBudget a ε (σ ε) (U ε) (V ε) (hU ε) (hV ε) ≤ C₁) →
          ∃ ε₁ ∈ Ioo (0 : ℝ) 1, ∀ (ε : ElasticScale), (ε : ℝ) < ε₁ →
            let ν := penalizedShellThickness ε (σ ε)
            0 < ν ∧ ν < 1 ∧ ∃ hRadius : 1 - ν ≤ 1,
              ∃ W : SphereAnnularLayer (1 - ν) 1 hRadius (V ε) (U ε) (hV ε) (hU ε),
                energy a ε (radialAnnulus 0 (1 - ν) 1) W.toFun W.gradient ≤ ENNReal.ofReal (C * ν) := by
  obtain ⟨C, hC, hShell⟩ := eventually_luckhaus2_of_penalizedProjectionLayer.{0} a hLayer C₀ C₁ hC₀ hC₁
  refine ⟨C, hC, ?_⟩
  intro σ hσ hσpos U V hU hV hUBound hVac hBudget
  let e (ε : ElasticScale) := (ε : ℝ)
  let l := comap e (𝓝[>] (0 : ℝ))
  have hε : Tendsto e l (𝓝 0) := map_comap_le.trans nhdsWithin_le_nhds
  have hEvent := hShell l id σ hε hσ hσpos U V hU hV hUBound hVac hBudget
  obtain ⟨b, hb, hB⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp (eventually_comap.mp hEvent)
  let ε₁ := min b (1 / 2 : ℝ)
  have hSmall (ε : ElasticScale) (h : (ε : ℝ) < ε₁) : (ε : ℝ) < b :=
    h.trans_le (min_le_left _ _)
  exact ⟨ε₁, ⟨lt_min hb (by norm_num), (min_le_right _ _).trans_lt (by norm_num)⟩,
    fun ε h => hB ⟨ε.property.1, hSmall ε h⟩ ε rfl⟩

private def firstPotentialFactor (a : BulkCoefficients) (Q : S0) : ℝ :=
  (((Q : Tensor) ^ 2).trace - preferredTraceSq a) *
    Real.sqrt (a.a4 / 4 + a.a6 / 6 * (((Q : Tensor) ^ 2).trace + 2 * preferredTraceSq a))

private def secondPotentialFactor (a : BulkCoefficients) (Q : S0) : ℝ :=
  Real.sqrt (a.a6' / 6) * ((Q : Tensor) ^ 3).trace

/-- The two smooth square factors of the sextic potential. -/
def bulkPotentialFactors (a : BulkCoefficients) (Q : S0) : HarmonicMaps.Ambient 2 :=
  WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then firstPotentialFactor a Q else secondPotentialFactor a Q)

private theorem bulkPotentialFactors_zero (a : BulkCoefficients) (Q : S0) :
    bulkPotentialFactors a Q 0 = firstPotentialFactor a Q := by
  simp [bulkPotentialFactors]

private theorem bulkPotentialFactors_one (a : BulkCoefficients) (Q : S0) :
    bulkPotentialFactors a Q 1 = secondPotentialFactor a Q := by
  simp [bulkPotentialFactors]

theorem bulkPotential_eq_norm_sq_factors (a : BulkCoefficients) (Q : S0) :
    bulkPotential a Q = ‖bulkPotentialFactors a Q‖ ^ 2 := by
  have hα : 0 ≤ a.a4 / 4 + a.a6 / 6 * (((Q : Tensor) ^ 2).trace + 2 * preferredTraceSq a) := by
    have := Q.trace_sq_nonneg
    have := preferredTraceSq_pos a
    have := a.a4_pos
    have := a.a6_pos
    positivity
  have hβ : 0 ≤ a.a6' / 6 := div_nonneg a.a6'_pos.le (by norm_num)
  rw [bulkPotential_factorization, PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two]
  simp only [bulkPotentialFactors_zero, bulkPotentialFactors_one, firstPotentialFactor,
    secondPotentialFactor, Real.norm_eq_abs, sq_abs, mul_pow, Real.sq_sqrt hα, Real.sq_sqrt hβ]

theorem contDiff_bulkPotentialFactors (a : BulkCoefficients) :
    ContDiff ℝ ∞ (bulkPotentialFactors a) := by
  let trace : Tensor →L[ℝ] ℝ := (Matrix.traceLinearMap (Fin 3) ℝ ℝ).toContinuousLinearMap
  have hT : ContDiff ℝ ∞ (fun Q : S0 => trace ((symmetricTraceless.subtypeL Q) ^ 2)) := by fun_prop
  have hC : ContDiff ℝ ∞ (fun Q : S0 => trace ((symmetricTraceless.subtypeL Q) ^ 3)) := by fun_prop
  have hα : ∀ Q : S0,
      0 < a.a4 / 4 + a.a6 / 6 * (trace ((symmetricTraceless.subtypeL Q) ^ 2) + 2 * preferredTraceSq a) := by
    intro Q
    have ht : 0 ≤ trace ((symmetricTraceless.subtypeL Q) ^ 2) := Q.trace_sq_nonneg
    have := a.a4_pos
    have := a.a6_pos
    have := preferredTraceSq_pos a
    positivity
  apply (contDiff_piLp 2).mpr
  intro i
  fin_cases i
  · have hFactor : ContDiff ℝ ∞ (fun Q : S0 => (trace ((symmetricTraceless.subtypeL Q) ^ 2) -
        preferredTraceSq a) * Real.sqrt
          (a.a4 / 4 + a.a6 / 6 * (trace ((symmetricTraceless.subtypeL Q) ^ 2) + 2 * preferredTraceSq a))) :=
      (hT.sub contDiff_const).mul
        ((contDiff_const.add (contDiff_const.mul (hT.add contDiff_const))).sqrt
          (fun Q => (hα Q).ne'))
    change ContDiff ℝ ∞ (fun Q : S0 => bulkPotentialFactors a Q 0)
    simp only [bulkPotentialFactors_zero]
    exact hFactor
  · have hFactor : ContDiff ℝ ∞ (fun Q : S0 => Real.sqrt (a.a6' / 6) *
        trace ((symmetricTraceless.subtypeL Q) ^ 3)) := contDiff_const.mul hC
    change ContDiff ℝ ∞ (fun Q : S0 => bulkPotentialFactors a Q 1)
    simp only [bulkPotentialFactors_one]
    exact hFactor

private def append_potential_coordinates (z : HarmonicMaps.Ambient 5)
    (b : HarmonicMaps.Ambient 2) : HarmonicMaps.Ambient 7 :=
  WithLp.toLp 2 (Fin.addCases (motive := fun _ : Fin (5 + 2) => ℝ) (fun i => z i) (fun i => b i))

private theorem append_potential_left (z : HarmonicMaps.Ambient 5) (b : HarmonicMaps.Ambient 2)
    (i : Fin 5) : append_potential_coordinates z b (Fin.castAdd 2 i) = z i := by
  simp [append_potential_coordinates]

private theorem append_potential_right (z : HarmonicMaps.Ambient 5) (b : HarmonicMaps.Ambient 2)
    (i : Fin 2) : append_potential_coordinates z b (Fin.natAdd 5 i) = b i := by
  simp [append_potential_coordinates]

private theorem contDiff_append_potential {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : E → HarmonicMaps.Ambient 5} {G : E → HarmonicMaps.Ambient 2}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (fun x => append_potential_coordinates (F x) (G x)) := by
  apply (contDiff_piLp 2).mpr
  intro i
  refine Fin.addCases (motive := fun i : Fin (5 + 2) =>
    ContDiff ℝ ∞ (fun x => append_potential_coordinates (F x) (G x) i)) ?_ ?_ i
  · intro j
    simpa only [append_potential_left] using (contDiff_piLp 2).mp hF j
  · intro j
    simpa only [append_potential_right] using (contDiff_piLp 2).mp hG j

private theorem norm_sq_append_potential_difference (z : HarmonicMaps.Ambient 5)
    (b : HarmonicMaps.Ambient 2) :
    ‖append_potential_coordinates z 0 - append_potential_coordinates z b‖ ^ 2 = ‖b‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_add (a := 5) (b := 2), PiLp.norm_sq_eq_of_L2]
  simp only [PiLp.sub_apply, append_potential_left, append_potential_right, sub_self, norm_zero,
    zero_pow (by decide : (2 : ℕ) ≠ 0), Finset.sum_const_zero, zero_add, PiLp.zero_apply, zero_sub, norm_neg]

private theorem exists_fderiv_bound_of_compactSupport
    (F : HarmonicMaps.Ambient 5 → HarmonicMaps.Ambient 7)
    (hF : ContDiff ℝ ∞ F) (hCompact : HasCompactSupport F) :
    ∃ L : ℝ, 0 < L ∧ ∀ z, ‖fderiv ℝ F z‖ ≤ L := by
  have hDeriv : HasCompactSupport (fderiv ℝ F) := hCompact.fderiv ℝ
  obtain ⟨L, hL⟩ := hDeriv.exists_bound_of_continuousOn
    (hF.continuous_fderiv (by simp)).continuousOn
  refine ⟨max L 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun z => ?_⟩
  by_cases hz : z ∈ tsupport (fderiv ℝ F)
  · exact (hL z hz).trans (le_max_left _ _)
  · rw [image_eq_zero_of_notMem_tsupport hz, norm_zero]
    exact zero_le_one.trans (le_max_right _ _)

/-- The two smooth maps used for lattice sampling preserve the original
coordinates on the bounded range. Their squared discrepancy measures the
bulk potential of the same input, and both derivatives are globally bounded. -/
theorem exists_smooth_penalized_grid_maps (a : BulkCoefficients) (B : ℝ) (hB : 0 ≤ B) :
    ∃ (F G : HarmonicMaps.Ambient 5 → HarmonicMaps.Ambient 7) (L : ℝ),
      0 < L ∧ ContDiff ℝ ∞ F ∧ ContDiff ℝ ∞ G ∧
      (∀ z, ‖fderiv ℝ F z‖ ≤ L) ∧ (∀ z, ‖fderiv ℝ G z‖ ≤ L) ∧
      ∀ z, ‖z‖ ≤ B →
        (∀ i : Fin 5, F z (Fin.castAdd 2 i) = z i ∧ G z (Fin.castAdd 2 i) = z i) ∧
        ‖F z - G z‖ ^ 2 = bulkPotential a (frobeniusCoordinateEquiv.symm z) := by
  let χ : ContDiffBump (0 : HarmonicMaps.Ambient 5) :=
    ⟨B + 1, B + 2, by linarith, by linarith⟩
  let f (z : HarmonicMaps.Ambient 5) := append_potential_coordinates z 0
  let g (z : HarmonicMaps.Ambient 5) :=
    append_potential_coordinates z (bulkPotentialFactors a (frobeniusCoordinateEquiv.symm z))
  let F (z : HarmonicMaps.Ambient 5) := χ z • f z
  let G (z : HarmonicMaps.Ambient 5) := χ z • g z
  have hInv : ContDiff ℝ ∞ (frobeniusCoordinateEquiv.symm : HarmonicMaps.Ambient 5 → S0) :=
    frobeniusCoordinateEquiv.symm.toContinuousLinearEquiv.toContinuousLinearMap.contDiff
  have hF : ContDiff ℝ ∞ F := χ.contDiff.smul (contDiff_append_potential contDiff_id contDiff_const)
  have hG : ContDiff ℝ ∞ G := χ.contDiff.smul
    (contDiff_append_potential contDiff_id ((contDiff_bulkPotentialFactors a).comp hInv))
  have hFs : HasCompactSupport F := χ.hasCompactSupport.smul_right
  have hGs : HasCompactSupport G := χ.hasCompactSupport.smul_right
  obtain ⟨L₁, hL₁, hf⟩ := exists_fderiv_bound_of_compactSupport F hF hFs
  obtain ⟨L₂, _, hg⟩ := exists_fderiv_bound_of_compactSupport G hG hGs
  refine ⟨F, G, max L₁ L₂, hL₁.trans_le (le_max_left _ _), hF, hG,
    fun z => (hf z).trans (le_max_left _ _), fun z => (hg z).trans (le_max_right _ _), ?_⟩
  intro z hz
  have hχ : χ z = 1 := χ.one_of_mem_closedBall (by
    rw [mem_closedBall, dist_zero_right]
    exact hz.trans (by dsimp only [χ]; linarith))
  have hFz : F z = f z := by simp only [F, hχ, one_smul]
  have hGz : G z = g z := by simp only [G, hχ, one_smul]
  rw [hFz, hGz]
  exact ⟨fun i => ⟨append_potential_left _ _ i, append_potential_left _ _ i⟩,
    (norm_sq_append_potential_difference _ _).trans (bulkPotential_eq_norm_sq_factors a _).symm⟩

/-- The squared intrinsic gradient integral for the native Euclidean
sphere carrier. -/
@[expose] def nativeSphereGradientEnergy {q : ℕ} (u : UnitTensorSphere → HarmonicMaps.Ambient q)
    (hu : StratificationTheory.MemSphereW12 (by decide : 2 ≤ 3) u) : ℝ :=
  ∫ θ : UnitTensorSphere, HarmonicMaps.hsNormSq (fun i =>
    StratificationTheory.sphereGradient (by decide : 2 ≤ 3) u hu i θ) ∂tensorSphereMeasure

private theorem exists_sphere_postcomposition_gradient_bound {q k : ℕ}
    (u : UnitTensorSphere → HarmonicMaps.Ambient q)
    (hu : StratificationTheory.MemSphereW12 (by decide : 2 ≤ 3) u)
    (F : HarmonicMaps.Ambient q → HarmonicMaps.Ambient k) (hF : ContDiff ℝ ∞ F)
    {L : ℝ} (hDF : ∀ z, ‖fderiv ℝ F z‖ ≤ L) :
    ∃ hv : StratificationTheory.MemSphereW12 (by decide : 2 ≤ 3) (F ∘ u),
      nativeSphereGradientEnergy (F ∘ u) hv ≤ L ^ 2 * nativeSphereGradientEnergy u hu := by
  letI : IsFiniteMeasure tensorSphereMeasure := by
    change IsFiniteMeasure
      (Measure.euclideanHausdorffMeasure (3 - 1) : Measure (sphere (0 : Point) 1))
    rw [StratificationTheory.euclideanHausdorffMeasure_unitSphere_eq_toSphere (by decide : 0 < 3)]
    infer_instance
  let Ω : HarmonicMaps.OpenDomain 3 := ⟨({0}ᶜ : Set Point), isOpen_compl_singleton⟩
  obtain ⟨w, Dw, hw, hRad, hRadGrad⟩ :=
    (StratificationTheory.sphereGradient_characterization (by decide : 2 ≤ 3) u hu).1.1
  let W := F ∘ w
  let D (x : Point) (i : Fin 3) := fderiv ℝ F (w x) (Dw x i)
  have hW : HarmonicMaps.MemW12Loc Ω W D := hw.postcompose F hF L hDF
  have hSphere : sphere (0 : Point) 1 ⊆ Ω.val := by
    intro x hx
    change x ≠ 0
    intro hx0
    rw [hx0, mem_sphere, dist_self] at hx
    norm_num at hx
  obtain ⟨V, hVOpen, hSphereV, hCV, hVCompact⟩ :=
    exists_open_between_and_isCompact_closure (isCompact_sphere (0 : Point) 1) Ω.property hSphere
  have hVΩ : V ⊆ Ω.val := subset_closure.trans hCV
  let A : HarmonicMaps.OpenDomain 3 := ⟨V, hVOpen⟩
  have hMeasure := Measure.restrict_mono_set (volume : Measure Point)
    (subset_closure : V ⊆ closure V)
  have hWV : HarmonicMaps.MemW12 A W D :=
    ⟨hW.1.mono hVΩ, (hW.2.1 _ hVCompact hCV).mono_measure hMeasure,
      fun i => (hW.2.2 i _ hVCompact hCV).mono_measure hMeasure⟩
  have hRadW (t : HarmonicMaps.PositiveRadius) (θ : UnitTensorSphere) :
      W (t.val • θ.val) = (F ∘ u) θ :=
    congrArg F (hRad t θ)
  have hv : StratificationTheory.MemSphereW12 (by decide : 2 ≤ 3) (F ∘ u) :=
    ⟨HarmonicMaps.memLp_postcomposition hu.1 hF hDF,
      A, hSphereV, (fun hz => (hVΩ hz) (mem_singleton 0)), W, D, hWV, fun t θ _ => hRadW t θ⟩
  let Grad (i : Fin 3) := StratificationTheory.sphereGradient (by decide : 2 ≤ 3) u hu i
  let G (i : Fin 3) (θ : UnitTensorSphere) := fderiv ℝ F (u θ) (Grad i θ)
  have hG (i : Fin 3) : MemLp (G i) 2 tensorSphereMeasure :=
    HarmonicMaps.memLp_postcomposition_column hu.1.aestronglyMeasurable (Lp.memLp (Grad i)) hF hDF
  let AGrad (i : Fin 3) := (hG i).toLp (G i)
  have hAGrad : AGrad = StratificationTheory.sphereGradient (by decide : 2 ≤ 3) (F ∘ u) hv := by
    apply (StratificationTheory.sphereGradient_characterization (by decide : 2 ≤ 3) (F ∘ u) hv).2.1
    refine ⟨W, D, hW, hRadW, ?_⟩
    intro t i
    filter_upwards [hRadGrad t i, (hG i).coeFn_toLp] with θ hθ hgθ
    change t.val • fderiv ℝ F (w (t.val • θ.val)) (Dw (t.val • θ.val) i) = AGrad i θ
    rw [← map_smul, hRad t θ]
    exact (congrArg (fderiv ℝ F (u θ)) hθ).trans hgθ.symm
  have hAE : ∀ᵐ θ ∂tensorSphereMeasure, ∀ i : Fin 3, AGrad i θ = G i θ :=
    ae_all_iff.mpr fun i => (hG i).coeFn_toLp
  have hDiff : ∀ᵐ θ ∂tensorSphereMeasure,
      HarmonicMaps.hsNormSq (fun i => AGrad i θ) ≤ L ^ 2 * HarmonicMaps.hsNormSq (fun i => Grad i θ) := by
    filter_upwards [hAE] with θ hθ
    simp only [HarmonicMaps.hsNormSq, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [hθ i, ← mul_pow]
    apply pow_le_pow_left₀ (norm_nonneg _)
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (hDF _) (norm_nonneg _))
  have hInt {m : ℕ} (v : Fin 3 → Lp (HarmonicMaps.Ambient m) 2 tensorSphereMeasure) :
      Integrable (fun θ => HarmonicMaps.hsNormSq (fun i => v i θ)) tensorSphereMeasure :=
    integrable_finsetSum Finset.univ fun i _ => (Lp.memLp (v i)).integrable_norm_pow
      (by decide : (2 : ℕ) ≠ 0)
  refine ⟨hv, ?_⟩
  unfold nativeSphereGradientEnergy
  rw [← hAGrad, ← integral_const_mul]
  exact integral_mono_ae (hInt AGrad) ((hInt Grad).const_mul _) hDiff

/-- A bounded tensor sphere map supplies a compact-range Sobolev pair for
`StratificationTheory.exists_sphere_pair_original_closed_target_face_grid`.
Its original coordinates, gradient channel and potential discrepancy refer
to the same tensor map and sphere measure. -/
theorem exists_sphere_pair_penalized_grid_channels (a : BulkCoefficients) (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : UnitTensorSphere → S0) (hu : MemSphereH1 u),
      (∀ᵐ θ ∂tensorSphereMeasure, ‖u θ‖ ≤ B) →
      ∃ (v : UnitTensorSphere → S0) (hv : MemSphereH1 v),
        u =ᵐ[tensorSphereMeasure] v ∧ (∀ θ, ‖v θ‖ ≤ B) ∧
        sphereGradientEnergy v hv = sphereGradientEnergy u hu ∧
        ∃ (N : Set (HarmonicMaps.Ambient 7)) (P : Fin 2 → UnitTensorSphere → HarmonicMaps.Ambient 7)
          (hP : ∀ j, StratificationTheory.MemSphereW12 (by decide : 2 ≤ 3) (P j)),
          IsCompact N ∧ (∀ j θ, P j θ ∈ N) ∧
          (∀ θ (j : Fin 2) (i : Fin 5),
            P j θ (Fin.castAdd 2 i) = frobeniusCoordinateEquiv (v θ) i) ∧
          (∀ θ, ‖P 0 θ - P 1 θ‖ ^ 2 = bulkPotential a (v θ)) ∧
          nativeSphereGradientEnergy (P 0) (hP 0) + nativeSphereGradientEnergy (P 1) (hP 1) ≤
            C * sphereGradientEnergy u hu := by
  obtain ⟨F, G, L, hL, hF, hG, hDF, hDG, hRange⟩ := exists_smooth_penalized_grid_maps a B hB
  refine ⟨2 * L ^ 2, by positivity, ?_⟩
  intro u hu hU
  let v (θ : UnitTensorSphere) := if ‖u θ‖ ≤ B then u θ else 0
  have hvEq : u =ᵐ[tensorSphereMeasure] v := hU.mono fun θ hθ => (if_pos hθ).symm
  have hvBound (θ : UnitTensorSphere) : ‖v θ‖ ≤ B := by
    dsimp only [v]
    split_ifs with hθ
    · exact hθ
    · simpa only [norm_zero] using hB
  let φ (θ : UnitTensorSphere) := frobeniusCoordinateEquiv (v θ)
  have hAE : (fun θ => frobeniusCoordinateEquiv (u θ)) =ᵐ[tensorSphereMeasure] φ :=
    hvEq.mono fun θ hθ => congrArg frobeniusCoordinateEquiv hθ
  have hv : MemSphereH1 v :=
    StratificationTheory.memSphereW12_congr_ae (by decide : 2 ≤ 3) hu hAE
  have hGrad := (StratificationTheory.sphereGradient_characterization (by decide : 2 ≤ 3)
    (fun θ => frobeniusCoordinateEquiv (u θ)) hu).2.2 φ hv hAE
  have hvEnergy : sphereGradientEnergy v hv = sphereGradientEnergy u hu := by
    unfold sphereGradientEnergy
    rw [hGrad]
  obtain ⟨hPF, hFE⟩ := exists_sphere_postcomposition_gradient_bound φ hv F hF hDF
  obtain ⟨hPG, hGE⟩ := exists_sphere_postcomposition_gradient_bound φ hv G hG hDG
  let K := closedBall (0 : HarmonicMaps.Ambient 5) B
  let N := F '' K ∪ G '' K
  let P (j : Fin 2) := if j = 0 then F ∘ φ else G ∘ φ
  have hP : ∀ j, StratificationTheory.MemSphereW12 (by decide : 2 ≤ 3) (P j) := by
    intro j
    unfold P
    split_ifs
    · exact hPF
    · exact hPG
  have hN : IsCompact N :=
    ((isCompact_closedBall _ _).image hF.continuous).union ((isCompact_closedBall _ _).image hG.continuous)
  have hVK (θ : UnitTensorSphere) : φ θ ∈ K := by
    change φ θ ∈ closedBall (0 : HarmonicMaps.Ambient 5) B
    rw [mem_closedBall, dist_zero_right, frobeniusCoordinateEquiv.norm_map]
    exact hvBound θ
  refine ⟨v, hv, hvEq, hvBound, hvEnergy, N, P, hP, hN, ?_, ?_, ?_, ?_⟩
  · intro j θ
    by_cases hj : j = 0
    · exact Or.inl ⟨φ θ, hVK θ, by simp only [P, if_pos hj, Function.comp_apply]⟩
    · exact Or.inr ⟨φ θ, hVK θ, by simp only [P, if_neg hj, Function.comp_apply]⟩
  · intro θ j i
    have hθ' : ‖φ θ‖ ≤ B := (frobeniusCoordinateEquiv.norm_map (v θ)).trans_le (hvBound θ)
    obtain ⟨hCoords, _⟩ := hRange (φ θ) hθ'
    unfold P
    split_ifs
    · exact (hCoords i).1
    · exact (hCoords i).2
  · intro θ
    have hθ' : ‖φ θ‖ ≤ B := (frobeniusCoordinateEquiv.norm_map (v θ)).trans_le (hvBound θ)
    simpa only [P, if_pos rfl, if_neg (by decide : (1 : Fin 2) ≠ 0), φ, Function.comp_apply,
      LinearIsometryEquiv.symm_apply_apply] using (hRange (φ θ) hθ').2
  · have h₀ : P 0 = F ∘ φ := by simp only [P, if_pos rfl]
    have h₁ : P 1 = G ∘ φ := by simp only [P, if_neg (by decide : (1 : Fin 2) ≠ 0)]
    have hFW : nativeSphereGradientEnergy (P 0) (hP 0) ≤ L ^ 2 * nativeSphereGradientEnergy φ hv := by
      simpa only [h₀] using hFE
    have hGW : nativeSphereGradientEnergy (P 1) (hP 1) ≤ L ^ 2 * nativeSphereGradientEnergy φ hv := by
      simpa only [h₁] using hGE
    have hEq : nativeSphereGradientEnergy φ hv = sphereGradientEnergy v hv := rfl
    rw [hvEnergy] at hEq
    rw [← hEq]
    linarith only [hFW, hGW]

end Thesis
end
end
