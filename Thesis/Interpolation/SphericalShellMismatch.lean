module

public import Thesis.Interpolation.SphericalShellCapTrace
public import Thesis.Interpolation.SphericalShellBudgets
import StratificationTheory.Foundation.CoordinateRectangleTrace
import StratificationTheory.Foundation.CoordinateL2Trace
import StratificationTheory.Foundation.BanachIntervalWeakRepresentative
import StratificationTheory.Foundation.CubicalConeGeometry
import StratificationTheory.Foundation.CylinderRawTime

/-! Endpoint difference bounds for the actual cap traces of the shell. -/

public section

open Filter HarmonicMaps MeasureTheory Metric Set
open scoped ContDiff ENNReal Topology Matrix.Norms.Frobenius

namespace Thesis

private theorem lp_endpoint_norm_sq_le_of_weakProduct {X : Type*} [MeasurableSpace X] {q : ℕ}
    (σ : Measure X) [IsFiniteMeasure σ] [IsSeparable σ] {a b : ℝ} (hab : a < b)
    {f g : X × ℝ → Ambient q}
    (hF : MemLp f 2 (σ.prod (volume.restrict (Icc a b))))
    (hG : MemLp g 2 (σ.prod (volume.restrict (Icc a b))))
    (hWeak : ∀ (φ : ℝ → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ioo a b →
      ∀ᵐ x ∂σ, (∫ t in Icc a b, deriv φ t • f (x, t)) = -(∫ t in Icc a b, φ t • g (x, t)))
    (H : C(Icc a b, Lp (Ambient q) 2 σ))
    (hH : ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo a b,
      ∃ hs : MemLp (fun x => f (x, t)) 2 σ, H ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp _) :
    ‖H ⟨b, hab.le, le_rfl⟩ - H ⟨a, le_rfl, hab.le⟩‖ ^ 2 ≤
      (b - a) * ∫ p : X × ℝ, ‖g p‖ ^ 2 ∂(σ.prod (volume.restrict (Icc a b))) := by
  let ν := volume.restrict (Ioo a b)
  let νC := volume.restrict (Icc a b)
  have hTime : νC = ν := Measure.restrict_congr_set Ioo_ae_eq_Icc.symm
  obtain ⟨F, G, hFL, hGL, hFs, hGs, hW⟩ :=
    StratificationTheory.exists_finite_lp_two_time_curves_with_weak_identity σ a b hF hG hWeak
  have hFL' : MemLp F 2 ν := hTime ▸ hFL
  have hGL' : MemLp G 2 ν := hTime ▸ hGL
  obtain ⟨K, hK, _⟩ := StratificationTheory.banach_interval_weakDerivative_exists_unique_continuous_representative
    hab hFL' hGL' (fun φ hφ hc hs => (hW φ hφ hc hs).2.2)
  have hFs' : ∀ᵐ t ∂volume, ∀ ht : t ∈ Ioo a b, ∃ hs : MemLp (fun x => f (x, t)) 2 σ, F t = hs.toLp _ := by
    rw [← ae_restrict_iff' measurableSet_Ioo]
    change ∀ᵐ t ∂ν, ∃ hs : MemLp (fun x => f (x, t)) 2 σ, F t = hs.toLp _
    rwa [← hTime]
  have hKs : ∀ᵐ t ∂volume, ∀ ht : t ∈ Ioo a b,
      ∃ hs : MemLp (fun x => f (x, t)) 2 σ, K ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp _ := by
    filter_upwards [hFs', hK.1] with t hFs hKt ht
    obtain ⟨hs, heq⟩ := hFs ht
    exact ⟨hs, (hKt ht).trans heq⟩
  have hHK : H = K := StratificationTheory.continuous_Lp_representatives_eq_of_ae_slices hab H K hH hKs
    (Eventually.of_forall fun _ _ => EventuallyEq.rfl)
  have hNorm : ∀ᵐ t ∂νC, ‖G t‖ ^ 2 = ∫ x, ‖g (x, t)‖ ^ 2 ∂σ := by
    filter_upwards [hGs] with t hGt
    obtain ⟨hs, hGt⟩ := hGt
    rw [hGt, Lp.norm_toLp, ← integral_norm_sq_eq_eLpNorm_two_toReal_sq hs]
  have hIntegrable := hG.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
  have hEnergy : (∫ t in Ioo a b, ‖G t‖ ^ 2) = ∫ p : X × ℝ, ‖g p‖ ^ 2 ∂(σ.prod νC) := by
    calc
      _ = ∫ t, ‖G t‖ ^ 2 ∂νC := by rw [hTime]
      _ = ∫ t, ∫ x, ‖g (x, t)‖ ^ 2 ∂σ ∂νC := integral_congr_ae hNorm
      _ = _ := (integral_prod_symm _ hIntegrable).symm
  rw [hHK]
  have hb := hK.2.2.2.1 ⟨a, le_rfl, hab.le⟩ ⟨b, hab.le, le_rfl⟩
  change ‖K ⟨b, hab.le, le_rfl⟩ - K ⟨a, le_rfl, hab.le⟩‖ ^ 2 ≤ |b - a| * _ at hb
  rwa [abs_of_nonneg (sub_nonneg.mpr hab.le), hEnergy] at hb

private theorem measurePreserving_cellInterfacePoint {n : ℕ} (U : OpenDomain n) (a b : ℝ) :
    MeasurePreserving (fun p : Domain n × ℝ => cellInterfacePoint p.1 p.2)
      (((volume : Measure (Domain n)).restrict U.val).prod (volume.restrict (Ioo a b)))
      (volume.restrict (cellInterfaceSlab U a b).val) := by
  let Ω := cellInterfaceSlab U a b
  let Φ : Domain n × ℝ → Domain (n + 1) := fun p => cellInterfacePoint p.1 p.2
  have hpre : Φ ⁻¹' Ω.val = U.val ×ˢ Ioo a b := by
    ext p
    simp only [Φ, Ω, cellInterfacePoint, cellInterfaceSlab, mem_preimage, mem_prod, mem_setOf_eq,
      ContinuousLinearEquiv.apply_symm_apply, PiLp.single_apply, ite_true]
  have hm := (StratificationTheory.measurePreserving_cylinder_coordinates_inverse n).restrict_preimage Ω.property.measurableSet
  change MeasurePreserving Φ (((volume : Measure (Domain n)).prod (volume : Measure ℝ)).restrict (Φ ⁻¹' Ω.val))
    (volume.restrict Ω.val) at hm
  rw [hpre, ← Measure.prod_restrict] at hm
  exact hm

private theorem cellInterface_raw_time_test {n q : ℕ} (U : OpenDomain n)
    [IsFiniteMeasure ((volume : Measure (Domain n)).restrict U.val)] {a b : ℝ}
    {u : Domain (n + 1) → Ambient q} {D : Domain (n + 1) → HarmonicMaps.Gradient (n + 1) q}
    (hu : MemW12 (cellInterfaceSlab U a b) u D)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ Ioo a b) :
    ∀ᵐ x ∂volume.restrict U.val,
      (∫ t in Icc a b, deriv φ t • u (cellInterfacePoint x t)) =
        -(∫ t in Icc a b, φ t • D (cellInterfacePoint x t) (Fin.natAdd n (0 : Fin 1))) := by
  let σ := (volume : Measure (Domain n)).restrict U.val
  let ν := volume.restrict (Ioo a b)
  let νC := volume.restrict (Icc a b)
  let f : Domain n × ℝ → Ambient q := fun p => u (cellInterfacePoint p.1 p.2)
  let g : Domain n × ℝ → Ambient q := fun p => D (cellInterfacePoint p.1 p.2) (Fin.natAdd n (0 : Fin 1))
  have hTime : νC = ν := Measure.restrict_congr_set Ioo_ae_eq_Icc.symm
  have hUfinite : (volume : Measure (Domain n)) U.val ≠ ⊤ := isFiniteMeasure_restrict.mp inferInstance
  have hE := StratificationTheory.MemW12.cylinder_time_test_ae U hUfinite hu hφ hc hs
  filter_upwards [hE] with x hx
  have hφL : MemLp φ ∞ ν := hφ.continuous.memLp_top_of_hasCompactSupport hc ν
  have hdφL : MemLp (deriv φ) ∞ ν := (hφ.continuous_deriv (by simp)).memLp_top_of_hasCompactSupport hc.deriv ν
  have hLeft : Integrable (fun t => deriv φ t • f (x, t)) ν := hx.1.smul_of_top_right hdφL
  have hRight : Integrable (fun t => φ t • g (x, t)) ν := hx.2.1.smul_of_top_right hφL
  have hId := hx.2.2.2
  change (∫ t, deriv φ t • f (x, t) + φ t • g (x, t) ∂ν) = 0 at hId
  rw [integral_add hLeft hRight] at hId
  change (∫ t, deriv φ t • f (x, t) ∂νC) = -(∫ t, φ t • g (x, t) ∂νC)
  rw [hTime]
  exact eq_neg_iff_add_eq_zero.mpr hId

/-- The two true L² endpoint classes on a native coordinate slab are
controlled by the original full slab Dirichlet integral. -/
theorem cellInterface_endpoint_norm_sq_le {n q : ℕ} (U : OpenDomain n)
    [IsFiniteMeasure ((volume : Measure (Domain n)).restrict U.val)] {a b : ℝ} (hab : a < b)
    {u : Domain (n + 1) → Ambient q} {D : Domain (n + 1) → HarmonicMaps.Gradient (n + 1) q}
    (hu : MemW12 (cellInterfaceSlab U a b) u D)
    (H : C(Icc a b, Lp (Ambient q) 2 (volume.restrict U.val)))
    (hH : ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo a b,
      ∃ hs : MemLp (fun x => u (cellInterfacePoint x t)) 2 (volume.restrict U.val), H ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp _) :
    ‖H ⟨b, hab.le, le_rfl⟩ - H ⟨a, le_rfl, hab.le⟩‖ ^ 2 ≤
      (b - a) * ∫ x in (cellInterfaceSlab U a b).val, hsNormSq (D x) := by
  let Ω := cellInterfaceSlab U a b
  let σ := (volume : Measure (Domain n)).restrict U.val
  let ν := volume.restrict (Ioo a b)
  let νC := volume.restrict (Icc a b)
  let Φ : Domain n × ℝ → Domain (n + 1) := fun p => cellInterfacePoint p.1 p.2
  let j := Fin.natAdd n (0 : Fin 1)
  let f := u ∘ Φ
  let g := fun p => D (Φ p) j
  have hm := measurePreserving_cellInterfacePoint U a b
  have hTime : νC = ν := Measure.restrict_congr_set Ioo_ae_eq_Icc.symm
  have hF : MemLp f 2 (σ.prod νC) := hTime.symm ▸ hu.2.1.comp_measurePreserving hm
  have hG : MemLp g 2 (σ.prod νC) := hTime.symm ▸ (hu.2.2 j).comp_measurePreserving hm
  have hWeak := cellInterface_raw_time_test U hu
  refine (lp_endpoint_norm_sq_le_of_weakProduct σ hab hF hG hWeak H hH).trans ?_
  apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr hab.le)
  let d := fun x => ‖D x j‖ ^ 2
  have hDN : AEStronglyMeasurable d (volume.restrict Ω.val) := (hu.2.2 j).aestronglyMeasurable.norm.pow 2
  have hDMap : AEStronglyMeasurable d (Measure.map Φ (σ.prod ν)) := by
    have hMap : Measure.map Φ (σ.prod ν) = volume.restrict Ω.val := hm.map_eq
    rwa [hMap]
  have hDInt : Integrable d (volume.restrict Ω.val) := (hu.2.2 j).integrable_norm_pow (by decide)
  calc
    _ = ∫ p, d (Φ p) ∂(σ.prod ν) := by
      change (∫ p : Domain n × ℝ, ‖g p‖ ^ 2 ∂(σ.prod νC)) = _
      rw [hTime]
    _ = ∫ x in Ω.val, d x := by
      rw [← integral_map hm.measurable.aemeasurable hDMap]
      exact congrArg (fun μ => ∫ x, d x ∂μ) hm.map_eq
    _ ≤ _ := integral_mono hDInt hu.integrable_hsNormSq (fun x => Finset.single_le_sum
      (f := fun k => ‖D x k‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ j))

private theorem unitCellCube_three_eq_slab : unitCellCube 3 = cellInterfaceSlab (unitCellCube 2) (-1) 1 := by
  apply Subtype.ext
  ext x
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 2) (m := 1)
  constructor
  · intro hx
    change (e x).1 ∈ (unitCellCube 2).val ∧ (e x).2 0 ∈ Ioo (-1 : ℝ) 1
    exact ⟨mem_iInter.mpr (fun i => mem_iInter.mp hx i.castSucc), mem_iInter.mp hx (Fin.last 2)⟩
  · intro hx
    change (e x).1 ∈ (unitCellCube 2).val ∧ (e x).2 0 ∈ Ioo (-1 : ℝ) 1 at hx
    apply mem_iInter.mpr
    intro i
    refine Fin.lastCases ?_ (fun k => ?_) i
    · exact hx.2
    · exact mem_iInter.mp hx.1 k

private noncomputable def cellCapJump {q : ℕ} {B : ℝ} {A : CompatibleCellFaces q B} (K : UnitCellFilling A) :
    Lp (Ambient q) 2 (volume.restrict (unitCellCube 2).val) :=
  K.trace 2 ⟨1, by norm_num, le_rfl⟩ - K.trace 2 ⟨-1, le_rfl, by norm_num⟩

private theorem cellCapJump_le_physical_faces {q : ℕ} {B h : ℝ} (hh : 0 < h) (A : CompatiblePhysicalCellFaces q B h)
    (W : UnitCellFilling (A.toUnit hh)) : ENNReal.ofReal (‖cellCapJump W‖ ^ 2) ≤
      6 * ∑ j, HarmonicMaps.dirichletEnergy (A.derivative j) (tensorGridOpenParameterBox 2 h).val := by
  letI : IsFiniteMeasure (volume.restrict (unitCellCube 2).val) :=
    isFiniteMeasure_restrict.mpr (StratificationTheory.volume_unit_coordinate_face_ne_top 2)
  have hW := W.memW12
  rw [unitCellCube_three_eq_slab] at hW
  have hRep : ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
      ∃ hs : MemLp (fun x => cellRadialField W.boundary (cellInterfacePoint x t)) 2
          (volume.restrict (unitCellCube 2).val), W.trace 2 ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp _ := by
    simpa only [unitCellFacePoint_cap_coordinate, cellInterfacePoint] using W.trace_slice 2
  have hd := cellInterface_endpoint_norm_sq_le (unitCellCube 2) (by norm_num : (-1 : ℝ) < 1) hW (W.trace 2) hRep
  rw [← unitCellCube_three_eq_slab] at hd
  have hBound : ‖cellCapJump W‖ ^ 2 ≤ 6 * ∑ j,
      ∫ x in (unitCellCube 2).val, hsNormSq ((A.toUnit hh).derivative j x) := by
    change _ ≤ _ at hd
    calc
      ‖cellCapJump W‖ ^ 2 ≤ (1 - (-1 : ℝ)) * ∫ x in (unitCellCube 3).val, hsNormSq (W.derivative x) := hd
      _ ≤ (1 - (-1 : ℝ)) * (3 * ∑ j, ∫ x in (unitCellCube 2).val, hsNormSq ((A.toUnit hh).derivative j x)) :=
        mul_le_mul_of_nonneg_left W.dirichlet_bound (by norm_num)
      _ = _ := by ring
  refine (ENNReal.ofReal_le_ofReal hBound).trans_eq ?_
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 6), ENNReal.ofReal_ofNat,
    ENNReal.ofReal_sum_of_nonneg (fun _ _ => integral_nonneg fun _ => hsNormSq_nonneg _)]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [← HarmonicMaps.dirichletEnergy_eq_ofReal_integral ((A.toUnit hh).face_memW12 j).integrable_hsNormSq,
    ← (physicalCellFace_memW12_energy hh (A.toUnit hh) j).2, (A.physical_eq hh j).2]

private theorem lintegral_capJump_pullback_le {X Y E : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [NormedAddCommGroup E] {μ : Measure X} {ν : Measure Y} {F : X → Y} (hF : Measurable F)
    {c : ℝ≥0∞} (hc : c ≠ ⊤) (hMap : Measure.map F μ ≤ c • ν) (K : Lp E 2 ν) :
    (∫⁻ x, ENNReal.ofReal (‖K (F x)‖ ^ 2) ∂μ) ≤ c * ENNReal.ofReal (‖K‖ ^ 2) := by
  have hm := Lp.memLp K
  have hK := ((hm.of_measure_le_smul hc hMap).aestronglyMeasurable.norm.pow 2).aemeasurable
  have hN : ∀ᵐ x ∂ν, 0 ≤ ‖K x‖ ^ 2 := Eventually.of_forall fun _ => sq_nonneg _
  calc
    _ = ∫⁻ y, ENNReal.ofReal (‖K y‖ ^ 2) ∂Measure.map F μ :=
      (lintegral_map' hK.ennreal_ofReal hF.aemeasurable).symm
    _ ≤ ∫⁻ y, ENNReal.ofReal (‖K y‖ ^ 2) ∂(c • ν) := lintegral_mono' hMap le_rfl
    _ = _ := by
      rw [lintegral_smul_measure, smul_eq_mul, ← ofReal_integral_eq_lintegral_ofReal (hm.integrable_norm_pow (by decide)) hN,
        integral_norm_sq_eq_eLpNorm_two_toReal_sq hm, Lp.norm_def]

variable {a : BulkCoefficients} {B h : ℝ} {v : UnitTensorSphere → S0} {hv : MemSphereH1 v}
variable {G : PenalizedSphereFaces a B h v hv} {I : ∀ f : ShellCellIndex G.grid.level, ProjectedCellInnerFace G f}

private theorem PhysicalShellCapClasses.ae_mismatch_on_patch {W : PenalizedFilledShell G I} (A : PhysicalShellCapClasses W)
    {c : Point} {f : ShellCellIndex G.grid.level} (hc : c = G.grid.center)
    (hQ : Measure.QuasiMeasurePreserving ((A.normalized.chart f).inverse ∘ (Subtype.val : UnitTensorSphere → Point))
      (tensorSphereMeasure.restrict (shellAngularSpherePatch c h f.val)) (volume.restrict (unitCellCube 2).val)) :
    (fun θ => ENNReal.ofReal (‖v θ - A.innerTensor θ‖ ^ 2))
      =ᵐ[tensorSphereMeasure.restrict (shellAngularSpherePatch c h f.val)]
        fun θ => ENNReal.ofReal (‖cellCapJump (W.cell f).unit ((A.normalized.chart f).inverse θ.val)‖ ^ 2) := by
  subst c
  let t₀ : Icc (-1 : ℝ) 1 := ⟨-1, le_rfl, by norm_num⟩
  let t₁ : Icc (-1 : ℝ) 1 := ⟨1, by norm_num, le_rfl⟩
  have hU : (A.normalized.curve t₁ : UnitTensorSphere → Ambient 5) =ᵐ[tensorSphereMeasure]
      fun θ => frobeniusCoordinateEquiv (v θ) := by
    change (A.normalized.curve ⟨1, by norm_num, le_rfl⟩ : UnitTensorSphere → Ambient 5) =ᵐ[tensorSphereMeasure] _
    rw [A.normalized.outer]
    exact hv.1.coeFn_toLp
  have hL (θ : UnitTensorSphere) : frobeniusCoordinateEquiv (A.innerTensor θ) = A.normalized.curve t₀ θ := by
    rw [PhysicalShellCapClasses.innerTensor, LinearIsometryEquiv.apply_symm_apply, A.inner_eq]
  have hSub := hQ.ae (Lp.coeFn_sub ((W.cell f).unit.trace 2 t₁) ((W.cell f).unit.trace 2 t₀))
  filter_upwards [ae_restrict_of_ae hU, A.normalized.pulls f t₁, A.normalized.pulls f t₀, hSub] with θ hUθ h1 h0 hK
  have hK' : cellCapJump (W.cell f).unit ((A.normalized.chart f).inverse θ.val) =
      (W.cell f).unit.trace 2 t₁ ((A.normalized.chart f).inverse θ.val) -
        (W.cell f).unit.trace 2 t₀ ((A.normalized.chart f).inverse θ.val) := hK
  change ENNReal.ofReal (‖v θ - A.innerTensor θ‖ ^ 2) = _
  rw [← frobeniusCoordinateEquiv.norm_map, map_sub, ← hUθ, hL, h1, h0, hK']

/-- The actual cap endpoint discrepancy costs at most the native (h^2)
factor times the sum of the original physical face Dirichlet integrals. -/
theorem PhysicalShellCapClasses.mismatch_lintegral_le_faces {W : PenalizedFilledShell G I}
    (A : PhysicalShellCapClasses W) (hSmall : h ≤ 1 / 32) :
    (∫⁻ θ, ENNReal.ofReal (‖v θ - A.innerTensor θ‖ ^ 2) ∂tensorSphereMeasure) ≤
      (ENNReal.ofReal ((32 * h) ^ 2) * 6) * ∑ f, ∑ j : CellFaceIndex,
        HarmonicMaps.dirichletEnergy ((W.faceFamily f).derivative j) (tensorGridOpenParameterBox 2 h).val := by
  classical
  let c := G.grid.center
  let F (f : ShellCellIndex G.grid.level) := shellAngularSpherePatch c h f.val
  let μ := (volume : Measure (Domain 2)).restrict (unitCellCube 2).val
  let C := ENNReal.ofReal ((32 * h) ^ 2)
  have hh := G.ht_pos
  have hh' : h ≤ 1 / 2 := hSmall.trans (by norm_num)
  have hc (i : Fin 3) : c i ∈ Icc (0 : ℝ) (1 / 32) := ⟨(G.grid.offset_mem i).1, (G.grid.offset_mem i).2.le.trans hSmall⟩
  have hm := G.grid.radius_mem
  have hM (f : ShellCellIndex G.grid.level) : MeasurableSet (F f) :=
    (A.normalized.chart f).patch_measurable.preimage measurable_subtype_coe
  have hCover : ∀ᵐ θ ∂tensorSphereMeasure, ∃ f, θ ∈ F f := ae_shellAngularSpherePatch_cover hh hc hm
  have hRest : tensorSphereMeasure = tensorSphereMeasure.restrict (⋃ f, F f) := by
    calc
      _ = tensorSphereMeasure.restrict univ := Measure.restrict_univ.symm
      _ = _ := by
        apply Measure.restrict_congr_set
        filter_upwards [hCover] with θ hθ
        exact propext ⟨fun _ => mem_iUnion.mpr hθ, fun _ => (mem_univ θ : θ ∈ (univ : Set UnitTensorSphere))⟩
  rw [hRest, lintegral_iUnion hM (pairwiseDisjoint_shellAngularSpherePatch hh hh' hc hm), tsum_fintype, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro f _
  let inv := (A.normalized.chart f).inverse ∘ (Subtype.val : UnitTensorSphere → Point)
  have hMap : Measure.map inv (tensorSphereMeasure.restrict (F f)) ≤ C • μ :=
    (A.normalized.chart f).map_sphere_measure (shellAngularPatch_subset_sphere hh hc hm f.property)
  have hi : Measurable inv := (A.normalized.chart f).measurable.comp measurable_subtype_coe
  have hQ : Measure.QuasiMeasurePreserving inv (tensorSphereMeasure.restrict (F f)) μ :=
    ⟨hi, Measure.absolutelyContinuous_of_le_smul hMap⟩
  rw [lintegral_congr_ae (A.ae_mismatch_on_patch rfl hQ)]
  exact (lintegral_capJump_pullback_le hi ENNReal.ofReal_ne_top hMap (cellCapJump (W.cell f).unit)).trans
    ((mul_le_mul_right (cellCapJump_le_physical_faces hh (W.faceFamily f) (W.cell f).unit) C).trans_eq (by rw [mul_assoc]))

/-- The actual cap difference has a linear mesh-size bound in terms of
the total six-face budget. -/
theorem PhysicalShellCapClasses.mismatch_le_h_face_energy {W : PenalizedFilledShell G I}
    (A : PhysicalShellCapClasses W) (hSmall : h ≤ 1 / 32) (ε : ElasticScale)
    {M : ℝ} (hM : 0 ≤ M)
    (hBudget : (∑ f, ∑ j : CellFaceIndex,
      physicalFacePenalizedEnergy a ε h (penalizedShellCellFace (I f) j) (penalizedShellCellFaceDerivative (I f) j))
        ≤ ENNReal.ofReal M) :
    sphereL2DifferenceSq v A.innerTensor ≤ 384 * h * M := by
  have hSum : (∑ f, ∑ j : CellFaceIndex,
      HarmonicMaps.dirichletEnergy ((W.faceFamily f).derivative j) (tensorGridOpenParameterBox 2 h).val)
        ≤ (2 : ℝ≥0∞) * ENNReal.ofReal M := by
    refine le_trans ?_ (mul_le_mul_right hBudget _)
    simp only [Finset.mul_sum, W.derivative_eq]
    refine Finset.sum_le_sum fun f _ => Finset.sum_le_sum fun j _ => ?_
    let D := HarmonicMaps.dirichletEnergy (penalizedShellCellFaceDerivative (I f) j) (tensorGridOpenParameterBox 2 h).val
    have hTwoHalf : (2 : ℝ≥0∞) * ENNReal.ofReal (1 / 2 : ℝ) = 1 := by
      rw [← ENNReal.ofReal_ofNat (n := 2), ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    calc
      D = 2 * (ENNReal.ofReal (1 / 2 : ℝ) * D) := by rw [← mul_assoc, hTwoHalf, one_mul]
      _ ≤ _ := mul_le_mul_right le_self_add _
  have hV := (frobeniusCoordinateEquiv_memLp_iff tensorSphereMeasure 2 v).mp hv.1
  have hP := (frobeniusCoordinateEquiv_memLp_iff tensorSphereMeasure 2 A.innerTensor).mp A.innerTensor_memLp
  have hIntegrable : Integrable (fun θ => ‖v θ - A.innerTensor θ‖ ^ 2) tensorSphereMeasure :=
    (hV.sub hP).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
  have hFactor : 12 * (32 * h) ^ 2 * M ≤ 384 * h * M := by
    refine mul_le_mul_of_nonneg_right ?_ hM
    nlinarith only [mul_nonneg G.ht_pos.le (sub_nonneg.mpr hSmall)]
  refine (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (mul_nonneg (by norm_num) G.ht_pos.le) hM)).mp ?_
  rw [sphereL2DifferenceSq, ofReal_integral_eq_lintegral_ofReal hIntegrable (Eventually.of_forall fun _ => sq_nonneg _)]
  refine (A.mismatch_lintegral_le_faces hSmall).trans ((mul_le_mul_right hSum _).trans ?_)
  calc
    _ = ENNReal.ofReal (12 * (32 * h) ^ 2 * M) := by
      rw [← ENNReal.ofReal_ofNat (n := 6), ← ENNReal.ofReal_ofNat (n := 2),
        ← ENNReal.ofReal_mul (by positivity : 0 ≤ (32 * h) ^ 2),
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
        ← ENNReal.ofReal_mul (by positivity : 0 ≤ (32 * h) ^ 2 * 6)]
      congr 1
      ring
    _ ≤ _ := ENNReal.ofReal_le_ofReal hFactor

end Thesis
