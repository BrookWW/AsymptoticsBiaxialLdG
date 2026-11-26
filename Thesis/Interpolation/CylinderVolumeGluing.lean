module

public import Thesis.Interpolation.CylinderCapSurface
import StratificationTheory.Foundation.LinearCoordinateMatchingTraceGluing
import StratificationTheory.Foundation.SmoothOpenDomainSobolevPullback

/-! Weak gluing along the actual horizontal interfaces of the translated
orthonormal cylinder. -/

@[expose] public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set
open scoped ContDiff ENNReal Matrix.Norms.Frobenius Topology

namespace Thesis.MeasureGeometry

abbrev CylinderHeightL2Trace (q : ℕ) (R lo hi : ℝ) :=
  C(Icc lo hi, Lp (Ambient q) 2 (volume.restrict (ball (0 : Plane) R)))

/-- The horizontal trace represents the raw physical slices in the same
translated orthonormal frame. -/
def RepresentsCylinderHeightL2Trace {q : ℕ} {R lo hi : ℝ}
    (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point) (u : Point → Ambient q)
    (T : CylinderHeightL2Trace q R lo hi) : Prop :=
  ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo lo hi,
    ∃ hs : MemLp (fun y : Plane => u (c + axisChart B (y, t))) 2 (volume.restrict (ball (0 : Plane) R)),
      T ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp (fun y : Plane => u (c + axisChart B (y, t)))

theorem translatedAxisCylinder_eq_recoveryCoordinates_preimage
    (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point) (R lo hi : ℝ) :
    translatedAxisCylinder c (B 2) R lo hi =
      cylinderRecoveryCoordinates B c ⁻¹' (ball (0 : Plane) R ×ˢ Ioo lo hi) := by
  ext x
  have hx : axisChart B (cylinderRecoveryCoordinates B c x) = x - c := by
    simpa only [add_sub_cancel_left] using
      congrArg (fun z : Point => z - c) (axisChart_cylinderRecoveryCoordinates B c x)
  change x - c ∈ openAxisCylinder (B 2) R lo hi ↔
    cylinderRecoveryCoordinates B c x ∈ ball (0 : Plane) R ×ˢ Ioo lo hi
  rw [← preimage_openAxisCylinder_axisChart B, mem_preimage, hx]

theorem axisChart_eq_finAddEquivProd_symm (B : OrthonormalBasis (Fin 3) ℝ Point)
    (y : Plane) (t : ℝ) :
    axisChart B (y, t) =
      B.repr.symm ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 2) (m := 1)).symm
        (y, EuclideanSpace.single (0 : Fin 1) t)) := by
  apply B.repr.injective
  apply recoveryReferenceSplit_injective
  have h := cylinderRecoveryCoordinates_axisChart B 0 (y, t)
  rw [zero_add, cylinderRecoveryCoordinates, sub_zero] at h
  rw [h, LinearIsometryEquiv.apply_symm_apply, recoveryReferenceSplit,
    ContinuousLinearEquiv.apply_symm_apply, PiLp.single_apply, if_pos rfl]

private theorem memW12_preimage_add_left {q : ℕ} {U : OpenDomain 3}
    {u : Point → Ambient q} {D : Point → HarmonicMaps.Gradient 3 q} (hu : MemW12 U u D) (c : Point) :
    MemW12 ⟨(fun x : Point => c + x) ⁻¹' U.val, U.property.preimage (continuous_const.add continuous_id)⟩
      (fun x => u (c + x)) (fun x => D (c + x)) := by
  let f (x : Point) := c + x
  let V : OpenDomain 3 := ⟨f ⁻¹' U.val, U.property.preimage (continuous_const.add continuous_id)⟩
  have hf : ContDiff ℝ ∞ f := contDiff_const.add contDiff_id
  have hD (x : Point) : fderiv ℝ f x = ContinuousLinearMap.id ℝ Point :=
    ((hasFDerivAt_id (𝕜 := ℝ) x).const_add c).fderiv
  have hMap := ((measurePreserving_add_left (volume : Measure Point) c).restrict_preimage U.property.measurableSet).map_eq
  have hM : Measure.map f (volume.restrict V.val) ≤ (1 : ℝ≥0∞) • volume.restrict U.val := by
    rw [one_smul]
    exact hMap.le
  have hW := StratificationTheory.memW12_smooth_open_domain_pullback hu V f hf.contDiffOn
    (fun _ hx => hx) 1 (fun x _ => by rw [hD x]; exact ContinuousLinearMap.norm_id_le)
    1 ENNReal.one_ne_top hM
  have hCol (x : Point) (i : Fin 3) :
      (∑ j : Fin 3, (fderiv ℝ f x (EuclideanSpace.single i 1)) j • D (f x) j) = D (f x) i := by
    rw [hD x, ContinuousLinearMap.id_apply]
    simp [PiLp.single_apply]
  simpa only [hCol, Function.comp_def, f] using hW

private def cylinderNativeLinearDomain (B : OrthonormalBasis (Fin 3) ℝ Point) (R a b : ℝ) : OpenDomain 3 :=
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 2) (m := 1)
  let T : Point →L[ℝ] ℝ := (EuclideanSpace.proj (0 : Fin 1)).comp
    ((ContinuousLinearMap.snd ℝ Plane (Domain 1)).comp e.toContinuousLinearMap)
  let V : OpenDomain 3 := ⟨{x : Point | (e x).1 ∈ ball (0 : Plane) R ∧ T x ∈ Ioo a b},
    (isOpen_ball.preimage (continuous_fst.comp e.continuous)).inter (isOpen_Ioo.preimage T.continuous)⟩
  ⟨B.repr ⁻¹' V.val, V.property.preimage B.repr.continuous⟩

private theorem cylinderNativeLinearDomain_eq (B : OrthonormalBasis (Fin 3) ℝ Point) (R a b : ℝ) :
    cylinderNativeLinearDomain B R a b = translatedAxisCylinderDomain B 0 R a b := by
  apply Subtype.ext
  rw [show (translatedAxisCylinderDomain B 0 R a b).val = translatedAxisCylinder 0 (B 2) R a b from rfl,
    translatedAxisCylinder_eq_recoveryCoordinates_preimage]
  ext x
  change ((recoveryReferenceSplit (B.repr x)).1 ∈ ball (0 : Plane) R ∧
    (recoveryReferenceSplit (B.repr x)).2 ∈ Ioo a b) ↔ _
  simp only [mem_preimage, cylinderRecoveryCoordinates, sub_zero, mem_prod]

private theorem translate_axisCylinder_preimage (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point)
    (R a b : ℝ) :
    (fun x : Point => c + x) ⁻¹' translatedAxisCylinder c (B 2) R a b = translatedAxisCylinder 0 (B 2) R a b := by
  ext x
  simp only [translatedAxisCylinder, mem_preimage, add_sub_cancel_left, sub_zero]

def cylinderHeightPiecewise {E : Type*} (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point)
    (t : ℝ) (u v : Point → E) (x : Point) : E :=
  if (cylinderRecoveryCoordinates B c x).2 < t then u x else v x

/-- Two original cylinder weak graphs with the same genuine horizontal
trace glue with the literal original physical columns. -/
theorem memW12_cylinderHeightPiecewise {q : ℕ}
    (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point) (R : ℝ) {a b d : ℝ} (hab : a < b) (hbd : b < d)
    (u v : Point → Ambient q) (Du Dv : Point → HarmonicMaps.Gradient 3 q)
    (hu : MemW12 (translatedAxisCylinderDomain B c R a b) u Du)
    (hv : MemW12 (translatedAxisCylinderDomain B c R b d) v Dv)
    (H : CylinderHeightL2Trace q R a b) (K : CylinderHeightL2Trace q R b d)
    (hH : RepresentsCylinderHeightL2Trace B c u H) (hK : RepresentsCylinderHeightL2Trace B c v K)
    (hMatch : H ⟨b, hab.le, le_rfl⟩ = K ⟨b, le_rfl, hbd.le⟩) :
    MemW12 (translatedAxisCylinderDomain B c R a d) (cylinderHeightPiecewise B c b u v)
      (cylinderHeightPiecewise B c b Du Dv) ∧
    ∃ J : CylinderHeightL2Trace q R a d,
      RepresentsCylinderHeightL2Trace B c (cylinderHeightPiecewise B c b u v) J ∧
      (∀ z : Icc a b, J ⟨z.val, z.property.1, z.property.2.trans hbd.le⟩ = H z) ∧
      (∀ z : Icc b d, J ⟨z.val, hab.le.trans z.property.1, z.property.2⟩ = K z) := by
  let Q := B.repr.symm.toContinuousLinearEquiv
  let u₀ (x : Point) := u (c + x)
  let v₀ (x : Point) := v (c + x)
  let Du₀ (x : Point) := Du (c + x)
  let Dv₀ (x : Point) := Dv (c + x)
  have hu₀ : MemW12 (cylinderNativeLinearDomain B R a b) u₀ Du₀ := by
    rw [cylinderNativeLinearDomain_eq]
    have eq : (⟨(fun x : Point => c + x) ⁻¹' (translatedAxisCylinderDomain B c R a b).val,
        (translatedAxisCylinderDomain B c R a b).property.preimage (continuous_const.add continuous_id)⟩ :
        OpenDomain 3) = translatedAxisCylinderDomain B 0 R a b :=
      Subtype.ext (translate_axisCylinder_preimage B c R a b)
    simpa only [eq] using memW12_preimage_add_left hu c
  have hv₀ : MemW12 (cylinderNativeLinearDomain B R b d) v₀ Dv₀ := by
    rw [cylinderNativeLinearDomain_eq]
    have eq : (⟨(fun x : Point => c + x) ⁻¹' (translatedAxisCylinderDomain B c R b d).val,
        (translatedAxisCylinderDomain B c R b d).property.preimage (continuous_const.add continuous_id)⟩ :
        OpenDomain 3) = translatedAxisCylinderDomain B 0 R b d :=
      Subtype.ext (translate_axisCylinder_preimage B c R b d)
    simpa only [eq] using memW12_preimage_add_left hv c
  letI : IsFiniteMeasure ((volume : Measure Plane).restrict (ballDomain (0 : Plane) R).val) :=
    finite_planarVolume_restrict_ball R
  have hG := StratificationTheory.memW12_linear_piecewise_of_matching_L2_traces (n := 2) (q := q)
    (ballDomain (0 : Plane) R) hab hbd Q u₀ v₀ Du₀ Dv₀
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 2) (m := 1)
  have hC (y : Plane) (z : ℝ) : Q (e.symm (y, EuclideanSpace.single (0 : Fin 1) z)) = axisChart B (y, z) :=
    (axisChart_eq_finAddEquivProd_symm B y z).symm
  have hH₀ : ∀ᵐ z : ℝ ∂volume, ∀ hz : z ∈ Ioo a b,
      ∃ hs : MemLp (fun y : Plane => u₀ (Q (e.symm (y, EuclideanSpace.single (0 : Fin 1) z)))) 2
        (volume.restrict (ball (0 : Plane) R)),
        H ⟨z, hz.1.le, hz.2.le⟩ = hs.toLp _ := by
    simpa only [hC, u₀, RepresentsCylinderHeightL2Trace] using hH
  have hK₀ : ∀ᵐ z : ℝ ∂volume, ∀ hz : z ∈ Ioo b d,
      ∃ hs : MemLp (fun y : Plane => v₀ (Q (e.symm (y, EuclideanSpace.single (0 : Fin 1) z)))) 2
        (volume.restrict (ball (0 : Plane) R)),
        K ⟨z, hz.1.le, hz.2.le⟩ = hs.toLp _ := by
    simpa only [hC, v₀, RepresentsCylinderHeightL2Trace] using hK
  have h := hG hu₀ hv₀ H K hH₀ hK₀ hMatch
  let f₀ := cylinderHeightPiecewise B 0 b u₀ v₀
  let D₀ := cylinderHeightPiecewise B 0 b Du₀ Dv₀
  have hf₀ : f₀ = (fun x => if (recoveryReferenceSplit (B.repr x)).2 < b then u₀ x else v₀ x) := by
    funext x
    simp only [f₀, cylinderHeightPiecewise, cylinderRecoveryCoordinates, sub_zero]
  let F₀ (x : Point) (i : Fin 3) := if (recoveryReferenceSplit (B.repr x)).2 < b then Du₀ x i else Dv₀ x i
  have hZ : F₀ = D₀ := by
    funext x i
    simp only [F₀, D₀, cylinderHeightPiecewise, cylinderRecoveryCoordinates, sub_zero, ite_apply]
  have hW : MemW12 (cylinderNativeLinearDomain B R a d) f₀ D₀ := by
    have h₁ : MemW12 (cylinderNativeLinearDomain B R a d)
      (fun x => if (recoveryReferenceSplit (B.repr x)).2 < b then u₀ x else v₀ x) F₀ := h.1
    rw [hZ] at h₁
    rw [hf₀]
    exact h₁
  have hDom : (⟨(fun x : Point => -c + x) ⁻¹' (cylinderNativeLinearDomain B R a d).val,
    (cylinderNativeLinearDomain B R a d).property.preimage (continuous_const.add continuous_id)⟩ : OpenDomain 3) =
      translatedAxisCylinderDomain B c R a d := by
    apply Subtype.ext
    rw [cylinderNativeLinearDomain_eq]
    ext x
    simp [translatedAxisCylinderDomain, translatedAxisCylinder, sub_eq_add_neg, add_comm]
  have hW' := memW12_preimage_add_left hW (-c)
  have hf : (fun x => f₀ (-c + x)) = cylinderHeightPiecewise B c b u v := by
    funext x
    have hA : -c + x = x - c := by abel
    have hP : c + (x - c) = x := by abel
    simp only [f₀, cylinderHeightPiecewise, cylinderRecoveryCoordinates, sub_zero, u₀, v₀, hA, hP]
    split_ifs <;> rfl
  have hD : (fun x => D₀ (-c + x)) = cylinderHeightPiecewise B c b Du Dv := by
    funext x
    have hA : -c + x = x - c := by abel
    have hP : c + (x - c) = x := by abel
    simp only [D₀, cylinderHeightPiecewise, cylinderRecoveryCoordinates, sub_zero, Du₀, Dv₀, hA, hP]
    split_ifs <;> rfl
  rw [hDom, hf, hD] at hW'
  obtain ⟨J, hJL, hJR, hJ⟩ := h.2
  refine ⟨hW', J, ?_, hJL, hJR⟩
  have hJ' : ∀ᵐ z : ℝ ∂volume, ∀ hz : z ∈ Ioo a d,
      ∃ hs : MemLp (fun y : Plane => f₀ (Q (e.symm (y, EuclideanSpace.single (0 : Fin 1) z)))) 2
        (volume.restrict (ball (0 : Plane) R)),
        J ⟨z, hz.1.le, hz.2.le⟩ = hs.toLp _ := by
    rw [hf₀]
    exact hJ
  filter_upwards [hJ'] with z hz hz'
  obtain ⟨hs, hEq⟩ := hz hz'
  have hRep (y : Plane) : f₀ (Q (e.symm (y, EuclideanSpace.single (0 : Fin 1) z))) =
      cylinderHeightPiecewise B c b u v (c + axisChart B (y, z)) := by
    rw [hC]
    simpa only [neg_add_cancel_left] using congrFun hf (c + axisChart B (y, z))
  have hAe : (fun y : Plane => f₀ (Q (e.symm (y, EuclideanSpace.single (0 : Fin 1) z))))
      =ᵐ[volume.restrict (ball (0 : Plane) R)]
      (fun y => cylinderHeightPiecewise B c b u v (c + axisChart B (y, z))) := Eventually.of_forall hRep
  let hLp := hs.ae_eq hAe
  exact ⟨hLp, hEq.trans (hs.toLp_congr hLp hAe)⟩

theorem mem_translatedAxisCylinder_iff_recoveryCoordinates
    (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point) (R a b : ℝ) (x : Point) :
    x ∈ translatedAxisCylinder c (B 2) R a b ↔
      (cylinderRecoveryCoordinates B c x).1 ∈ ball (0 : Plane) R ∧
      (cylinderRecoveryCoordinates B c x).2 ∈ Ioo a b := by
  rw [translatedAxisCylinder_eq_recoveryCoordinates_preimage]
  rfl

theorem ae_cylinderHeight_ne (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point)
    (R a d b : ℝ) :
    ∀ᵐ x ∂volume.restrict (translatedAxisCylinder c (B 2) R a d), (cylinderRecoveryCoordinates B c x).2 ≠ b := by
  let μ := (volume : Measure Plane).restrict (ball 0 R)
  let ν := (volume : Measure ℝ).restrict (Ioo a d)
  have hZ : (μ.prod ν) (univ ×ˢ ({b} : Set ℝ)) = 0 := by rw [Measure.prod_prod, measure_singleton, mul_zero]
  have hSet : {p : Plane × ℝ | ¬ p.2 ≠ b} = univ ×ˢ ({b} : Set ℝ) := by ext p; simp
  have hAe : ∀ᵐ p : Plane × ℝ ∂μ.prod ν, p.2 ≠ b := ae_iff.mpr (by rw [hSet]; exact hZ)
  exact (measurePreserving_cylinderRecoveryCoordinates B c R a d).quasiMeasurePreserving.ae hAe

theorem restrict_volume_axisCylinder_eq_add (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point)
    (R : ℝ) {a b d : ℝ} (hab : a < b) (hbd : b < d) :
    (volume : Measure Point).restrict (translatedAxisCylinder c (B 2) R a d) =
      volume.restrict (translatedAxisCylinder c (B 2) R a b) +
        volume.restrict (translatedAxisCylinder c (B 2) R b d) := by
  let L := translatedAxisCylinder c (B 2) R a b
  let M := translatedAxisCylinder c (B 2) R b d
  let U := translatedAxisCylinder c (B 2) R a d
  have hM : MeasurableSet M := (isOpen_translatedAxisCylinder _ _ _ _ _).measurableSet
  have hU : MeasurableSet U := (isOpen_translatedAxisCylinder _ _ _ _ _).measurableSet
  have hL (x : Point) : x ∈ L ↔ (cylinderRecoveryCoordinates B c x).1 ∈ ball 0 R ∧
      (cylinderRecoveryCoordinates B c x).2 ∈ Ioo a b :=
    mem_translatedAxisCylinder_iff_recoveryCoordinates B c R a b x
  have hR (x : Point) : x ∈ M ↔ (cylinderRecoveryCoordinates B c x).1 ∈ ball 0 R ∧
      (cylinderRecoveryCoordinates B c x).2 ∈ Ioo b d :=
    mem_translatedAxisCylinder_iff_recoveryCoordinates B c R b d x
  have hs (x : Point) : x ∈ U ↔ (cylinderRecoveryCoordinates B c x).1 ∈ ball 0 R ∧
      (cylinderRecoveryCoordinates B c x).2 ∈ Ioo a d :=
    mem_translatedAxisCylinder_iff_recoveryCoordinates B c R a d x
  have hDis : Disjoint L M := Set.disjoint_left.mpr fun x hxl hxr =>
    (not_lt_of_ge ((hR x).1 hxr).2.1.le) ((hL x).1 hxl).2.2
  have hSides : L ∪ M ⊆ U := by
    intro x hx
    rcases hx with hx | hx
    · have h := (hL x).1 hx
      exact (hs x).2 ⟨h.1, h.2.1, h.2.2.trans hbd⟩
    · have h := (hR x).1 hx
      exact (hs x).2 ⟨h.1, hab.trans h.2.1, h.2.2⟩
  have hCover : ∀ᵐ x ∂volume, x ∈ U → x ∈ L ∪ M := by
    apply (ae_restrict_iff' hU).mp
    filter_upwards [ae_cylinderHeight_ne B c R a d b, ae_restrict_mem hU] with x hne hx
    obtain ⟨hDisk, ha, hd⟩ := (hs x).1 hx
    by_cases h : (cylinderRecoveryCoordinates B c x).2 < b
    · exact Or.inl ((hL x).2 ⟨hDisk, ha, h⟩)
    · exact Or.inr ((hR x).2 ⟨hDisk, lt_of_le_of_ne (le_of_not_gt h) hne.symm, hd⟩)
  have hEq : (L ∪ M : Set Point) =ᵐ[(volume : Measure Point)] U :=
    hCover.mono fun x hx => propext ⟨fun hy => hSides hy, hx⟩
  exact (Measure.restrict_congr_set hEq.symm).trans (Measure.restrict_union hDis hM)

/-- Exact additivity for any two displayed densities in the same height
partition. The horizontal seam is a null set for the cylinder volume. -/
theorem lintegral_cylinderHeightPiecewise_eq_add (B : OrthonormalBasis (Fin 3) ℝ Point)
    (c : Point) (R : ℝ) {a b d : ℝ} (hab : a < b) (hbd : b < d) (f g : Point → ℝ≥0∞) :
    (∫⁻ x in translatedAxisCylinder c (B 2) R a d, cylinderHeightPiecewise B c b f g x) =
      (∫⁻ x in translatedAxisCylinder c (B 2) R a b, f x) +
        ∫⁻ x in translatedAxisCylinder c (B 2) R b d, g x := by
  rw [restrict_volume_axisCylinder_eq_add B c R hab hbd, lintegral_add_measure]
  congr 1
  · apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem (isOpen_translatedAxisCylinder c (B 2) R a b).measurableSet] with x hx
    exact if_pos ((mem_translatedAxisCylinder_iff_recoveryCoordinates B c R a b x).1 hx).2.2
  · apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem (isOpen_translatedAxisCylinder c (B 2) R b d).measurableSet] with x hx
    exact if_neg (not_lt_of_ge ((mem_translatedAxisCylinder_iff_recoveryCoordinates B c R b d x).1 hx).2.1.le)

theorem energy_cylinderHeightPiecewise_eq_add (a : BulkCoefficients) (ε : ElasticScale)
    (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point) (R : ℝ) {l b h : ℝ} (hlb : l < b) (hbh : b < h)
    (u v : Point → S0) (Du Dv : Point → Thesis.Gradient) :
    energy a ε (translatedAxisCylinder c (B 2) R l h) (cylinderHeightPiecewise B c b u v)
      (cylinderHeightPiecewise B c b Du Dv) =
        energy a ε (translatedAxisCylinder c (B 2) R l b) u Du +
          energy a ε (translatedAxisCylinder c (B 2) R b h) v Dv := by
  unfold energy
  have hEq (x : Point) :
      ENNReal.ofReal (energyDensity a ε (cylinderHeightPiecewise B c b u v x) (cylinderHeightPiecewise B c b Du Dv x)) =
        cylinderHeightPiecewise B c b (fun y => ENNReal.ofReal (energyDensity a ε (u y) (Du y)))
          (fun y => ENNReal.ofReal (energyDensity a ε (v y) (Dv y))) x := by
    unfold cylinderHeightPiecewise
    split_ifs <;> rfl
  simp_rw [hEq]
  exact lintegral_cylinderHeightPiecewise_eq_add B c R hlb hbh _ _

def cylinderThreePiecewise {E : Type*} (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point)
    (b d : ℝ) (u v w : Point → E) : Point → E :=
  cylinderHeightPiecewise B c d (cylinderHeightPiecewise B c b u v) w

/-- The two horizontal interfaces give the actual three-piece weak graph
on one physical cylinder, with its original exterior horizontal classes. -/
theorem memW12_cylinderThreePiecewise {q : ℕ}
    (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point) (R : ℝ) {a b d e : ℝ}
    (hab : a < b) (hbd : b < d) (hde : d < e)
    (u v w : Point → Ambient q) (Du Dv Dw : Point → HarmonicMaps.Gradient 3 q)
    (hu : MemW12 (translatedAxisCylinderDomain B c R a b) u Du)
    (hv : MemW12 (translatedAxisCylinderDomain B c R b d) v Dv)
    (hw : MemW12 (translatedAxisCylinderDomain B c R d e) w Dw)
    (P : CylinderHeightL2Trace q R a b) (Q : CylinderHeightL2Trace q R b d) (S : CylinderHeightL2Trace q R d e)
    (hP : RepresentsCylinderHeightL2Trace B c u P) (hQ : RepresentsCylinderHeightL2Trace B c v Q)
    (hS : RepresentsCylinderHeightL2Trace B c w S)
    (hPQ : P ⟨b, hab.le, le_rfl⟩ = Q ⟨b, le_rfl, hbd.le⟩)
    (hQS : Q ⟨d, hbd.le, le_rfl⟩ = S ⟨d, le_rfl, hde.le⟩) :
    MemW12 (translatedAxisCylinderDomain B c R a e) (cylinderThreePiecewise B c b d u v w)
      (cylinderThreePiecewise B c b d Du Dv Dw) ∧
    ∃ T : CylinderHeightL2Trace q R a e,
      RepresentsCylinderHeightL2Trace B c (cylinderThreePiecewise B c b d u v w) T ∧
      T ⟨a, le_rfl, (hab.trans (hbd.trans hde)).le⟩ = P ⟨a, le_rfl, hab.le⟩ ∧
      T ⟨e, (hab.trans (hbd.trans hde)).le, le_rfl⟩ = S ⟨e, hde.le, le_rfl⟩ := by
  obtain ⟨hUV, T, hT, hTL, hTR⟩ := memW12_cylinderHeightPiecewise B c R hab hbd u v Du Dv hu hv P Q hP hQ hPQ
  have hTmeet : T ⟨d, (hab.trans hbd).le, le_rfl⟩ = S ⟨d, le_rfl, hde.le⟩ :=
    (hTR ⟨d, hbd.le, le_rfl⟩).trans hQS
  obtain ⟨hm, V, hV, hVL, hVR⟩ := memW12_cylinderHeightPiecewise B c R (hab.trans hbd) hde
    (cylinderHeightPiecewise B c b u v) w (cylinderHeightPiecewise B c b Du Dv) Dw hUV hw T S hT hS hTmeet
  exact ⟨hm, V, hV, (hVL ⟨a, le_rfl, (hab.trans hbd).le⟩).trans (hTL ⟨a, le_rfl, hab.le⟩),
    hVR ⟨e, hde.le, le_rfl⟩⟩

theorem energy_cylinderThreePiecewise_eq_sum (a : BulkCoefficients) (ε : ElasticScale)
    (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point) (R : ℝ)
    {l b d e : ℝ} (hlb : l < b) (hbd : b < d) (hde : d < e)
    (u v w : Point → S0) (Du Dv Dw : Point → Thesis.Gradient) :
    energy a ε (translatedAxisCylinder c (B 2) R l e) (cylinderThreePiecewise B c b d u v w)
      (cylinderThreePiecewise B c b d Du Dv Dw) =
        energy a ε (translatedAxisCylinder c (B 2) R l b) u Du +
          energy a ε (translatedAxisCylinder c (B 2) R b d) v Dv +
            energy a ε (translatedAxisCylinder c (B 2) R d e) w Dw := by
  unfold cylinderThreePiecewise
  rw [energy_cylinderHeightPiecewise_eq_add a ε B c R (hlb.trans hbd) hde,
    energy_cylinderHeightPiecewise_eq_add a ε B c R hlb hbd]

end Thesis.MeasureGeometry

end
