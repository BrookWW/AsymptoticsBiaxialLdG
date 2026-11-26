module

public import Thesis.Interpolation.SphericalGrid
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Thesis.Foundation.BulkGeometry
import Thesis.StressEnergy
import StratificationTheory.Foundation.ClosedTargetACLInheritance
import StratificationTheory.Foundation.NativeIntervalL2Trace
import StratificationTheory.Foundation.IntervalWeakRepresentative

/-! The penalized sphere traces on one translated cubical boundary. -/

public section

open Filter HarmonicMaps MeasureTheory Metric Set
open scoped BigOperators ENNReal Matrix.Norms.Frobenius NNReal Topology

namespace Thesis

@[expose] noncomputable def decodeTensorCoordinates : Ambient 7 →L[ℝ] S0 :=
  frobeniusCoordinateEquiv.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((ContinuousLinearMap.fst ℝ (Ambient 5) (Ambient 2)).comp
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 5) (m := 2)).toContinuousLinearMap)

private theorem firstTensorCoordinates_apply (z : Ambient 7) (i : Fin 5) :
    ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 5) (m := 2)) z).1 i = z (Fin.castAdd 2 i) :=
  rfl

theorem decodeTensorCoordinates_of_eq_coordinates (z : Ambient 7) (A : S0)
    (h : ∀ i : Fin 5, z (Fin.castAdd 2 i) = frobeniusCoordinateEquiv A i) :
    decodeTensorCoordinates z = A := by
  have hFirst : ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 5) (m := 2)) z).1 =
      frobeniusCoordinateEquiv A := PiLp.ext (fun i => (firstTensorCoordinates_apply z i).trans (h i))
  change frobeniusCoordinateEquiv.symm ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 5) (m := 2)) z).1 = A
  rw [hFirst, LinearIsometryEquiv.symm_apply_apply]

theorem norm_sq_decodeTensorCoordinates_le (z : Ambient 7) :
    ‖decodeTensorCoordinates z‖ ^ 2 ≤ ‖z‖ ^ 2 := by
  change ‖frobeniusCoordinateEquiv.symm
    ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 5) (m := 2)) z).1‖ ^ 2 ≤ ‖z‖ ^ 2
  rw [LinearIsometryEquiv.norm_map, PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2,
    Fin.sum_univ_add (a := 5) (b := 2)]
  simp only [firstTensorCoordinates_apply]
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

theorem memLp_interval_of_nativeOne {q : ℕ} {h : ℝ} {g : ℝ → Ambient q}
    (hg : MemLp (fun t : Domain 1 => g (t 0)) 2
      (volume.restrict {t : Domain 1 | t 0 ∈ Ioo (0 : ℝ) h})) :
    MemLp g 2 (volume.restrict (Ioo (0 : ℝ) h)) := by
  let E := (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ)).toHomeomorph
  have hMap := (StratificationTheory.measurePreserving_domainOne_eval.restrict_preimage
    (measurableSet_Ioo (a := 0) (b := h))).map_eq
  have hMem : MemLp g 2 (Measure.map E
      (volume.restrict {t : Domain 1 | t 0 ∈ Ioo (0 : ℝ) h})) :=
    E.measurableEmbedding.memLp_map_measure_iff.mpr hg
  change MemLp g 2 (Measure.map (fun t : Domain 1 => t 0)
    (volume.restrict ((fun t : Domain 1 => t 0) ⁻¹' Ioo (0 : ℝ) h))) at hMem
  rwa [hMap] at hMem

private theorem edgeTrace_energy_mem_closed {h B : ℝ} (hh : 0 < h) {U : ℝ → S0}
    (hAC : AbsolutelyContinuousOnInterval U 0 h)
    (hAe : ∀ᵐ t ∂volume.restrict (Ioo 0 h), ‖U t‖ ≤ B) :
    ∀ t ∈ Icc 0 h, ‖U t‖ ≤ B := by
  have hMembership : ∀ᵐ t ∂volume.restrict (Ioo 0 h), U t ∈ closedBall 0 B :=
    hAe.mono (fun t ht => mem_closedBall_zero_iff.mpr ht)
  intro t ht
  apply mem_closedBall_zero_iff.mp
  exact StratificationTheory.absolutelyContinuous_interval_mem_closed_of_ae hh hAC
    EventuallyEq.rfl isClosed_closedBall hMembership t ht

/-- Each oriented edge of one physical cubical boundary has a tensor trace
and its derivative in arc-length coordinates of the physical cube. All
vertex values are those of the same normalized sphere representative. -/
structure PenalizedSphereGrid (a : BulkCoefficients) (B h : ℝ)
    (v : UnitTensorSphere → S0) (hv : MemSphereH1 v) where
  center : Point
  level : ℕ
  offset_mem : ∀ i : Fin 3, center i ∈ Ico (0 : ℝ) h
  radius_mem : (level : ℝ) * h ∈ Icc (1 / 8 : ℝ) (1 / 4)
  trace : ↥(cubeBoundaryEdges level) → ℝ → S0
  derivative : ↥(cubeBoundaryEdges level) → ℝ → S0
  trace_ac : ∀ e, AbsolutelyContinuousOnInterval (trace e) 0 h
  derivative_memLp : ∀ e, MemLp (derivative e) 2 (volume.restrict (Ioo 0 h))
  trace_increment : ∀ e, ∀ s ∈ Icc 0 h, ∀ t ∈ Icc 0 h,
    trace e t - trace e s = ∫ r in s..t, derivative e r
  trace_bound : ∀ e, ∀ t ∈ Icc 0 h, ‖trace e t‖ ≤ B
  trace_ae : ∀ e, ∀ᵐ t ∂volume.restrict (Ioo 0 h), ∃ θ : UnitTensorSphere,
    θ.val = NormedSpace.normalize (tensorGridEdgePoint center h e.val t) ∧ trace e t = v θ
  endpoint_eq : ∀ e, ∀ t ∈ ({0, h} : Set ℝ), ∃ θ : UnitTensorSphere,
    θ.val = NormedSpace.normalize (tensorGridEdgePoint center h e.val t) ∧ trace e t = v θ

/-- The same grid controls the unscaled potential and squared derivative
integrals of the actual tensor traces, with constants uniform in the mesh
size and chosen before the sphere datum. -/
theorem exists_penalizedSphereGrid (a : BulkCoefficients) (B : ℝ) (hB : 0 ≤ B) :
    ∃ C > (0 : ℝ), ∀ (u : UnitTensorSphere → S0) (hu : MemSphereH1 u),
      (∀ᵐ θ ∂tensorSphereMeasure, ‖u θ‖ ≤ B) → ∀ {h : ℝ}, 0 < h → h ≤ 1 / 32 →
      ∃ (v : UnitTensorSphere → S0) (hv : MemSphereH1 v),
        u =ᵐ[tensorSphereMeasure] v ∧ (∀ θ, ‖v θ‖ ≤ B) ∧
        sphereGradientEnergy v hv = sphereGradientEnergy u hu ∧
        ∃ G : PenalizedSphereGrid a B h v hv,
          (∑ e, ∫ t in Ioo (0 : ℝ) h, ‖G.derivative e t‖ ^ 2) ≤ C / h * sphereGradientEnergy u hu ∧
          (∑ e, ∫ t in Ioo (0 : ℝ) h, bulkPotential a (G.trace e t)) ≤
            C / h * ∫ θ : UnitTensorSphere, bulkPotential a (u θ) ∂tensorSphereMeasure := by
  classical
  letI : CompleteSpace S0 := complete_of_proper
  obtain ⟨K, hK, hChannels⟩ := exists_sphere_pair_penalized_grid_channels a B hB
  let C := max (2304 * K) (12288 : ℝ)
  have hC : 0 < C := (show (0 : ℝ) < 12288 by norm_num).trans_le (le_max_right _ _)
  refine ⟨C, hC, ?_⟩
  intro u hu huB h hh hsmall
  obtain ⟨v, hv, hvu, hvB, hV, N, P, hP, hN, hPN, hCoordinates, hPotential, hEnergy⟩ :=
    hChannels u hu huB
  obtain ⟨w, Dw, _, hRad, c, m, hc, hm, hEdge, hTrace, hGradientChannel, hPotentialChannel⟩ :=
    exists_sphere_pair_shifted_cube_edge_data P hP hN
      (fun l => Eventually.of_forall (hPN l)) hh hsmall
  let E := ↥(cubeBoundaryEdges m)
  let x (e : E) (t : ℝ) := tensorGridEdgePoint c h e.val t
  let J := decodeTensorCoordinates
  have hCenter (i : Fin 3) : c i ∈ Icc (0 : ℝ) (1 / 32) :=
    ⟨(hc i).1, (hc i).2.le.trans hsmall⟩
  have hRaw (e : E) (t : ℝ) (ht : t ∈ Icc 0 h) :
      ∃ θ : UnitTensorSphere, θ.val = NormedSpace.normalize (x e t) ∧
        J (w 0 (x e t)) = v θ ∧ ‖w 0 (x e t) - w 1 (x e t)‖ ^ 2 = bulkPotential a (v θ) := by
    have hθ := (normalized_grid_edge_dist hh hCenter hm e.property ht ht).1
    let θ : UnitTensorSphere := ⟨NormedSpace.normalize (x e t), hθ⟩
    have hx : x e t ≠ 0 := NormedSpace.norm_normalize_eq_one_iff.mp (mem_sphere_zero_iff_norm.mp hθ)
    let ρ : PositiveRadius := ⟨‖x e t‖, norm_pos_iff.mpr hx⟩
    have hw (l : Fin 2) : w l (x e t) = P l θ := by
      have h := hRad l ρ θ
      change w l (‖x e t‖ • NormedSpace.normalize (x e t)) = P l θ at h
      simpa only [NormedSpace.norm_smul_normalize] using h
    exact ⟨θ, rfl, by rw [hw]; exact decodeTensorCoordinates_of_eq_coordinates _ _ (hCoordinates θ 0),
      by rw [hw, hw, hPotential]⟩
  choose raw hRep using fun e : E => hTrace e.val e.property 0
  let nativeDerivative (e : E) (t : ℝ) := Dw 0 (x e t) (e.val.2)
  let g (e : E) (t : ℝ) := J (nativeDerivative e t)
  have hNative (e : E) : MemLp (nativeDerivative e) 2 (volume.restrict (Ioo (0 : ℝ) h)) :=
    memLp_interval_of_nativeOne ((hEdge e.val e.property 0).2.2 (0 : Fin 1))
  have hg (e : E) : MemLp (g e) 2 (volume.restrict (Ioo (0 : ℝ) h)) :=
    (hNative e).continuousLinearMap_comp J
  let U (e : E) (t : ℝ) := J (raw e 0) + ∫ r in 0..t, g e r
  have hEq (e : E) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) h) : U e t = J (raw e t) := by
    have hInc := (hRep e).2.2.2.2.2 0 ⟨le_rfl, hh.le⟩ t ht
    have hn := StratificationTheory.intervalIntegrable_of_memLp_two hh.le (hNative e)
    have hInt : IntervalIntegrable (nativeDerivative e) volume 0 t := by
      refine hn.mono_set' ?_
      rw [uIoc_of_le ht.1, uIoc_of_le hh.le]
      exact Ioc_subset_Ioc_right ht.2
    calc
      U e t = J (raw e 0) + J (∫ r in 0..t, nativeDerivative e r) :=
        congrArg (fun z => J (raw e 0) + z) (J.intervalIntegral_comp_comm hInt)
      _ = J (raw e 0) + J (raw e t - raw e 0) := by rw [hInc]
      _ = _ := by rw [map_sub, add_sub_cancel]
  have hAC (e : E) : AbsolutelyContinuousOnInterval (U e) 0 h := by
    have hInt := StratificationTheory.intervalIntegrable_of_memLp_two hh.le (hg e)
    have hPrim := StratificationTheory.intervalPrimitive_absolutelyContinuous hInt left_mem_uIcc
    have hConst : AbsolutelyContinuousOnInterval (fun _ : ℝ => J (raw e 0)) 0 h := by
      simp only [AbsolutelyContinuousOnInterval, dist_self, Finset.sum_const_zero, tendsto_const_nhds]
    exact hConst.add hPrim
  have hTraceAe (e : E) : ∀ᵐ t ∂volume.restrict (Ioo 0 h),
      ∃ θ : UnitTensorSphere, θ.val = NormedSpace.normalize (x e t) ∧ U e t = v θ := by
    filter_upwards [(hRep e).2.1, ae_restrict_mem measurableSet_Ioo] with t ht ht'
    obtain ⟨θ, hθ, hθ', _⟩ := hRaw e t (Ioo_subset_Icc_self ht')
    exact ⟨θ, hθ, by rw [hEq e t (Ioo_subset_Icc_self ht'), ht]; exact hθ'⟩
  let G : PenalizedSphereGrid a B h v hv :=
    { center := c
      level := m
      offset_mem := hc
      radius_mem := hm
      trace := U
      derivative := g
      trace_ac := hAC
      derivative_memLp := hg
      trace_increment := by
        intro e s hs t ht
        change _ + (∫ r in 0..t, g e r) - (_ + (∫ r in 0..s, g e r)) = _
        rw [add_sub_add_left_eq_sub]
        exact StratificationTheory.intervalPrimitive_sub hh.le (hg e) hs ht
      trace_bound := fun e => edgeTrace_energy_mem_closed hh (hAC e) ((hTraceAe e).mono
        (fun t ⟨θ, _, hEq⟩ => hEq ▸ hvB θ))
      trace_ae := hTraceAe
      endpoint_eq := by
        intro e t ht
        rcases Set.mem_insert_iff.mp ht with ht₀ | htₕ
        · subst t
          have htc : (0 : ℝ) ∈ Icc 0 h := ⟨le_rfl, hh.le⟩
          obtain ⟨θ, hθ, hθ', _⟩ := hRaw e 0 htc
          exact ⟨θ, hθ, by rw [hEq e 0 htc, (hRep e).2.2.1]; exact hθ'⟩
        · have heq := Set.mem_singleton_iff.mp htₕ
          subst t
          have htc : h ∈ Icc 0 h := ⟨hh.le, le_rfl⟩
          obtain ⟨θ, hθ, hθ', _⟩ := hRaw e h htc
          exact ⟨θ, hθ, by rw [hEq e h htc, (hRep e).2.2.2.1]; exact hθ'⟩ }
  have hSumAttach (f : TensorGridEdge → ℝ≥0∞) : (∑ e : E, f e.val) = ∑ e ∈ cubeBoundaryEdges m, f e := by
    change (∑ e ∈ (Finset.univ : Finset ↥(cubeBoundaryEdges m)), f e.val) = _
    rw [Finset.univ_eq_attach, Finset.sum_attach]
  refine ⟨v, hv, hvu, hvB, hV, G, ?_, ?_⟩
  · have hnonneg : 0 ≤ sphereGradientEnergy u hu :=
      integral_nonneg (fun _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (div_nonneg hC.le hh.le) hnonneg)).mp
    rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => integral_nonneg fun _ => sq_nonneg _)]
    change (∑ e : E, ENNReal.ofReal (∫ t in Ioo (0 : ℝ) h, ‖g e t‖ ^ 2)) ≤ _
    calc
      _ ≤ ∑ e : E, ∫⁻ t in Ioo (0 : ℝ) h, ENNReal.ofReal
          (hsNormSq (Dw 0 (x e t)) + hsNormSq (Dw 1 (x e t))) := by
        apply Finset.sum_le_sum
        intro e _
        rw [ofReal_integral_eq_lintegral_ofReal ((hg e).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0))
          (Eventually.of_forall (fun _ => sq_nonneg _))]
        refine lintegral_mono (fun t => ENNReal.ofReal_le_ofReal ?_)
        refine (norm_sq_decodeTensorCoordinates_le (nativeDerivative e t)).trans ?_
        have hSum : ‖nativeDerivative e t‖ ^ 2 ≤ hsNormSq (Dw 0 (x e t)) :=
          Finset.single_le_sum (f := fun i => ‖Dw 0 (x e t) i‖ ^ 2)
            (fun j _ => sq_nonneg _) (Finset.mem_univ e.val.2)
        exact hSum.trans (le_add_of_nonneg_right (hsNormSq_nonneg _))
      _ ≤ ENNReal.ofReal (2304 / h) * ENNReal.ofReal
          (nativeSphereGradientEnergy (P 0) (hP 0) + nativeSphereGradientEnergy (P 1) (hP 1)) := by
        exact (hSumAttach (fun e => ∫⁻ t in Ioo (0 : ℝ) h, ENNReal.ofReal
          (hsNormSq (Dw 0 (tensorGridEdgePoint c h e t)) +
            hsNormSq (Dw 1 (tensorGridEdgePoint c h e t))))).le.trans hGradientChannel
      _ ≤ ENNReal.ofReal (C / h * sphereGradientEnergy u hu) := by
        calc
          _ ≤ ENNReal.ofReal (2304 / h) * ENNReal.ofReal (K * sphereGradientEnergy u hu) :=
            mul_le_mul_right (ENNReal.ofReal_le_ofReal hEnergy) _
          _ = ENNReal.ofReal ((2304 * K / h) * sphereGradientEnergy u hu) := by
            rw [← ENNReal.ofReal_mul (div_nonneg (by norm_num) hh.le)]
            congr 1
            ring
          _ ≤ _ := ENNReal.ofReal_le_ofReal
            (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (le_max_left _ _) hh.le) hnonneg)
  · have hPotNonneg : 0 ≤ ∫ θ : UnitTensorSphere, bulkPotential a (u θ) ∂tensorSphereMeasure :=
      integral_nonneg (fun θ => bulkPotential_nonneg a (u θ))
    apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (div_nonneg hC.le hh.le) hPotNonneg)).mp
    rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => integral_nonneg fun _ => bulkPotential_nonneg a _)]
    change (∑ e : E, ENNReal.ofReal (∫ t in Ioo (0 : ℝ) h, bulkPotential a (U e t))) ≤ _
    have hSpherePot : ∫ θ : UnitTensorSphere, ‖P 0 θ - P 1 θ‖ ^ 2 ∂tensorSphereMeasure =
        ∫ θ : UnitTensorSphere, bulkPotential a (u θ) ∂tensorSphereMeasure :=
      integral_congr_ae (hvu.mono (fun θ ht => (hPotential θ).trans (congrArg _ ht.symm)))
    calc
      _ = ∑ e : E, ∫⁻ t in Ioo (0 : ℝ) h, ENNReal.ofReal
          (‖w 0 (x e t) - w 1 (x e t)‖ ^ 2) := by
        apply Finset.sum_congr rfl
        intro e _
        have hCont : ContinuousOn (U e) (Icc (0 : ℝ) h) := by
          simpa only [uIcc_of_le hh.le] using! (hAC e).continuousOn
        have hInt : IntegrableOn (fun t => bulkPotential a (U e t)) (Ioo (0 : ℝ) h) :=
          ((contDiff_bulkPotential a).continuous.comp_continuousOn hCont).integrableOn_Icc.mono_set Ioo_subset_Icc_self
        rw [ofReal_integral_eq_lintegral_ofReal hInt
          (Eventually.of_forall (fun _ => bulkPotential_nonneg a _))]
        apply lintegral_congr_ae
        filter_upwards [(hRep e).2.1, ae_restrict_mem measurableSet_Ioo] with t ht ht'
        obtain ⟨θ, _, hθ, hθ'⟩ := hRaw e t (Ioo_subset_Icc_self ht')
        rw [hEq e t (Ioo_subset_Icc_self ht'), ht, hθ, hθ']
      _ ≤ ENNReal.ofReal (12288 / h) * ENNReal.ofReal
          (∫ θ : UnitTensorSphere, ‖P 0 θ - P 1 θ‖ ^ 2 ∂tensorSphereMeasure) := by
        exact (hSumAttach (fun e => ∫⁻ t in Ioo (0 : ℝ) h, ENNReal.ofReal
          (‖w 0 (tensorGridEdgePoint c h e t) - w 1 (tensorGridEdgePoint c h e t)‖ ^ 2))).le.trans hPotentialChannel
      _ ≤ _ := by
        rw [hSpherePot, ENNReal.ofReal_mul (div_nonneg hC.le hh.le)]
        exact mul_le_mul_left (ENNReal.ofReal_le_ofReal
          (div_le_div_of_nonneg_right (le_max_right _ _) hh.le)) _

/-- One selected grid gives the penalized edge budget simultaneously at any
elastic scale. Nonnegativity also gives this budget on each individual edge. -/
theorem exists_penalizedSphereGrid_energy (a : BulkCoefficients) (B : ℝ) (hB : 0 ≤ B) :
    ∃ C > (0 : ℝ), ∀ (u : UnitTensorSphere → S0) (hu : MemSphereH1 u),
      (∀ᵐ θ ∂tensorSphereMeasure, ‖u θ‖ ≤ B) → ∀ {h : ℝ}, 0 < h → h ≤ 1 / 32 →
      ∃ (v : UnitTensorSphere → S0) (hv : MemSphereH1 v),
        u =ᵐ[tensorSphereMeasure] v ∧ (∀ θ, ‖v θ‖ ≤ B) ∧
        sphereGradientEnergy v hv = sphereGradientEnergy u hu ∧
        ∃ G : PenalizedSphereGrid a B h v hv, ∀ ε : ElasticScale,
          let E := fun e => ∫ t in Ioo (0 : ℝ) h,
            (1 / 2 : ℝ) * ‖G.derivative e t‖ ^ 2 + (ε : ℝ)⁻¹ ^ 2 * bulkPotential a (G.trace e t)
          (∑ e, E e) ≤ C / h * spherePenalizedEnergy a ε u hu ∧
            ∀ e, E e ≤ C / h * spherePenalizedEnergy a ε u hu := by
  obtain ⟨C, hC, H⟩ := exists_penalizedSphereGrid a B hB
  refine ⟨C, hC, ?_⟩
  intro u hu huB h hh hsmall
  obtain ⟨v, hv, huv, hvB, hvGrad, G, hGrad, hBulk⟩ := H u hu huB hh hsmall
  refine ⟨v, hv, huv, hvB, hvGrad, G, ?_⟩
  intro ε E
  have hSplit (e : ↥(cubeBoundaryEdges G.level)) : E e =
      (1 / 2 : ℝ) * (∫ t in Ioo (0 : ℝ) h, ‖G.derivative e t‖ ^ 2) +
        (ε : ℝ)⁻¹ ^ 2 * ∫ t in Ioo (0 : ℝ) h, bulkPotential a (G.trace e t) := by
    have hDir := (G.derivative_memLp e).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
    have hTrace : ContinuousOn (G.trace e) (Icc (0 : ℝ) h) := by
      simpa only [uIcc_of_le hh.le] using! (G.trace_ac e).continuousOn
    have hPot : IntegrableOn (fun t => bulkPotential a (G.trace e t)) (Ioo (0 : ℝ) h) :=
      ((contDiff_bulkPotential a).continuous.comp_continuousOn hTrace).integrableOn_Icc.mono_set Ioo_subset_Icc_self
    change (∫ t in Ioo (0 : ℝ) h, (1 / 2 : ℝ) * ‖G.derivative e t‖ ^ 2 +
      (ε : ℝ)⁻¹ ^ 2 * bulkPotential a (G.trace e t)) = _
    rw [integral_add (hDir.const_mul _) (hPot.const_mul _), integral_const_mul, integral_const_mul]
  have hTotal : (∑ e, E e) ≤ C / h * spherePenalizedEnergy a ε u hu := by
    simp_rw [hSplit, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [spherePenalizedEnergy, sphereScaledBulkEnergy, integral_const_mul]
    calc
      _ ≤ (1 / 2 : ℝ) * (C / h * sphereGradientEnergy u hu) +
          (ε : ℝ)⁻¹ ^ 2 * (C / h * ∫ θ : UnitTensorSphere, bulkPotential a (u θ) ∂tensorSphereMeasure) :=
        add_le_add (mul_le_mul_of_nonneg_left hGrad (by norm_num))
          (mul_le_mul_of_nonneg_left hBulk (sq_nonneg _))
      _ = _ := by ring
  refine ⟨hTotal, fun e => ?_⟩
  refine (Finset.single_le_sum (fun j _ => ?_) (Finset.mem_univ e)).trans hTotal
  exact integral_nonneg (fun t => add_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
    (mul_nonneg (sq_nonneg _) (bulkPotential_nonneg a _)))

end Thesis

end
