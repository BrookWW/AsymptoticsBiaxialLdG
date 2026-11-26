module

public import Thesis.Interpolation.PenalizedSphereGrid
public import Thesis.Interpolation.SphericalGridFaces
import Thesis.Foundation.BulkGeometry
import Thesis.StressEnergy
import StratificationTheory.Foundation.ClosedTargetACLInheritance
import StratificationTheory.Foundation.IntervalWeakRepresentative

/-! Tensor-valued native face graphs and their compatible traces on one
penalized sphere grid. -/

public section

open Filter HarmonicMaps MeasureTheory Metric Set
open scoped BigOperators ContDiff ENNReal Matrix.Norms.Frobenius Topology

namespace Thesis

private theorem integrableOn_smul_test {d q : ℕ} {Ω : OpenDomain d}
    {f : Domain d → Ambient q} {χ : Domain d → ℝ}
    (hf : LocallyIntegrableOn f Ω.val volume) (hχ : Continuous χ)
    (hComp : HasCompactSupport χ) (hSupp : tsupport χ ⊆ Ω.val) :
    IntegrableOn (fun x => χ x • f x) Ω.val volume := by
  have hfK := hf.integrableOn_compact_subset hSupp hComp
  have hχK : MemLp χ ∞ (volume.restrict (tsupport χ)) :=
    hχ.memLp_top_of_hasCompactSupport hComp _
  have hpair := hfK.smul_of_top_right hχK
  apply (integrableOn_iff_integrable_of_support_subset ?_).mp hpair |>.integrableOn
  intro x hx
  by_contra! hnot
  have hx0 := image_eq_zero_of_notMem_tsupport hnot
  change χ x • f x ≠ 0 at hx
  rw [hx0, zero_smul] at hx
  exact hx rfl

/-- Linear projection of the target preserves the actual weak coordinate
columns of a native Sobolev graph. -/
theorem memW12_target_continuousLinearMap {d p q : ℕ} {Ω : OpenDomain d}
    {f : Domain d → Ambient p} {D : Domain d → HarmonicMaps.Gradient d p}
    (hf : MemW12 Ω f D) (L : Ambient p →L[ℝ] Ambient q) :
    MemW12 Ω (fun x => L (f x)) (fun x i => L (D x i)) := by
  refine ⟨⟨L.locallyIntegrableOn_comp hf.1.1, fun i => L.locallyIntegrableOn_comp (hf.1.2.1 i), ?_⟩,
    hf.2.1.continuousLinearMap_comp L, fun i => (hf.2.2 i).continuousLinearMap_comp L⟩
  intro i φ hφ hComp hSupp
  let χ := coordinateDerivative φ hφ i
  have hχ : Continuous χ := (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcχ : HasCompactSupport χ := hComp.fderiv_apply ℝ (EuclideanSpace.single i 1)
  have hsχ : tsupport χ ⊆ Ω.val := (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1)).trans hSupp
  have hInt := integrableOn_smul_test hf.1.1 hχ hcχ hsχ
  have hGradInt := integrableOn_smul_test (hf.1.2.1 i) hφ.continuous hComp hSupp
  change (∫ x in Ω.val, χ x • L (f x)) = -(∫ x in Ω.val, φ x • L (D x i))
  simp_rw [← map_smul L]
  rw [L.integral_comp_comm hInt, L.integral_comp_comm hGradInt,
    hf.1.2.2 i φ hφ hComp hSupp, map_neg]

private theorem compLpL_toLp_tensor {μ : Measure (Domain 1)} {f : Domain 1 → Ambient 7}
    (hf : MemLp f 2 μ) :
    decodeTensorCoordinates.compLpL 2 μ (hf.toLp f) =
      (hf.continuousLinearMap_comp decodeTensorCoordinates).toLp (fun x => decodeTensorCoordinates (f x)) := by
  apply Lp.ext
  filter_upwards [(decodeTensorCoordinates.coeFn_compLpL (μ := μ) (hf.toLp f)),
    hf.coeFn_toLp, (hf.continuousLinearMap_comp decodeTensorCoordinates).coeFn_toLp] with x hCLM hF hDec
  exact hCLM.trans ((congrArg decodeTensorCoordinates hF).trans hDec.symm)

private theorem tensorGridOpenParameterBox_one_preimage (h : ℝ) :
    (tensorGridOpenParameterBox 1 h).val = (fun x : Domain 1 => x 0) ⁻¹' Ioo (0 : ℝ) h := by
  ext x
  constructor
  · intro hx
    exact mem_iInter.mp hx (0 : Fin 1)
  · intro hx
    exact mem_iInter.mpr (fun j => (Subsingleton.elim (0 : Fin 1) j) ▸ hx)

private theorem decode_tensor_edge_trace {h : ℝ} (hh : 0 < h) {f g : ℝ → Ambient 7}
    (hg : MemLp g 2 (volume.restrict (Ioo 0 h)))
    (hraw : ∀ s ∈ Icc 0 h, ∀ t ∈ Icc 0 h, f t - f s = ∫ r in s..t, g r) :
    let d := fun t => decodeTensorCoordinates (g t)
    let u := fun t => decodeTensorCoordinates (f 0) + ∫ r in 0..t, d r
    AbsolutelyContinuousOnInterval u 0 h ∧ MemLp d 2 (volume.restrict (Ioo 0 h)) ∧
      EqOn u (fun t => decodeTensorCoordinates (f t)) (Icc 0 h) ∧
      ∀ s ∈ Icc 0 h, ∀ t ∈ Icc 0 h, u t - u s = ∫ r in s..t, d r := by
  intro d u
  letI : CompleteSpace S0 := complete_of_proper
  let J := decodeTensorCoordinates
  have hd : MemLp d 2 (volume.restrict (Ioo 0 h)) := hg.continuousLinearMap_comp J
  have hRawInt := StratificationTheory.intervalIntegrable_of_memLp_two hh.le hg
  have hInt := StratificationTheory.intervalIntegrable_of_memLp_two hh.le hd
  have hConst : AbsolutelyContinuousOnInterval (fun _ : ℝ => J (f 0)) 0 h := by
    simp only [AbsolutelyContinuousOnInterval, dist_self, Finset.sum_const_zero, tendsto_const_nhds]
  refine ⟨hConst.add (StratificationTheory.intervalPrimitive_absolutelyContinuous hInt left_mem_uIcc), hd, ?_, ?_⟩
  · intro t ht
    have htInt : IntervalIntegrable g volume 0 t := hRawInt.mono_set' (by
      rw [uIoc_of_le ht.1, uIoc_of_le hh.le]
      exact Ioc_subset_Ioc_right ht.2)
    calc
      u t = J (f 0) + J (∫ r in 0..t, g r) :=
        congrArg (fun z => J (f 0) + z) (J.intervalIntegral_comp_comm htInt)
      _ = J (f 0) + J (f t - f 0) := by rw [hraw 0 ⟨le_rfl, hh.le⟩ t ht]
      _ = J (f t) := by rw [map_sub, add_sub_cancel]
  · intro s hs t ht
    change _ + (∫ r in 0..t, d r) - (_ + (∫ r in 0..s, d r)) = _
    rw [add_sub_add_left_eq_sub]
    exact StratificationTheory.intervalPrimitive_sub hh.le hd hs ht

/-- Lower parallel edge of an oriented square on the chosen cube. -/
@[expose] def tensorSquareLowerEdge {m : ℕ} (f : ↥(cubeBoundarySquares m)) :
    ↥(cubeBoundaryEdges m) :=
  ⟨(f.val.1, f.val.2.val.1), (cubeBoundarySquares_edges_mem f.property).1⟩

/-- Upper parallel edge of an oriented square on the chosen cube. -/
@[expose] def tensorSquareUpperEdge {m : ℕ} (f : ↥(cubeBoundarySquares m)) :
    ↥(cubeBoundaryEdges m) :=
  ⟨(f.val.1 + Pi.single f.val.2.val.2 (1 : ℤ), f.val.2.val.1),
    (cubeBoundarySquares_edges_mem f.property).2.1⟩

/-- Edge at the lower endpoint of the first square coordinate. -/
@[expose] def tensorSquareLeftEdge {m : ℕ} (f : ↥(cubeBoundarySquares m)) :
    ↥(cubeBoundaryEdges m) :=
  ⟨(f.val.1, f.val.2.val.2), (cubeBoundarySquares_edges_mem f.property).2.2.1⟩

/-- Edge at the upper endpoint of the first square coordinate. -/
@[expose] def tensorSquareRightEdge {m : ℕ} (f : ↥(cubeBoundarySquares m)) :
    ↥(cubeBoundaryEdges m) :=
  ⟨(f.val.1 + Pi.single f.val.2.val.1 (1 : ℤ), f.val.2.val.2),
    (cubeBoundarySquares_edges_mem f.property).2.2.2⟩

/-- Actual tensor face graphs on the affine coordinates of one physical
boundary cube. Their transverse L² traces belong to that cube's edge
representatives. -/
structure PenalizedSphereFaces (a : BulkCoefficients) (B h : ℝ) (v : UnitTensorSphere → S0)
    (hv : MemSphereH1 v) where
  ht_pos : 0 < h
  grid : PenalizedSphereGrid a B h v hv
  face : ↥(cubeBoundarySquares grid.level) → Domain 2 → S0
  derivative : ↥(cubeBoundarySquares grid.level) → Domain 2 → Fin 2 → S0
  face_memW12 : ∀ f, MemW12 (tensorGridOpenParameterBox 2 h)
    (fun s => frobeniusCoordinateEquiv (face f s))
    (fun s i => frobeniusCoordinateEquiv (derivative f s i))
  face_eq : ∀ f s, s 0 ∈ Icc 0 h → s 1 ∈ Icc 0 h → ∃ θ : UnitTensorSphere,
    θ.val = NormedSpace.normalize
      (tensorGridSquarePoint (tensorGridVertex grid.center h f.val.1) f.val.2 (s 0) (s 1)) ∧
    face f s = v θ
  face_trace : ∀ f,
    let μ := volume.restrict (tensorGridOpenParameterBox 1 h).val
    ∃ H : C(Icc (0 : ℝ) h, Lp S0 2 μ),
      (∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (0 : ℝ) h,
        ∃ hs : MemLp (fun s : Domain 1 => face f (WithLp.toLp 2 ![s 0, t])) 2 μ,
          H ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp _) ∧
      (∃ hg₀ : MemLp (fun s : Domain 1 => grid.trace (tensorSquareLowerEdge f) (s 0)) 2 μ,
        H ⟨0, le_rfl, le_of_lt ht_pos⟩ = hg₀.toLp _) ∧
      (∃ hg₁ : MemLp (fun s : Domain 1 => grid.trace (tensorSquareUpperEdge f) (s 0)) 2 μ,
        H ⟨h, le_of_lt ht_pos, le_rfl⟩ = hg₁.toLp _)
  face_trace_cross : ∀ f,
    let μ := volume.restrict (tensorGridOpenParameterBox 1 h).val
    ∃ H : C(Icc (0 : ℝ) h, Lp S0 2 μ),
      (∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (0 : ℝ) h,
        ∃ hs : MemLp (fun s : Domain 1 => face f (WithLp.toLp 2 ![t, s 0])) 2 μ,
          H ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp _) ∧
      (∃ hg₀ : MemLp (fun s : Domain 1 => grid.trace (tensorSquareLeftEdge f) (s 0)) 2 μ,
        H ⟨0, le_rfl, le_of_lt ht_pos⟩ = hg₀.toLp _) ∧
      (∃ hg₁ : MemLp (fun s : Domain 1 => grid.trace (tensorSquareRightEdge f) (s 0)) 2 μ,
        H ⟨h, le_of_lt ht_pos, le_rfl⟩ = hg₁.toLp _)

private theorem compLpL_of_eqOn_edge_trace {h : ℝ} {u : ℝ → S0} {raw : ℝ → Ambient 7}
    (hEq : EqOn u (fun t => decodeTensorCoordinates (raw t)) (Icc 0 h))
    (hRaw : MemLp (fun s : Domain 1 => raw (s 0)) 2
      (volume.restrict (tensorGridOpenParameterBox 1 h).val)) :
    let μ := volume.restrict (tensorGridOpenParameterBox 1 h).val
    ∃ hu : MemLp (fun s : Domain 1 => u (s 0)) 2 μ,
      decodeTensorCoordinates.compLpL 2 μ (hRaw.toLp _) = hu.toLp _ := by
  intro μ
  have heq : (fun s : Domain 1 => u (s 0)) =ᵐ[μ] (fun s : Domain 1 => decodeTensorCoordinates (raw (s 0))) := by
    filter_upwards [ae_restrict_mem (tensorGridOpenParameterBox 1 h).property.measurableSet] with s hs
    exact hEq (Ioo_subset_Icc_self (mem_iInter.mp hs 0))
  have hd := hRaw.continuousLinearMap_comp decodeTensorCoordinates
  have hu := (memLp_congr_ae heq).mpr hd
  exact ⟨hu, (compLpL_toLp_tensor hRaw).trans (MemLp.toLp_congr hd hu heq.symm)⟩

/-- The actual tensor atlas, both edge bounds and both square bounds hold on
one selected cube. The square energies use the physical native coordinates. -/
theorem exists_penalizedSphereFaces_with_face_budgets (a : BulkCoefficients) (B : ℝ) (hB : 0 ≤ B) :
    ∃ C > (0 : ℝ), ∀ (u : UnitTensorSphere → S0) (hu : MemSphereH1 u),
      (∀ᵐ θ ∂tensorSphereMeasure, ‖u θ‖ ≤ B) → ∀ {h : ℝ}, 0 < h → h ≤ 1 / 32 →
      ∃ (v : UnitTensorSphere → S0) (hv : MemSphereH1 v),
        u =ᵐ[tensorSphereMeasure] v ∧ (∀ θ, ‖v θ‖ ≤ B) ∧
        sphereGradientEnergy v hv = sphereGradientEnergy u hu ∧
        ∃ G : PenalizedSphereFaces a B h v hv,
          (∑ e, ∫ t in Ioo (0 : ℝ) h, ‖G.grid.derivative e t‖ ^ 2) ≤ C / h * sphereGradientEnergy u hu ∧
          (∑ e, ∫ t in Ioo (0 : ℝ) h, bulkPotential a (G.grid.trace e t)) ≤
            C / h * (∫ θ : UnitTensorSphere, bulkPotential a (u θ) ∂tensorSphereMeasure) ∧
          (∑ f, ∫⁻ s in (tensorGridOpenParameterBox 2 h).val,
            ENNReal.ofReal (∑ i, ‖G.derivative f s i‖ ^ 2)) ≤ ENNReal.ofReal (6 * C * sphereGradientEnergy u hu) ∧
          (∑ f, ∫⁻ s in (tensorGridOpenParameterBox 2 h).val, ENNReal.ofReal (bulkPotential a (G.face f s))) ≤
            ENNReal.ofReal (6 * C * ∫ θ : UnitTensorSphere, bulkPotential a (u θ) ∂tensorSphereMeasure) := by
  classical
  letI : CompleteSpace S0 := complete_of_proper
  obtain ⟨K, hK, hChannels⟩ := exists_sphere_pair_penalized_grid_channels a B hB
  let n : ℝ := Fintype.card TensorGridSample
  have hn : 0 < n := Nat.cast_pos.mpr Fintype.card_pos
  let C := max (768 * n * K) (4096 * n)
  have hC : 0 < C := (mul_pos (by norm_num) hn).trans_le (le_max_right _ _)
  refine ⟨C, hC, ?_⟩
  intro u hu huB h hh hsmall
  obtain ⟨v, hv, hvu, hvB, hvGrad, N, P, hP, hN, hPN, hCoordinates, hPotential, hEnergy⟩ :=
    hChannels u hu huB
  obtain ⟨R⟩ := exists_sphereFaceGrid P hP hN (fun l => Eventually.of_forall (hPN l)) hh
  obtain ⟨T⟩ := R.exists_cube hsmall
  let E := ↥(cubeBoundaryEdges T.level)
  let F := ↥(cubeBoundarySquares T.level)
  let c := R.center
  let x (e : E) (t : ℝ) := tensorGridEdgePoint c h e.val t
  let y (f : F) (s : Domain 2) := tensorGridSquarePoint (tensorGridVertex c h f.val.1) f.val.2 (s 0) (s 1)
  let J := decodeTensorCoordinates
  have hc (i : Fin 3) : c i ∈ Icc (0 : ℝ) (1 / 32) :=
    ⟨(R.offset_mem i).1, (R.offset_mem i).2.le.trans hsmall⟩
  obtain ⟨_, _, _, chart, hInv, _, _⟩ := shiftedCoordinateCube_geometry hc T.radius_mem
  have hRay {z : Point} (hz : z ∈ frontier (shiftedCoordinateCube c ((T.level : ℝ) * h))) :
      ∃ θ : UnitTensorSphere, θ.val = NormedSpace.normalize z ∧ J (R.radialPair 0 z) = v θ ∧
        ‖R.radialPair 0 z - R.radialPair 1 z‖ ^ 2 = bulkPotential a (v θ) := by
    let θ := chart.symm ⟨z, hz⟩
    have hθ : θ.val = NormedSpace.normalize z := hInv ⟨z, hz⟩
    have hz₀ : z ≠ 0 := NormedSpace.norm_normalize_eq_one_iff.mp
      (hθ ▸ mem_sphere_zero_iff_norm.mp θ.property)
    let ρ : PositiveRadius := ⟨‖z‖, norm_pos_iff.mpr hz₀⟩
    have hw (l : Fin 2) : R.radialPair l z = P l θ := by
      have h := R.radial_eq l ρ θ
      change R.radialPair l (‖z‖ • θ.val) = P l θ at h
      simpa only [hθ, NormedSpace.norm_smul_normalize] using h
    exact ⟨θ, hθ, by rw [hw]; exact decodeTensorCoordinates_of_eq_coordinates _ _ (hCoordinates θ 0),
      by rw [hw, hw, hPotential]⟩
  choose raw hRep using fun e : E => T.edge_trace e.property 0
  let dRaw (e : E) (t : ℝ) := R.gradient 0 (x e t) e.val.2
  let d (e : E) (t : ℝ) := J (dRaw e t)
  let U (e : E) (t : ℝ) := J (raw e 0) + ∫ r in 0..t, d e r
  have hNative (e : E) : MemLp (dRaw e) 2 (volume.restrict (Ioo (0 : ℝ) h)) := by
    apply memLp_interval_of_nativeOne
    have hD := (T.edge_memW12 e.property 0).2.2 (0 : Fin 1)
    rwa [tensorGridOpenParameterBox_one_preimage] at hD
  have hEdge (e : E) := decode_tensor_edge_trace hh (hNative e) (hRep e).2.2.2.2
  have huEq (e : E) {t : ℝ} (ht : t ∈ Icc 0 h) : U e t = J (raw e t) := (hEdge e).2.2.1 ht
  have hTraceAe (e : E) : ∀ᵐ t ∂volume.restrict (Ioo 0 h), ∃ θ : UnitTensorSphere,
      θ.val = NormedSpace.normalize (x e t) ∧ U e t = v θ := by
    filter_upwards [(hRep e).2.1, ae_restrict_mem measurableSet_Ioo] with t ht ht'
    have htc := Ioo_subset_Icc_self ht'
    obtain ⟨θ, hθ, hEq, _⟩ := hRay (tensorGridEdgePoint_mem_frontier hh e.property htc)
    exact ⟨θ, hθ, by rw [huEq e htc, ht]; exact hEq⟩
  have hTraceBound (e : E) : ∀ t ∈ Icc 0 h, ‖U e t‖ ≤ B := by
    have hAe : ∀ᵐ t ∂volume.restrict (Ioo 0 h), U e t ∈ closedBall 0 B := (hTraceAe e).mono
      (fun t ⟨θ, _, hEq⟩ => mem_closedBall_zero_iff.mpr (hEq ▸ hvB θ))
    intro t ht
    exact mem_closedBall_zero_iff.mp
      (StratificationTheory.absolutelyContinuous_interval_mem_closed_of_ae hh (hEdge e).1
        EventuallyEq.rfl isClosed_closedBall hAe t ht)
  let G : PenalizedSphereGrid a B h v hv :=
    { center := c
      level := T.level
      offset_mem := R.offset_mem
      radius_mem := T.radius_mem
      trace := U
      derivative := d
      trace_ac := fun e => (hEdge e).1
      derivative_memLp := fun e => (hEdge e).2.1
      trace_increment := fun e => (hEdge e).2.2.2
      trace_bound := hTraceBound
      trace_ae := hTraceAe
      endpoint_eq := by
        intro e t ht
        rcases Set.mem_insert_iff.mp ht with h₀ | h₁
        · subst t
          have htc : (0 : ℝ) ∈ Icc 0 h := ⟨le_rfl, hh.le⟩
          obtain ⟨θ, hθ, hEq, _⟩ := hRay (tensorGridEdgePoint_mem_frontier hh e.property htc)
          exact ⟨θ, hθ, by rw [huEq e htc, (hRep e).2.2.1]; exact hEq⟩
        · have heq := Set.mem_singleton_iff.mp h₁
          subst t
          have htc : h ∈ Icc 0 h := ⟨hh.le, le_rfl⟩
          obtain ⟨θ, hθ, hEq, _⟩ := hRay (tensorGridEdgePoint_mem_frontier hh e.property htc)
          exact ⟨θ, hθ, by rw [huEq e htc, (hRep e).2.2.2.1]; exact hEq⟩ }
  let face (f : F) (s : Domain 2) := J (R.radialPair 0 (y f s))
  let dFace (f : F) (s : Domain 2) (i : Fin 2) :=
    J (R.gradient 0 (y f s) (tensorGridSquareDirections f.val.2 i))
  let atlas : PenalizedSphereFaces a B h v hv :=
    { ht_pos := hh
      grid := G
      face := face
      derivative := dFace
      face_memW12 := by
        intro f
        exact memW12_target_continuousLinearMap (T.square_memW12 f.property 0)
          (frobeniusCoordinateEquiv.toContinuousLinearEquiv.toContinuousLinearMap.comp J)
      face_eq := by
        intro f s hs ht
        obtain ⟨θ, hθ, hEq, _⟩ := hRay (tensorGridSquarePoint_mem_frontier hh f.property hs ht)
        exact ⟨θ, hθ, hEq⟩
      face_trace := by
        intro f μ
        let e₀ : E := tensorSquareLowerEdge f
        let e₁ : E := tensorSquareUpperEdge f
        obtain ⟨H, hInside, ⟨hg₀, h₀⟩, ⟨hg₁, h₁⟩⟩ :=
          T.square_trace_of_edge_representatives f.property 0 (hRep e₀).2.1 (hRep e₁).2.1
        let K : C(Icc (0 : ℝ) h, Lp S0 2 μ) :=
          ⟨fun t => J.compLpL 2 μ (H t), (J.compLpL 2 μ).continuous.comp H.continuous⟩
        refine ⟨K, ?_, ?_, ?_⟩
        · filter_upwards [hInside] with t ht ht'
          obtain ⟨hs, hClass⟩ := ht ht'
          have hs' : MemLp (fun s : Domain 1 => face f (WithLp.toLp 2 ![s 0, t])) 2 μ :=
            hs.continuousLinearMap_comp J
          refine ⟨hs', ?_⟩
          change J.compLpL 2 μ (H ⟨t, ht'.1.le, ht'.2.le⟩) = _
          rw [hClass]
          exact compLpL_toLp_tensor hs
        · obtain ⟨hu₀, hTop⟩ := compLpL_of_eqOn_edge_trace (fun _ ht => huEq e₀ ht) hg₀
          exact ⟨hu₀, (congrArg (J.compLpL 2 μ) h₀).trans hTop⟩
        · obtain ⟨hu₁, hTop⟩ := compLpL_of_eqOn_edge_trace (fun _ ht => huEq e₁ ht) hg₁
          exact ⟨hu₁, (congrArg (J.compLpL 2 μ) h₁).trans hTop⟩
      face_trace_cross := by
        intro f μ
        let e₀ : E := tensorSquareLeftEdge f
        let e₁ : E := tensorSquareRightEdge f
        obtain ⟨H, hInside, ⟨hg₀, h₀⟩, ⟨hg₁, h₁⟩⟩ :=
          T.square_trace_cross_of_edge_representatives f.property 0 (hRep e₀).2.1 (hRep e₁).2.1
        let K : C(Icc (0 : ℝ) h, Lp S0 2 μ) :=
          ⟨fun t => J.compLpL 2 μ (H t), (J.compLpL 2 μ).continuous.comp H.continuous⟩
        refine ⟨K, ?_, ?_, ?_⟩
        · filter_upwards [hInside] with t ht ht'
          obtain ⟨hs, hClass⟩ := ht ht'
          have hs' : MemLp (fun s : Domain 1 => face f (WithLp.toLp 2 ![t, s 0])) 2 μ :=
            hs.continuousLinearMap_comp J
          refine ⟨hs', ?_⟩
          change J.compLpL 2 μ (H ⟨t, ht'.1.le, ht'.2.le⟩) = _
          rw [hClass]
          exact compLpL_toLp_tensor hs
        · obtain ⟨hu₀, hBot⟩ := compLpL_of_eqOn_edge_trace (fun _ ht => huEq e₀ ht) hg₀
          exact ⟨hu₀, (congrArg (J.compLpL 2 μ) h₀).trans hBot⟩
        · obtain ⟨hu₁, hTop⟩ := compLpL_of_eqOn_edge_trace (fun _ ht => huEq e₁ ht) hg₁
          exact ⟨hu₁, (congrArg (J.compLpL 2 μ) h₁).trans hTop⟩ }
  have hSum (f : TensorGridEdge → ℝ≥0∞) : (∑ e : E, f e.val) = ∑ e ∈ cubeBoundaryEdges T.level, f e := by
    change (∑ e ∈ (Finset.univ : Finset ↥(cubeBoundaryEdges T.level)), f e.val) = _
    rw [Finset.univ_eq_attach, Finset.sum_attach]
  have hSumFace (g : TensorGridSquare → ℝ≥0∞) : (∑ f : F, g f.val) = ∑ f ∈ cubeBoundarySquares T.level, g f := by
    change (∑ f ∈ (Finset.univ : Finset ↥(cubeBoundarySquares T.level)), g f.val) = _
    rw [Finset.univ_eq_attach, Finset.sum_attach]
  have hRawPot : (∫ θ : UnitTensorSphere, ‖P 0 θ - P 1 θ‖ ^ 2 ∂tensorSphereMeasure) =
      ∫ θ : UnitTensorSphere, bulkPotential a (u θ) ∂tensorSphereMeasure :=
    integral_congr_ae (hvu.mono (fun θ ht => (hPotential θ).trans (congrArg _ ht.symm)))
  refine ⟨v, hv, hvu, hvB, hvGrad, atlas, ?_, ?_, ?_, ?_⟩
  · have hNonneg : 0 ≤ sphereGradientEnergy u hu :=
      integral_nonneg (fun _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (div_nonneg hC.le hh.le) hNonneg)).mp
    rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => integral_nonneg fun _ => sq_nonneg _)]
    change (∑ e : E, ENNReal.ofReal (∫ t in Ioo (0 : ℝ) h, ‖d e t‖ ^ 2)) ≤ _
    calc
      _ ≤ ∑ e : E, ∫⁻ t in Ioo (0 : ℝ) h, ENNReal.ofReal
          (hsNormSq (R.gradient 0 (x e t)) + hsNormSq (R.gradient 1 (x e t))) := by
        apply Finset.sum_le_sum
        intro e _
        rw [ofReal_integral_eq_lintegral_ofReal ((hEdge e).2.1.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0))
          (Eventually.of_forall (fun _ => sq_nonneg _))]
        apply lintegral_mono
        intro t
        apply ENNReal.ofReal_le_ofReal
        refine (norm_sq_decodeTensorCoordinates_le (dRaw e t)).trans ?_
        have hColumn : ‖dRaw e t‖ ^ 2 ≤ hsNormSq (R.gradient 0 (x e t)) :=
          Finset.single_le_sum (f := fun i => ‖R.gradient 0 (x e t) i‖ ^ 2)
            (fun i _ => sq_nonneg _) (Finset.mem_univ e.val.2)
        exact hColumn.trans (le_add_of_nonneg_right (hsNormSq_nonneg _))
      _ ≤ ENNReal.ofReal ((768 * n) / h) *
          ENNReal.ofReal (nativeSphereGradientEnergy (P 0) (hP 0) + nativeSphereGradientEnergy (P 1) (hP 1)) :=
        (hSum (fun e => ∫⁻ t in Ioo (0 : ℝ) h, ENNReal.ofReal
          (hsNormSq (R.gradient 0 (tensorGridEdgePoint c h e t)) +
            hsNormSq (R.gradient 1 (tensorGridEdgePoint c h e t))))).le.trans T.gradient_budget
      _ ≤ ENNReal.ofReal (C / h * sphereGradientEnergy u hu) := by
        calc
          _ ≤ ENNReal.ofReal ((768 * n) / h) * ENNReal.ofReal (K * sphereGradientEnergy u hu) :=
            mul_le_mul_right (ENNReal.ofReal_le_ofReal hEnergy) _
          _ = ENNReal.ofReal ((768 * n * K / h) * sphereGradientEnergy u hu) := by
            rw [← ENNReal.ofReal_mul (by positivity)]
            congr 1
            ring
          _ ≤ _ := ENNReal.ofReal_le_ofReal
            (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (le_max_left _ _) hh.le) hNonneg)
  · have hNonneg : 0 ≤ ∫ θ : UnitTensorSphere, bulkPotential a (u θ) ∂tensorSphereMeasure :=
      integral_nonneg (fun θ => bulkPotential_nonneg a (u θ))
    apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (div_nonneg hC.le hh.le) hNonneg)).mp
    rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => integral_nonneg fun _ => bulkPotential_nonneg a _)]
    change (∑ e : E, ENNReal.ofReal (∫ t in Ioo (0 : ℝ) h, bulkPotential a (U e t))) ≤ _
    calc
      _ = ∑ e : E, ∫⁻ t in Ioo (0 : ℝ) h,
          ENNReal.ofReal (‖R.radialPair 0 (x e t) - R.radialPair 1 (x e t)‖ ^ 2) := by
        apply Finset.sum_congr rfl
        intro e _
        have hCont : ContinuousOn (U e) (Icc (0 : ℝ) h) := by
          simpa only [uIcc_of_le hh.le] using! (hEdge e).1.continuousOn
        have hi : IntegrableOn (fun t => bulkPotential a (U e t)) (Ioo (0 : ℝ) h) :=
          ((contDiff_bulkPotential a).continuous.comp_continuousOn hCont).integrableOn_Icc.mono_set Ioo_subset_Icc_self
        rw [ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (fun _ => bulkPotential_nonneg a _))]
        apply lintegral_congr_ae
        filter_upwards [(hRep e).2.1, ae_restrict_mem measurableSet_Ioo] with t ht ht'
        have htc := Ioo_subset_Icc_self ht'
        obtain ⟨θ, _, hEq, hPot⟩ := hRay (tensorGridEdgePoint_mem_frontier hh e.property htc)
        rw [huEq e htc, ht, hEq, hPot]
      _ ≤ ENNReal.ofReal ((4096 * n) / h) *
          ENNReal.ofReal (∫ θ : UnitTensorSphere, ‖P 0 θ - P 1 θ‖ ^ 2 ∂tensorSphereMeasure) :=
        (hSum (fun e => ∫⁻ t in Ioo (0 : ℝ) h, ENNReal.ofReal
          (‖R.radialPair 0 (tensorGridEdgePoint c h e t) - R.radialPair 1 (tensorGridEdgePoint c h e t)‖ ^ 2))).le.trans
          T.discrepancy_budget
      _ ≤ _ := by
        rw [hRawPot, ENNReal.ofReal_mul (div_nonneg hC.le hh.le)]
        exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (le_max_right _ _) hh.le)) _
  · have hNonneg : 0 ≤ sphereGradientEnergy u hu :=
      integral_nonneg (fun _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    change (∑ f : F, ∫⁻ s in (tensorGridOpenParameterBox 2 h).val,
      ENNReal.ofReal (∑ i, ‖dFace f s i‖ ^ 2)) ≤ _
    calc
      _ ≤ ∑ f : F, ∫⁻ s in (tensorGridOpenParameterBox 2 h).val,
          ENNReal.ofReal (hsNormSq (R.gradient 0 (y f s)) + hsNormSq (R.gradient 1 (y f s))) := by
        apply Finset.sum_le_sum
        intro f _
        apply lintegral_mono
        intro s
        apply ENNReal.ofReal_le_ofReal
        let dir := tensorGridSquareDirections f.val.2
        calc
          _ ≤ ∑ i : Fin 2, ‖R.gradient 0 (y f s) (dir i)‖ ^ 2 :=
            Finset.sum_le_sum fun i _ => norm_sq_decodeTensorCoordinates_le _
          _ = ∑ i ∈ Finset.univ.map dir, ‖R.gradient 0 (y f s) i‖ ^ 2 := by rw [Finset.sum_map]
          _ ≤ hsNormSq (R.gradient 0 (y f s)) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => sq_nonneg _)
          _ ≤ _ := le_add_of_nonneg_right (hsNormSq_nonneg _)
      _ ≤ ENNReal.ofReal (4608 * n) *
          ENNReal.ofReal (nativeSphereGradientEnergy (P 0) (hP 0) + nativeSphereGradientEnergy (P 1) (hP 1)) := by
        exact (hSumFace (fun f => ∫⁻ s in (tensorGridOpenParameterBox 2 h).val,
          let x := tensorGridSquarePoint (tensorGridVertex c h f.1) f.2 (s 0) (s 1)
          ENNReal.ofReal (hsNormSq (R.gradient 0 x) + hsNormSq (R.gradient 1 x)))).le.trans T.square_gradient_budget
      _ ≤ ENNReal.ofReal (6 * C * sphereGradientEnergy u hu) := by
        calc
          _ ≤ ENNReal.ofReal (4608 * n) * ENNReal.ofReal (K * sphereGradientEnergy u hu) :=
            mul_le_mul_right (ENNReal.ofReal_le_ofReal hEnergy) _
          _ = ENNReal.ofReal (6 * (768 * n * K) * sphereGradientEnergy u hu) := by
            rw [← ENNReal.ofReal_mul (by positivity)]
            congr 1
            ring
          _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num)) hNonneg)
  · change (∑ f : F, ∫⁻ s in (tensorGridOpenParameterBox 2 h).val, ENNReal.ofReal (bulkPotential a (face f s))) ≤ _
    calc
      _ = ∑ f : F, ∫⁻ s in (tensorGridOpenParameterBox 2 h).val,
          ENNReal.ofReal (‖R.radialPair 0 (y f s) - R.radialPair 1 (y f s)‖ ^ 2) := by
        apply Finset.sum_congr rfl
        intro f _
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem (tensorGridOpenParameterBox 2 h).property.measurableSet] with s hs
        have hs₀ : s 0 ∈ Icc 0 h := Ioo_subset_Icc_self (mem_iInter.mp hs 0)
        have hs₁ : s 1 ∈ Icc 0 h := Ioo_subset_Icc_self (mem_iInter.mp hs 1)
        obtain ⟨θ, _, hEq, hPot⟩ := hRay (tensorGridSquarePoint_mem_frontier hh f.property hs₀ hs₁)
        change ENNReal.ofReal (bulkPotential a (J (R.radialPair 0 (y f s)))) = _
        rw [hEq, hPot]
      _ ≤ ENNReal.ofReal (24576 * n) * ENNReal.ofReal
          (∫ θ : UnitTensorSphere, ‖P 0 θ - P 1 θ‖ ^ 2 ∂tensorSphereMeasure) := by
        exact (hSumFace (fun f => ∫⁻ s in (tensorGridOpenParameterBox 2 h).val,
          let x := tensorGridSquarePoint (tensorGridVertex c h f.1) f.2 (s 0) (s 1)
          ENNReal.ofReal (‖R.radialPair 0 x - R.radialPair 1 x‖ ^ 2))).le.trans T.square_discrepancy_budget
      _ ≤ _ := by
        rw [hRawPot, ENNReal.ofReal_mul (by positivity : 0 ≤ 6 * C)]
        apply mul_le_mul_left
        apply ENNReal.ofReal_le_ofReal
        calc
          (24576 * n : ℝ) = 6 * (4096 * n) := by ring
          _ ≤ 6 * C := mul_le_mul_of_nonneg_left (le_max_right _ _) (by norm_num)

/-- The actual tensor face atlas and both controlled edge sums have one
native translated cube. The selected face graphs use affine physical cube coordinates. -/
theorem exists_penalizedSphereFaces (a : BulkCoefficients) (B : ℝ) (hB : 0 ≤ B) :
    ∃ C > (0 : ℝ), ∀ (u : UnitTensorSphere → S0) (hu : MemSphereH1 u),
      (∀ᵐ θ ∂tensorSphereMeasure, ‖u θ‖ ≤ B) → ∀ {h : ℝ}, 0 < h → h ≤ 1 / 32 →
      ∃ (v : UnitTensorSphere → S0) (hv : MemSphereH1 v),
        u =ᵐ[tensorSphereMeasure] v ∧ (∀ θ, ‖v θ‖ ≤ B) ∧
        sphereGradientEnergy v hv = sphereGradientEnergy u hu ∧
        ∃ G : PenalizedSphereFaces a B h v hv,
          (∑ e, ∫ t in Ioo (0 : ℝ) h, ‖G.grid.derivative e t‖ ^ 2) ≤ C / h * sphereGradientEnergy u hu ∧
          (∑ e, ∫ t in Ioo (0 : ℝ) h, bulkPotential a (G.grid.trace e t)) ≤
            C / h * ∫ θ : UnitTensorSphere, bulkPotential a (u θ) ∂tensorSphereMeasure := by
  obtain ⟨C, hC, hAtlas⟩ := exists_penalizedSphereFaces_with_face_budgets a B hB
  refine ⟨C, hC, fun u hu hRange {h} hh hsmall => ?_⟩
  obtain ⟨v, hv, hEq, hBound, hGrad, G, hg, hp, _, _⟩ := hAtlas u hu hRange hh hsmall
  exact ⟨v, hv, hEq, hBound, hGrad, G, hg, hp⟩

end Thesis

end
