module

public import Thesis.Interpolation.SquareCircleTrace
public import Thesis.Interpolation.VacuumDiskCollar
import StratificationTheory.Foundation.PositiveCubeSobolevDenormalization

/-! A vacuum filling of a null-homotopic centered square boundary. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set StratificationTheory
open scoped Matrix.Norms.Frobenius

namespace Thesis

/-- Sobolev traces on the four actual sides of the centered square. -/
structure CenteredSquareTraceData (u : Plane → Ambient 5) (b : UnitSquareBoundary → Ambient 5) where
  curve : Fin 2 → C(Icc (-1 : ℝ) 1, Lp (Ambient 5) 2 (volume.restrict (unitCellCube 1).val))
  slice : ∀ i : Fin 2, ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
    ∃ htLp : MemLp (fun x => u (unitCellFaceSlice i x t)) 2 (volume.restrict (unitCellCube 1).val),
      curve i ⟨t, ht.1.le, ht.2.le⟩ = htLp.toLp _
  edge : ∀ i (positive : Bool),
    (curve i ⟨if positive then 1 else -1, by cases positive <;> norm_num,
      by cases positive <;> norm_num⟩ : Domain 1 → Ambient 5) =ᵐ[volume.restrict (unitCellCube 1).val]
      fun x => b (unitSquareSideParameter i positive (x 0))

/-- Bi-Lipschitz Sobolev composition and the associated trace change of
variables for the verified radial square-to-disk chart. -/
@[expose] def External.UnitSquareDiskSobolevPullback : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (w : Plane → Ambient 5) (Dw : Plane → HarmonicMaps.Gradient 2 5),
    MemW12 (ballDomain (0 : Plane) 1) w Dw →
    ∀ (b : UnitSquareBoundary → Ambient 5) {s : ℝ} (hs : s < 1) (H : VacuumBallTrace 2 s),
      RepresentsVacuumBallTrace w H →
      (∃ hb : MemLp (fun θ => b (unitSquareCircleHomeomorph.symm θ)) 2 (unitBoundarySurface 2),
        H ⟨1, hs.le, le_rfl⟩ = hb.toLp _) →
      ∃ G : Plane → HarmonicMaps.Gradient 2 5,
        MemW12 (unitCellCube 2) (w ∘ planarSquareBallHomeomorph) G ∧
        Nonempty (CenteredSquareTraceData (w ∘ planarSquareBallHomeomorph) b) ∧
        (∫ x in (unitCellCube 2).val, hsNormSq (G x)) ≤ C * (∫ x in ball (0 : Plane) 1, hsNormSq (Dw x))

/-- The actual circle map obtained from a centered square boundary. -/
@[expose] def squareVacuumBoundaryLoop (a : BulkCoefficients) (b : C(UnitSquareBoundary, vacuum a)) :
    C(NativeCircle, vacuum a) := b.comp ⟨unitSquareCircleHomeomorph.symm, unitSquareCircleHomeomorph.symm.continuous⟩

/-- The Sobolev edge energy of a centered square boundary. -/
@[expose] def centeredSquareBoundaryGradientEnergy (b : C(UnitSquareBoundary, Tensor)) : ℝ :=
  ∑ i : Fin 2, ∑ j : Bool, ∫ t in Ioo (-1 : ℝ) 1, ‖deriv (b ∘ unitSquareSideParameter i j) t‖ ^ 2

private theorem vacuumLoopParameter_eval {T t : ℝ} (hT : 0 < T) (ht : t ∈ Icc 0 T) :
    T * (vacuumLoopParameter T t).val = t := by
  have ht' : t / T ∈ Icc (0 : ℝ) 1 := ⟨div_nonneg ht.1 hT.le, (div_le_one hT).2 ht.2⟩
  have hEq : (vacuumLoopParameter T t).val = t / T :=
    congrArg Subtype.val (projIcc_of_mem zero_le_one ht')
  rw [hEq, mul_comm, div_mul_cancel₀ _ hT.ne']

/-- The actual square boundary fills with the prescribed four side traces
and energy linear in their summed squared tangential derivatives. -/
theorem exists_unitSquare_vacuum_fill_of_null_boundary (a : BulkCoefficients)
    (hAngle : External.SquareBoundaryAngularSobolev) (hTransport : External.UnitSquareDiskSobolevPullback)
    (hCircular : External.PeriodicAngularSobolev) (hP : External.QuaternionSpherePoincare 2 (le_refl 2)) :
    ∃ C : ℝ, 0 < C ∧ ∀ b : C(UnitSquareBoundary, vacuum a),
      let B : C(UnitSquareBoundary, Tensor) := ⟨fun x => ((b x).val : Tensor),
        symmetricTraceless.subtypeL.continuous.comp (continuous_subtype_val.comp b.continuous)⟩
      let q := squareVacuumBoundaryLoop a b
      (∀ i : Fin 2, ∀ positive : Bool,
        let e := B ∘ unitSquareSideParameter i positive
        AbsolutelyContinuousOnInterval e (-1) 1 ∧
        MemLp (deriv e) 2 (volume.restrict (Ioo (-1 : ℝ) 1))) →
      q.Homotopic (ContinuousMap.const NativeCircle (q nativeCircleLoopBase)) →
      ∃ (w : Plane → Ambient 5) (Dw : Plane → HarmonicMaps.Gradient 2 5),
        MemW12 (unitCellCube 2) w Dw ∧
        (∀ᵐ x ∂volume.restrict (unitCellCube 2).val, frobeniusCoordinateEquiv.symm (w x) ∈ vacuum a) ∧
        Nonempty (CenteredSquareTraceData w (fun x => frobeniusCoordinateEquiv (b x).val)) ∧
        (∃ U : Set Plane, IsOpen U ∧ (frontier (unitCellCube 2).val) ⊆ U ∧ ContinuousOn w U ∧
          ∀ x : UnitSquareBoundary, w x.val = frobeniusCoordinateEquiv (b x).val) ∧
        (∫ x in (unitCellCube 2).val, hsNormSq (Dw x)) ≤ C * centeredSquareBoundaryGradientEnergy B := by
  obtain ⟨C₁, hC₁, hAngle⟩ := hAngle
  obtain ⟨C₂, hC₂, hTransport⟩ := hTransport
  obtain ⟨C₃, hC₃, hFill⟩ := exists_vacuum_disk_fill_of_null_loop a hCircular hP
  refine ⟨C₂ * (C₃ + 1) * C₁, mul_pos (mul_pos hC₂ (by positivity)) hC₁, ?_⟩
  intro b B q hB hNull
  obtain ⟨v, hv⟩ := vacuumQuaternionProjection_surjective a (q nativeCircleLoopBase)
  let γ := nativeVacuumLoopPath a q v hv
  have hγ : FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ) = 1 := by
    apply (vacuumFundamentalGroupEquiv a v).injective
    rw [map_one]
    exact (nativeVacuum_homotopic_const_iff a q v hv).1 hNull
  have hParam (t : ℝ) (ht : t ∈ Icc 0 (2 * Real.pi)) :
      γ (vacuumLoopParameter (2 * Real.pi) t) = q (circleNativeParam (t - Real.pi)) := by
    change nativeCircleLoop q (vacuumLoopParameter (2 * Real.pi) t) = _
    rw [nativeCircleLoop_apply, vacuumLoopParameter_eval Real.two_pi_pos ht]
  have hθ : vacuumLoopTensor γ (2 * Real.pi) = squareBoundaryAngularTensor B := by
    funext t
    change ((nativeCircleLoop q (vacuumLoopParameter (2 * Real.pi) t)).val : Tensor) = _
    rfl
  obtain ⟨hAC, hD, hθE⟩ := hAngle B hB
  have hACγ : AbsolutelyContinuousOnInterval (vacuumLoopTensor γ (2 * Real.pi)) 0 (2 * Real.pi) := by
    rw [hθ]
    exact hAC
  have hDγ : MemLp (deriv (vacuumLoopTensor γ (2 * Real.pi))) 2 (volume.restrict (Ioo 0 (2 * Real.pi))) := by
    rw [hθ]
    exact hD
  obtain ⟨s, hs, u, Du, H, _, hu, huN, hTrace, ⟨hLp, hEnd⟩, huE⟩ :=
    hFill v γ q hParam hACγ hDγ hγ
  obtain ⟨hq, hqE⟩ := exists_memSphereW12_of_vacuumAngular a hCircular q
    (fun t => γ (vacuumLoopParameter (2 * Real.pi) t)) (fun _ ht => hParam _ ht)
    hACγ hDγ
  have hEnd' : H ⟨1, hs.le, le_rfl⟩ = hq.1.toLp _ := hEnd
  obtain ⟨w, Dw, hw, hwN, hwCollar, hwTrace, hwE⟩ :=
    exists_vacuumDisk_with_radial_collar a nativeCircleLoopBase q hq hu huN hs H hTrace hEnd'
  let f (x : UnitSquareBoundary) := frobeniusCoordinateEquiv (b x).val
  obtain ⟨G, hSquare, hEdges, hEnergy⟩ := hTransport w Dw hw f (by norm_num)
    (ContinuousMap.const (Icc (1 / 2 : ℝ) 1) (hq.1.toLp _)) hwTrace ⟨hq.1, rfl⟩
  have hSZ : (unitCellCube 2).val = planarSquareBallHomeomorph ⁻¹' ball (0 : Plane) 1 :=
    planarSquare_one_eq_unitCellCube.symm.trans (planarSquare_eq_preimage_ball 1)
  have hVac : ∀ᵐ x ∂volume.restrict (unitCellCube 2).val,
      frobeniusCoordinateEquiv.symm ((w ∘ planarSquareBallHomeomorph) x) ∈ vacuum a := by
    rw [hSZ]
    apply (ae_restrict_iff' (planarSquareBallHomeomorph.continuous.measurable measurableSet_ball)).2
    exact planarSquareBallHomeomorph_quasiMeasurePreserving.ae ((ae_restrict_iff' measurableSet_ball).1 hwN)
  let U := {x : Plane | 1 / 2 < ‖planarSquareBallHomeomorph x‖}
  have hNorm (x : UnitSquareBoundary) : ‖planarSquareBallHomeomorph x.val‖ = 1 := by
    change ‖(unitSquareCircleHomeomorph x).val‖ = 1
    exact mem_sphere_zero_iff_norm.1 (unitSquareCircleHomeomorph x).property
  refine ⟨w ∘ planarSquareBallHomeomorph, G, hSquare, hVac, hEdges, ⟨U, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact isOpen_Ioi.preimage planarSquareBallHomeomorph.continuous.norm
  · intro x hx
    change (1 / 2 : ℝ) < ‖planarSquareBallHomeomorph x‖
    rw [hNorm ⟨x, hx⟩]
    norm_num
  · have hC : ContinuousOn (fun x : Plane => frobeniusCoordinateEquiv
        (q (sphereRadialDirection nativeCircleLoopBase x)).val) ({0}ᶜ : Set Plane) :=
      frobeniusCoordinateEquiv.continuous.comp_continuousOn
        ((continuous_subtype_val.comp q.continuous).comp_continuousOn
          (continuousOn_sphereRadialDirection nativeCircleLoopBase))
    refine (hC.comp planarSquareBallHomeomorph.continuous.continuousOn ?_).congr ?_
    · intro x hx hZero
      have h : planarSquareBallHomeomorph x = 0 := hZero
      change (1 / 2 : ℝ) < ‖planarSquareBallHomeomorph x‖ at hx
      rw [h, norm_zero] at hx
      norm_num at hx
    · intro x hx
      exact hwCollar _ hx.le
  · intro x
    have h : (1 / 2 : ℝ) ≤ ‖planarSquareBallHomeomorph x.val‖ := by rw [hNorm x]; norm_num
    change (1 / 2 : ℝ) ≤ ‖(unitSquareCircleHomeomorph x).val‖ at h
    change w (unitSquareCircleHomeomorph x).val = _
    rw [hwCollar _ h, sphereRadialDirection_unit]
    change frobeniusCoordinateEquiv (b (unitSquareCircleHomeomorph.symm (unitSquareCircleHomeomorph x))).val = _
    rw [Homeomorph.symm_apply_apply]
  · rw [hθ] at huE
    have hqE' : vacuumSphereGradientEnergy (le_refl 2) q hq ≤
        ∫ t in Ioo 0 (2 * Real.pi), ‖deriv (squareBoundaryAngularTensor B) t‖ ^ 2 := hqE.trans_eq
          (congrArg (fun g : ℝ → Tensor => ∫ t in Ioo 0 (2 * Real.pi), ‖deriv g t‖ ^ 2) hθ)
    calc
      _ ≤ C₂ * (∫ x in ball (0 : Plane) 1, hsNormSq (Dw x)) := hEnergy
      _ ≤ C₂ * ((∫ x in ball (0 : Plane) 1, hsNormSq (Du x)) +
          vacuumSphereGradientEnergy (le_refl 2) q hq) := mul_le_mul_of_nonneg_left hwE hC₂.le
      _ ≤ C₂ * (C₃ * (∫ t in Ioo 0 (2 * Real.pi), ‖deriv (squareBoundaryAngularTensor B) t‖ ^ 2) +
          ∫ t in Ioo 0 (2 * Real.pi), ‖deriv (squareBoundaryAngularTensor B) t‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add huE hqE') hC₂.le
      _ ≤ C₂ * ((C₃ + 1) * (C₁ * centeredSquareBoundaryGradientEnergy B)) := by
        rw [add_mul, one_mul]
        exact mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left hθE hC₃.le) hθE) hC₂.le
      _ = _ := by ring

private def CenteredSquareTraceData.physical {w : Plane → Ambient 5}
    {b : UnitSquareBoundary → Ambient 5} (T : CenteredSquareTraceData w b)
    {h : ℝ} (hh : 0 < h) (edge : Fin 2 → Bool → ℝ → Ambient 5)
    (hEdge : ∀ i p t, t ∈ Icc (0 : ℝ) h →
      edge i p t = b (unitSquareSideParameter i p ((t - h / 2) / (h / 2)))) :
    NormalizedSquareTraces h (fun x => w ((h / 2)⁻¹ • (x - WithLp.toLp 2 (fun _ => h / 2)))) edge := by
  let A (x : Plane) := (h / 2)⁻¹ • (x - WithLp.toLp 2 (fun _ => h / 2))
  have hInv (x : Plane) : A (unitToPhysicalCellFace h x) = x := by
    simp only [A, unitToPhysicalCellFace, add_sub_cancel_left, smul_smul,
      inv_mul_cancel₀ (half_pos hh).ne', one_smul]
  refine ⟨T.curve, ?_, ?_⟩
  · intro i
    filter_upwards [T.slice i] with t ht ht'
    have hEq : (fun x => w (A (unitToPhysicalCellFace h (unitCellFaceSlice i x t)))) =
        fun x => w (unitCellFaceSlice i x t) := funext fun x => congrArg w (hInv _)
    change ∃ hLp : MemLp (fun x => w (A (unitToPhysicalCellFace h (unitCellFaceSlice i x t)))) 2
        (volume.restrict (unitCellCube 1).val), T.curve i ⟨t, ht'.1.le, ht'.2.le⟩ = hLp.toLp _
    rw [hEq]
    exact ht ht'
  · intro i p
    filter_upwards [T.edge i p, ae_restrict_mem (unitCellCube 1).property.measurableSet] with x hx hxUnit
    have hX : x 0 ∈ Ioo (-1 : ℝ) 1 := by
      have h : x ∈ ⋂ j : Fin 1, (EuclideanSpace.proj j) ⁻¹' Ioo (-1 : ℝ) 1 := hxUnit
      exact mem_iInter.1 h 0
    have hT : unitEdgeToPhysical h x ∈ Icc 0 h := by
      unfold unitEdgeToPhysical
      constructor <;> nlinarith [mul_nonneg (half_pos hh).le (show 0 ≤ x 0 + 1 by linarith [hX.1]),
        mul_nonneg (half_pos hh).le (show 0 ≤ 1 - x 0 by linarith [hX.2])]
    have hId : (unitEdgeToPhysical h x - h / 2) / (h / 2) = x 0 := by
      unfold unitEdgeToPhysical
      rw [add_sub_cancel_left, mul_comm, mul_div_cancel_right₀ _ (half_pos hh).ne']
    rw [hx, hEdge i p _ hT, hId]

/-- The physical square filling retains the same prescribed edge classes.
The two-dimensional Dirichlet energy is invariant under the last similarity. -/
theorem exists_physicalSquare_vacuum_fill_of_null_boundary (a : BulkCoefficients)
    (hAngle : External.SquareBoundaryAngularSobolev) (hTransport : External.UnitSquareDiskSobolevPullback)
    (hCircular : External.PeriodicAngularSobolev) (hP : External.QuaternionSpherePoincare 2 (le_refl 2)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (h : ℝ), 0 < h → ∀ b : C(UnitSquareBoundary, vacuum a),
      let B : C(UnitSquareBoundary, Tensor) := ⟨fun x => ((b x).val : Tensor),
        symmetricTraceless.subtypeL.continuous.comp (continuous_subtype_val.comp b.continuous)⟩
      let q := squareVacuumBoundaryLoop a b
      (∀ i : Fin 2, ∀ positive : Bool,
        let e := B ∘ unitSquareSideParameter i positive
        AbsolutelyContinuousOnInterval e (-1) 1 ∧
        MemLp (deriv e) 2 (volume.restrict (Ioo (-1 : ℝ) 1))) →
      q.Homotopic (ContinuousMap.const NativeCircle (q nativeCircleLoopBase)) →
      ∀ edge : Fin 2 → Bool → ℝ → Ambient 5,
        (∀ i p t, t ∈ Icc (0 : ℝ) h → edge i p t =
          frobeniusCoordinateEquiv (b (unitSquareSideParameter i p ((t - h / 2) / (h / 2)))).val) →
        ∃ (w : Plane → Ambient 5) (Dw : Plane → HarmonicMaps.Gradient 2 5),
          MemW12 (tensorGridOpenParameterBox 2 h) w Dw ∧
          (∀ᵐ x ∂volume.restrict (tensorGridOpenParameterBox 2 h).val,
            frobeniusCoordinateEquiv.symm (w x) ∈ vacuum a) ∧
          Nonempty (NormalizedSquareTraces h w edge) ∧
          (∃ U : Set Plane, IsOpen U ∧ (∀ x : UnitSquareBoundary, unitToPhysicalCellFace h x.val ∈ U) ∧
            ContinuousOn w U ∧ ∀ i p (x : Domain 1), x 0 ∈ Icc (-1 : ℝ) 1 →
              w (unitToPhysicalCellFace h (unitCellFaceSlice i x (if p then 1 else -1))) =
                edge i p (unitEdgeToPhysical h x)) ∧
          (∫ x in (tensorGridOpenParameterBox 2 h).val, hsNormSq (Dw x)) ≤ C * centeredSquareBoundaryGradientEnergy B := by
  obtain ⟨C, hC, hFill⟩ := exists_unitSquare_vacuum_fill_of_null_boundary a hAngle hTransport hCircular hP
  refine ⟨C, hC, ?_⟩
  intro h hh b B q hB hQ edge hEdge
  obtain ⟨w, Dw, hw, hVac, ⟨T⟩, ⟨U, hU, hUS, hUC, hUB⟩, hEnergy⟩ := hFill b hB hQ
  obtain ⟨hw', hD, _, hVal⟩ := StratificationTheory.memW12_positive_cube_denormalization_energy hh w Dw hw
  let A (x : Plane) := (h / 2)⁻¹ • (x - WithLp.toLp 2 (fun _ => h / 2))
  let Dw' (x : Plane) (i : Fin 2) := (h / 2)⁻¹ • Dw (A x) i
  have hD' : (∫ x in (tensorGridOpenParameterBox 2 h).val, hsNormSq (Dw' x)) =
      ∫ x in (unitCellCube 2).val, hsNormSq (Dw x) := by
    change (∫ x in (tensorGridOpenParameterBox 2 h).val, hsNormSq (Dw' x)) =
      (h / 2) ^ ((2 : ℤ) - 2) * ∫ x in (unitCellCube 2).val, hsNormSq (Dw x) at hD
    simpa only [sub_self, zpow_zero, one_mul] using hD
  have hA : Continuous A := by dsimp only [A]; fun_prop
  have hInv (x : Plane) : A (unitToPhysicalCellFace h x) = x := by
    simp only [A, unitToPhysicalCellFace, add_sub_cancel_left, smul_smul,
      inv_mul_cancel₀ (half_pos hh).ne', one_smul]
  refine ⟨w ∘ A, Dw', hw', hVal (fun y => frobeniusCoordinateEquiv.symm y ∈ vacuum a) hVac,
    ⟨T.physical hh edge hEdge⟩, ⟨A ⁻¹' U, hU.preimage hA, ?_, ?_, ?_⟩, hD'.trans_le hEnergy⟩
  · intro x
    change A (unitToPhysicalCellFace h x.val) ∈ U
    rw [hInv]
    exact hUS x.property
  · exact hUC.comp hA.continuousOn (fun _ hx => hx)
  · intro i p x hx
    have hT : unitEdgeToPhysical h x ∈ Icc 0 h := by
      unfold unitEdgeToPhysical
      constructor <;> nlinarith [mul_nonneg (half_pos hh).le (show 0 ≤ x 0 + 1 by linarith [hx.1]),
        mul_nonneg (half_pos hh).le (show 0 ≤ 1 - x 0 by linarith [hx.2])]
    have hId : (unitEdgeToPhysical h x - h / 2) / (h / 2) = x 0 := by
      unfold unitEdgeToPhysical
      rw [add_sub_cancel_left, mul_comm, mul_div_cancel_right₀ _ (half_pos hh).ne']
    change w (A (unitToPhysicalCellFace h (unitCellFaceSlice i x (if p then 1 else -1)))) = _
    rw [hInv, hEdge i p _ hT, hId, ← unitSquareSideParameter_eq i p x hx]
    exact hUB _

end Thesis
