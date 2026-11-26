module

public import Thesis.Interpolation.CylinderBoundaryTrace

/-! The terminal and middle fields as one competitor on the original
oriented cylinder. -/

@[expose] public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set
open scoped ContDiff ENNReal Matrix.Norms.Frobenius Topology

namespace Thesis.MeasureGeometry

private theorem cylinderClosed_subset_of_height_subset (B : OrthonormalBasis (Fin 3) ℝ Point)
    (c : Point) (R : ℝ) {a b l h : ℝ} (ha : l ≤ a) (hb : b ≤ h) :
    translatedClosedAxisCylinder c (B 2) R a b ⊆ translatedClosedAxisCylinder c (B 2) R l h := by
  intro x hx
  have hx' : x - c ∈ closedAxisCylinder (B 2) R a b := hx
  exact show x - c ∈ closedAxisCylinder (B 2) R l h from ⟨hx'.1, ha.trans hx'.2.1, hx'.2.2.trans hb⟩

private theorem matchingCylinderSideTraces_of_continuous_reference {q : ℕ}
    (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point) {R lo hi : ℝ} (hR : 0 < R) (hI : lo < hi)
    {u v : Point → Ambient q}
    (hv : ContinuousOn v (translatedClosedAxisCylinder c (B 2) R lo hi))
    (P : CylinderSideL2Trace q R lo hi) (hP : RepresentsCylinderSideL2Trace B c u P)
    (hMatch : (P ⟨R, half_le_self hR.le, le_rfl⟩ : NativeCircle × ℝ → Ambient q)
      =ᵐ[cylinderSideTraceMeasure lo hi] fun p => v (c + axisChart B (R • p.1.val, p.2))) :
    MatchingCylinderSideTraces B c hR lo hi u v := by
  obtain ⟨T, Q, hT, hQ, _, hRaw⟩ := exists_cylinderBoundaryL2Traces_of_continuousOn_closed B c hR hI hv
  exact ⟨P, Q, hP, hQ, Lp.ext (hMatch.trans (hRaw ⟨R, half_le_self hR.le, le_rfl⟩).symm)⟩

/-- The raw exterior values and the two native interior disk classes
are prescribed in the same physical frame. -/
structure CylinderTerminalRimMatches
    (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point) {R lo hi : ℝ} (hR : 0 < R)
    (hCut : lo + R / 2 < hi - R / 2)
    (L U : TerminalCylinderBoundaryData 5 R hR) (g : Point → S0)
    (P : CylinderHeightL2Trace 5 R (lo + R / 2) (hi - R / 2))
    (Q : CylinderSideL2Trace 5 R (lo + R / 2) (hi - R / 2)) : Prop where
  exteriorLower : L.lower =ᵐ[volume.restrict (ball (0 : Plane) R)]
    fun y => frobeniusField g (c + axisChart B (y, lo))
  exteriorUpper : U.upper =ᵐ[volume.restrict (ball (0 : Plane) R)]
    fun y => frobeniusField g (c + axisChart B (y, hi))
  interiorLower : (P ⟨lo + R / 2, le_rfl, hCut.le⟩ : Plane → Ambient 5)
    =ᵐ[volume.restrict (ball (0 : Plane) R)] L.upper
  interiorUpper : (P ⟨hi - R / 2, hCut.le, le_rfl⟩ : Plane → Ambient 5)
    =ᵐ[volume.restrict (ball (0 : Plane) R)] U.lower
  lowerWall : (fun p : NativeCircle × ℝ =>
    terminalCylinderSurfaceValue B (cylinderTerminalCenter B c lo (lo + R / 2)) (R / 4) L
      (c + axisChart B (R • p.1.val, p.2))) =ᵐ[cylinderSideTraceMeasure lo (lo + R / 2)]
    fun p => frobeniusField g (c + axisChart B (R • p.1.val, p.2))
  middleWall : (Q ⟨R, half_le_self hR.le, le_rfl⟩ : NativeCircle × ℝ → Ambient 5)
    =ᵐ[cylinderSideTraceMeasure (lo + R / 2) (hi - R / 2)]
    fun p => frobeniusField g (c + axisChart B (R • p.1.val, p.2))
  upperWall : (fun p : NativeCircle × ℝ =>
    terminalCylinderSurfaceValue B (cylinderTerminalCenter B c (hi - R / 2) hi) (R / 4) U
      (c + axisChart B (R • p.1.val, p.2))) =ᵐ[cylinderSideTraceMeasure (hi - R / 2) hi]
    fun p => frobeniusField g (c + axisChart B (R • p.1.val, p.2))

/-- Two compatible terminal boundaries and the original middle field
give a single admissible competitor, with the exact middle energy and the
sum of the two terminal surface costs multiplied by the radius. -/
theorem exists_cylinderRecoveryCompetitor (a : BulkCoefficients)
    (hSurf : External.TerminalCylinderSurfaceSobolev) (hTransport : External.AmbientBiLipschitzSobolevPullback3)
    (hChartTrace : External.CylinderBoundaryChartTraceTransport) (hKernel : External.CylinderBoundaryTraceKernel) :
    ∃ K : ℝ, 0 < K ∧ ∀ (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point)
      {R lo hi : ℝ} (hR : 0 < R) (hCut : lo + R / 2 < hi - R / 2)
      (ε : ElasticScale) (L U : TerminalCylinderBoundaryData 5 R hR) (M : ℝ),
      L.Bounded M → U.Bounded M →
      ∀ (v g : Point → S0) (Dv Dg : Point → Thesis.Gradient),
      MemH1 (translatedAxisCylinder c (B 2) R (lo + R / 2) (hi - R / 2)) v Dv →
      MemH1 (translatedAxisCylinder c (B 2) R lo hi) g Dg →
      ContinuousOn g (translatedClosedAxisCylinder c (B 2) R lo hi) →
      ∀ (P : CylinderHeightL2Trace 5 R (lo + R / 2) (hi - R / 2))
        (Q : CylinderSideL2Trace 5 R (lo + R / 2) (hi - R / 2)),
      RepresentsCylinderHeightL2Trace B c (frobeniusField v) P →
      RepresentsCylinderSideL2Trace B c (frobeniusField v) Q →
      CylinderTerminalRimMatches B c hR hCut L U g P Q →
      ∃ (u : Point → S0) (Du : Point → Thesis.Gradient),
        MemH1 (translatedAxisCylinder c (B 2) R lo hi) u Du ∧
        SameTrace (translatedAxisCylinder c (B 2) R lo hi) u g Du Dg ∧
        energy a ε (translatedAxisCylinder c (B 2) R lo hi) u Du ≤
          energy a ε (translatedAxisCylinder c (B 2) R (lo + R / 2) (hi - R / 2)) v Dv +
            ENNReal.ofReal (K * R) *
              (terminalCylinderSurfacePenalizedEnergy a ε (R / 4) L +
                terminalCylinderSurfacePenalizedEnergy a ε (R / 4) U) := by
  obtain ⟨K, hK, hTerm⟩ := exists_penalized_terminalAxisCylinder_fill a hSurf hTransport hChartTrace
  refine ⟨K, hK, ?_⟩
  intro B c R lo hi hR hCut ε L U M hL hU v g Dv Dg hv hg hgC P Q hP hQ hMatch
  let b := lo + R / 2
  let d := hi - R / 2
  have hlb : lo < b := by dsimp only [b]; linarith only [hR]
  have hbd : b < d := hCut
  have hdh : d < hi := by dsimp only [d]; linarith only [hR]
  have hI : lo < hi := hlb.trans (hbd.trans hdh)
  have hLenL : (b - lo) / 2 = R / 4 := by dsimp only [b]; ring
  have hLenU : (hi - d) / 2 = R / 4 := by dsimp only [d]; ring
  have hLen : R / 4 ≤ R := by linarith only [hR]
  obtain ⟨u, Du, A, C, hu, hA, hC, hExtL, hInL, hWallL, _, _, hEnergyL⟩ :=
    hTerm B c hR hlb hLenL.ge (hLenL.le.trans hLen) ε L M hL
  obtain ⟨w, Dw, S, N, hw, hS, hN, hInU, hExtU, hWallU, _, _, hEnergyU⟩ :=
    hTerm B c hR hdh hLenU.ge (hLenU.le.trans hLen) ε U M hU
  have hG : ContinuousOn (frobeniusField g) (translatedClosedAxisCylinder c (B 2) R lo hi) :=
    frobeniusCoordinateEquiv.continuous.comp_continuousOn hgC
  obtain ⟨T, W, hT, hW, hTval, _⟩ := exists_cylinderBoundaryL2Traces_of_continuousOn_closed B c hR hI hG
  have hOutsideL : A ⟨lo, le_rfl, hlb.le⟩ = T ⟨lo, le_rfl, hI.le⟩ :=
    Lp.ext (hExtL.trans (hMatch.exteriorLower.trans (hTval ⟨lo, le_rfl, hI.le⟩).symm))
  have hOutsideU : S ⟨hi, hdh.le, le_rfl⟩ = T ⟨hi, hI.le, le_rfl⟩ :=
    Lp.ext (hExtU.trans (hMatch.exteriorUpper.trans (hTval ⟨hi, hI.le, le_rfl⟩).symm))
  have hInsideL : A ⟨b, hlb.le, le_rfl⟩ = P ⟨b, le_rfl, hbd.le⟩ :=
    Lp.ext (hInL.trans hMatch.interiorLower.symm)
  have hInsideU : P ⟨d, hbd.le, le_rfl⟩ = S ⟨d, le_rfl, hdh.le⟩ :=
    Lp.ext (hMatch.interiorUpper.trans hInU.symm)
  have hSideL : MatchingCylinderSideTraces B c hR lo b (frobeniusField u) (frobeniusField g) :=
    matchingCylinderSideTraces_of_continuous_reference B c hR hlb
      (hG.mono (cylinderClosed_subset_of_height_subset B c R le_rfl (hbd.trans hdh).le)) C hC
      (hWallL.trans (by simpa only [hLenL] using hMatch.lowerWall))
  have hSideM : MatchingCylinderSideTraces B c hR b d (frobeniusField v) (frobeniusField g) :=
    matchingCylinderSideTraces_of_continuous_reference B c hR hbd
      (hG.mono (cylinderClosed_subset_of_height_subset B c R hlb.le hdh.le)) Q hQ hMatch.middleWall
  have hSideU : MatchingCylinderSideTraces B c hR d hi (frobeniusField w) (frobeniusField g) :=
    matchingCylinderSideTraces_of_continuous_reference B c hR hdh
      (hG.mono (cylinderClosed_subset_of_height_subset B c R (hlb.trans hbd).le le_rfl)) N hN
      (hWallU.trans (by simpa only [hLenU] using hMatch.upperWall))
  obtain ⟨hSob, hSame⟩ := cylinderThreePiecewise_memH1_sameTrace hKernel B c hR hlb hbd hdh
    u v w g Du Dv Dw Dg hu hv hw hg A P S T hA hP hS hT hInsideL hInsideU hOutsideL hOutsideU hSideL hSideM hSideU
  refine ⟨cylinderThreePiecewise B c b d u v w, cylinderThreePiecewise B c b d Du Dv Dw, hSob, hSame, ?_⟩
  rw [energy_cylinderThreePiecewise_eq_sum a ε B c R hlb hbd hdh]
  have hL' : energy a ε (translatedAxisCylinder c (B 2) R lo b) u Du ≤
      ENNReal.ofReal (K * R) * terminalCylinderSurfacePenalizedEnergy a ε (R / 4) L := by
    simpa only [hLenL] using hEnergyL
  have hU' : energy a ε (translatedAxisCylinder c (B 2) R d hi) w Dw ≤
      ENNReal.ofReal (K * R) * terminalCylinderSurfacePenalizedEnergy a ε (R / 4) U := by
    simpa only [hLenU] using hEnergyU
  exact (add_le_add (add_le_add hL' le_rfl) hU').trans_eq (by rw [mul_add]; ac_rfl)

end Thesis.MeasureGeometry

end
