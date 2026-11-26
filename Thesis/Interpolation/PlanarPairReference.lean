module

public import Thesis.Interpolation.PlanarPairRecovery
public import Thesis.Interpolation.PlanarPairSobolevExterior
public import Thesis.MeasureGeometry.PlanarVacuumAnnulus
import Thesis.Foundation.VacuumTarget

/-! Fixed punctured-disk reference data and the ordered splitting comparison. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set StratificationTheory
open scoped Matrix.Norms.Frobenius

namespace Thesis

/-- The relative Sobolev extension of compatible based loops on a fixed
disk with two holes. The collars retain the round-circle parametrizations
of the three original boundary maps. -/
@[expose] def External.PuncturedDiskSobolevExtension : Prop :=
  ∀ {q : ℕ} (N : CompactSmoothEmbeddedTarget q) {X : Type} [TopologicalSpace X]
    (j : C(X, Ambient q)), Topology.IsEmbedding j → range j = N.carrierSet →
    ∀ (A : X) (outer : C(NativeCircle, X)) (inner : Fin 2 → C(NativeCircle, X))
      (h₀ : A = outer nativeCircleLoopBase) (hᵢ : ∀ i, A = inner i nativeCircleLoopBase),
      MemSphereW12 (le_refl 2) (fun z => j (outer z)) →
      (∀ i, MemSphereW12 (le_refl 2) (fun z => j (inner i z))) →
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk ((nativeCircleLoop outer).cast h₀ h₀)) =
        FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk ((nativeCircleLoop (inner 0)).cast (hᵢ 0) (hᵢ 0))) *
          FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk ((nativeCircleLoop (inner 1)).cast (hᵢ 1) (hᵢ 1))) →
      ∃ (w : Plane → Ambient q) (D : Plane → HarmonicMaps.Gradient 2 q),
        MemW12 planarPairExteriorDomain w D ∧
        (∀ᵐ z ∂volume.restrict planarPairExteriorDomain.val, w z ∈ N.carrierSet) ∧
        (∀ (i : Fin 2) (z : Plane), z ∈ planarPairExteriorDomain.val →
          z ∈ ball (planarPairCoreCenter i) (1 / 4) →
          w z = j (inner i (sphereRadialDirection nativeCircleLoopBase (z - planarPairCoreCenter i)))) ∧
        (∀ r ≥ (7 / 8 : ℝ), ∀ θ : NativeCircle, w (r • θ.val) = j (outer θ))

private theorem exists_basic_pair_for_splittingCost (a : BulkCoefficients) (v : Sphere3) (g : QuaternionGroup 2) :
    ∃ f : Fin 2 → QuaternionGroup 2,
      (∀ i, f i = 1 ∨ IsLightQuaternion (f i)) ∧ f 0 * f 1 = g ∧
      vacuumSplittingCost a v (f 0) + vacuumSplittingCost a v (f 1) = vacuumSplittingCost a v g := by
  by_cases hg : g = 1
  · subst g
    exact ⟨fun _ => 1, fun _ => Or.inl rfl, by simp, by simp [vacuumSplittingCost_one]⟩
  by_cases hLight : IsLightQuaternion g
  · refine ⟨![g, 1], ?_, by simp, by simp [vacuumSplittingCost_one]⟩
    intro i
    fin_cases i
    · exact Or.inr hLight
    · exact Or.inl rfl
  obtain ⟨f, hf, hProd⟩ := exists_two_light_factors_of_nontrivial_nonlight hg hLight
  refine ⟨f, fun i => Or.inr (hf i), hProd, ?_⟩
  rw [vacuumSplittingCost_light a v (hf 0), vacuumSplittingCost_light a v (hf 1),
    vacuumSplittingCost_nontrivial_nonlight a v hg hLight]
  ring

/-- A fixed actual native boundary admits a disk recovery with its
full free splitting cost. The finite additive constant may depend on
the fixed boundary map. -/
theorem exists_planarWeakRecovery_of_splittingCost (a : BulkCoefficients)
    (hPolar : External.PeriodicAngularSobolev)
    (b : C(NativeCircle, vacuum a))
    (hb : MemSphereW12 (le_refl 2) (fun θ => frobeniusCoordinateEquiv (b θ).val)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ε : ℝ}, 0 < ε → ε < 3 / 16 →
      ∃ (w : Plane → Ambient 5) (Dw : Plane → HarmonicMaps.Gradient 2 5),
        MemW12 (ballDomain (0 : Plane) 1) w Dw ∧
        (∀ᵐ x ∂volume.restrict (ball (0 : Plane) 1), ‖w x‖ ≤ Real.sqrt 2 * vacuumRadius a) ∧
        (∀ r ≥ (7 / 8 : ℝ), ∀ θ : NativeCircle, w (r • θ.val) = frobeniusCoordinateEquiv (b θ).val) ∧
        planarWeakEnergy a ε w Dw 1 ≤ nativeVacuumCircleCost a b * Real.log (1 / ε) + C := by
  obtain ⟨v, hv⟩ := vacuumQuaternionProjection_surjective a (b nativeCircleLoopBase)
  let g := nativeVacuumLoopWord a b v hv
  obtain ⟨f, hBasic, hProd, hCost⟩ := exists_basic_pair_for_splittingCost a v g
  obtain ⟨p, hp, hWord, hMem, hUpper⟩ :=
    exists_planarPairCores_of_fixed_exterior a hPolar v f hBasic b
  have hGroup :
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk ((nativeCircleLoop b).cast hv hv)) =
        FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk ((nativeCircleLoop (p 0)).cast (hp 0) (hp 0))) *
          FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk ((nativeCircleLoop (p 1)).cast (hp 1) (hp 1))) := by
    apply (vacuumFundamentalGroupEquiv a v).injective
    rw [map_mul]
    change g = nativeVacuumLoopWord a (p 0) v (hp 0) * nativeVacuumLoopWord a (p 1) v (hp 1)
    rw [hWord 0, hWord 1]
    exact hProd.symm
  obtain ⟨P⟩ := exists_planarPairExterior_of_vacuum_words a
    (vacuumQuaternionProjection a v) b p hv hp hb hMem hGroup
  obtain ⟨C, hC, h⟩ := hUpper P
  refine ⟨C, hC, ?_⟩
  intro ε hε hε₁
  obtain ⟨u, Du, hu, huB, huOut, hEn⟩ := h hε hε₁
  have hOuterCost : vacuumSplittingCost a v g = nativeVacuumCircleCost a b :=
    (nativeVacuumCircleCost_eq a b v hv).symm
  exact ⟨u, Du, hu, huB, huOut, hEn.trans_eq (by rw [hCost, hOuterCost])⟩

/-- Physical disk version of the fixed-boundary recovery, with the exact
source logarithm and no dependence of the additive constant on the scale. -/
theorem exists_planarWeakRecovery_on_ball_of_splittingCost (a : BulkCoefficients)
    (hPolar : External.PeriodicAngularSobolev)
    (b : C(NativeCircle, vacuum a))
    (hb : MemSphereW12 (le_refl 2) (fun θ => frobeniusCoordinateEquiv (b θ).val)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (c : Plane) {R ε : ℝ}, 0 < R → 0 < ε → ε < (3 / 16 : ℝ) * R →
      ∃ (w : Plane → Ambient 5) (Dw : Plane → HarmonicMaps.Gradient 2 5),
        MemW12 (ballDomain c R) w Dw ∧
        (∀ᵐ x ∂volume.restrict (ball c R), ‖w x‖ ≤ Real.sqrt 2 * vacuumRadius a) ∧
        (∀ r ≥ (7 / 8 : ℝ) * R, ∀ θ : NativeCircle, w (c + r • θ.val) = frobeniusCoordinateEquiv (b θ).val) ∧
        ((1 / 2 : ℝ) * (∫ x in ball c R, hsNormSq (Dw x)) +
          ε⁻¹ ^ 2 * ∫ x in ball c R, planarCoordinateBulkPotential a (w x)) ≤
            nativeVacuumCircleCost a b * Real.log (R / ε) + C := by
  obtain ⟨C, hC, hRec⟩ := exists_planarWeakRecovery_of_splittingCost a hPolar b hb
  refine ⟨C, hC, ?_⟩
  intro c R ε hR hε hCut
  let ζ := ε / R
  have hζ : 0 < ζ := div_pos hε hR
  have hζ₁ : ζ < 3 / 16 := (div_lt_iff₀ hR).2 hCut
  obtain ⟨u, Du, hu, huB, hRay, hEn⟩ := hRec hζ hζ₁
  obtain ⟨D, hw, hVal, hE⟩ := planarRecovery_affine a c (ε := ε) hR hu
  let w (x : Plane) := u (R⁻¹ • (x - c))
  have hwRay (r : ℝ) (hr : r ≥ (7 / 8 : ℝ) * R) (θ : NativeCircle) :
      w (c + r • θ.val) = frobeniusCoordinateEquiv (b θ).val := by
    change u (R⁻¹ • (c + r • θ.val - c)) = _
    rw [add_sub_cancel_left, smul_smul, mul_comm R⁻¹, ← div_eq_mul_inv]
    exact hRay (r / R) ((le_div_iff₀ hR).2 hr) θ
  have hLog : Real.log (1 / ζ) = Real.log (R / ε) := by
    rw [one_div, show ζ⁻¹ = R / ε from inv_div _ _]
  refine ⟨w, D, hw, hVal (fun z => ‖z‖ ≤ Real.sqrt 2 * vacuumRadius a) huB, hwRay,
    hE.le.trans (hEn.trans_eq ?_)⟩
  rw [hLog]

end Thesis
