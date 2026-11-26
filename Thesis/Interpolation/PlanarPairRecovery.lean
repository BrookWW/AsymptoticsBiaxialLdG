module

public import Thesis.Interpolation.PlanarCoreRecovery
import StratificationTheory.Foundation.SobolevLocalAssembly
import HarmonicMaps.Analysis.SobolevAECongruence

/-! The two displaced planar cores and their actual common vacuum exterior. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set StratificationTheory
open scoped Matrix.Norms.Frobenius

namespace Thesis

/-- The fixed centers of the two disjoint reference disks. -/
@[expose] def planarPairCoreCenter (i : Fin 2) : Plane := EuclideanSpace.single 0 (if i = 0 then -1 / 2 else 1 / 2)

private theorem norm_planarPairCoreCenter (i : Fin 2) : ‖planarPairCoreCenter i‖ = 1 / 2 := by
  rw [planarPairCoreCenter, PiLp.norm_single]
  split <;> norm_num

private theorem dist_planarPairCoreCenter : dist (planarPairCoreCenter 0) (planarPairCoreCenter 1) = 1 := by
  have hD : planarPairCoreCenter 0 - planarPairCoreCenter 1 = EuclideanSpace.single 0 (-1) := by
    apply PiLp.ext
    intro i
    fin_cases i <;> norm_num [planarPairCoreCenter, PiLp.sub_apply, PiLp.single_apply]
  rw [dist_eq_norm, hD, PiLp.norm_single]
  norm_num

private theorem pairCore_balls_disjoint :
    Disjoint (ball (planarPairCoreCenter 0) (1 / 4)) (ball (planarPairCoreCenter 1) (1 / 4)) :=
  ball_disjoint_ball (by rw [dist_planarPairCoreCenter]; norm_num)

private theorem pairCore_ball_subset (i : Fin 2) :
    ball (planarPairCoreCenter i) (1 / 4) ⊆ ball (0 : Plane) 1 := by
  intro z hz
  rw [mem_ball] at hz
  rw [mem_ball, dist_zero_right]
  have h := dist_triangle z (planarPairCoreCenter i) 0
  rw [dist_zero_right, dist_zero_right] at h
  linarith only [h, hz, norm_planarPairCoreCenter i]

/-- A fixed exterior overlapping the two physical rim circles, so the
native charts can be glued on genuine open collars. -/
@[expose] def planarPairExteriorDomain : OpenDomain 2 :=
  ⟨ball (0 : Plane) 1 ∩ ⋂ i : Fin 2, {z | 3 / 16 < dist z (planarPairCoreCenter i)},
    isOpen_ball.inter (isOpen_iInter_of_finite fun _ => isOpen_lt continuous_const (continuous_id.dist continuous_const))⟩

/-- A fixed reference vacuum map on the twice-punctured disk with the
original three round-circle data on collars. -/
structure PlanarPairExterior (a : BulkCoefficients) (outer : C(NativeCircle, vacuum a))
    (inner : Fin 2 → C(NativeCircle, vacuum a)) where
  field : Plane → Ambient 5
  columns : Plane → HarmonicMaps.Gradient 2 5
  sobolev : MemW12 planarPairExteriorDomain field columns
  vacuum_ae : ∀ᵐ x ∂volume.restrict planarPairExteriorDomain.val,
    frobeniusCoordinateEquiv.symm (field x) ∈ vacuum a
  inner_collar : ∀ (i : Fin 2) (x : Plane), x ∈ planarPairExteriorDomain.val →
    x ∈ ball (planarPairCoreCenter i) (1 / 4) →
    field x = frobeniusCoordinateEquiv ((inner i) (sphereRadialDirection nativeCircleLoopBase
      (x - planarPairCoreCenter i))).val
  outer_collar : ∀ (r : ℝ), 7 / 8 ≤ r → ∀ θ : NativeCircle,
    field (r • θ.val) = frobeniusCoordinateEquiv (outer θ).val

private theorem planarCore_eval_near_rim {a : BulkCoefficients} {b : C(NativeCircle, vacuum a)} {u : Plane → Ambient 5}
    {c : Plane} {ε : ℝ} (hε : 0 < ε)
    (hRay : ∀ r ≥ ε, ∀ θ : NativeCircle, u (c + r • θ.val) = frobeniusCoordinateEquiv (b θ).val)
    {x : Plane} (hx : ε ≤ dist x c) :
    u x = frobeniusCoordinateEquiv (b (sphereRadialDirection nativeCircleLoopBase (x - c))).val := by
  have hNorm : ε ≤ ‖x - c‖ := dist_eq_norm x c ▸ hx
  have hNe := norm_ne_zero_iff.mp (ne_of_gt (hε.trans_le hNorm))
  let θ := sphereRadialDirection nativeCircleLoopBase (x - c)
  have hDecomp : c + ‖x - c‖ • θ.val = x := by
    change c + ‖x - c‖ • (sphereRadialDirection nativeCircleLoopBase (x - c)).val = x
    rw [sphereRadialDirection, dif_pos hNe, NormedSpace.norm_smul_normalize, add_sub_cancel]
  exact (congrArg u hDecomp).symm.trans (hRay _ hNorm θ)

private theorem memLp_two_union {E : Type*} [NormedAddCommGroup E] {u : Plane → E}
    {A B : Set Plane} (hA : MemLp u 2 (volume.restrict A)) (hB : MemLp u 2 (volume.restrict B)) :
    MemLp u 2 (volume.restrict (A ∪ B)) := by
  have hA' : IntegrableOn (fun x => ‖u x‖ ^ 2) A := hA.integrable_norm_pow (by norm_num)
  have hB' : IntegrableOn (fun x => ‖u x‖ ^ 2) B := hB.integrable_norm_pow (by norm_num)
  exact (memLp_two_iff_integrable_sq_norm
    (aestronglyMeasurable_union_iff.2 ⟨hA.aestronglyMeasurable, hB.aestronglyMeasurable⟩)).2 (hA'.union hB')

private theorem restrict_memW12 {n q : ℕ} {U V : OpenDomain n} {u : Domain n → Ambient q}
    {D : Domain n → HarmonicMaps.Gradient n q}
    (hU : MemW12 U u D) (hVU : V.val ⊆ U.val) : MemW12 V u D :=
  ⟨hU.1.mono hVU, hU.2.1.mono_measure (Measure.restrict_mono_set _ hVU),
    fun i => (hU.2.2 i).mono_measure (Measure.restrict_mono_set _ hVU)⟩

/-- Actual shifted core maps paste with the fixed exterior on genuine
overlaps, keeping their weak columns and their original outer circle. -/
theorem exists_planarPair_gluing {a : BulkCoefficients} {b₀ : C(NativeCircle, vacuum a)}
    {b : Fin 2 → C(NativeCircle, vacuum a)} (P : PlanarPairExterior a b₀ b)
    {ε : ℝ} (hε : 0 < ε) (hεcut : ε < 3 / 16)
    (u : Fin 2 → Plane → Ambient 5) (Du : Fin 2 → Plane → HarmonicMaps.Gradient 2 5)
    (hU : ∀ i, MemW12 (ballDomain (planarPairCoreCenter i) (1 / 4)) (u i) (Du i))
    (hRay : ∀ i, ∀ r ≥ ε, ∀ θ : NativeCircle,
      u i (planarPairCoreCenter i + r • θ.val) = frobeniusCoordinateEquiv (b i θ).val) :
    ∃ (w : Plane → Ambient 5) (Dw : Plane → HarmonicMaps.Gradient 2 5),
      MemW12 (ballDomain (0 : Plane) 1) w Dw ∧
      (∀ i, EqOn w (u i) (ball (planarPairCoreCenter i) (1 / 4))) ∧
      (∀ i, EqOn Dw (Du i) (ball (planarPairCoreCenter i) (1 / 4))) ∧
      EqOn w P.field ((ball (0 : Plane) 1) \ ⋃ i, ball (planarPairCoreCenter i) (1 / 4)) ∧
      EqOn Dw P.columns ((ball (0 : Plane) 1) \ ⋃ i, ball (planarPairCoreCenter i) (1 / 4)) ∧
      (∀ r ≥ (7 / 8 : ℝ), ∀ θ : NativeCircle, w (r • θ.val) = frobeniusCoordinateEquiv (b₀ θ).val) := by
  classical
  let Ω := ballDomain (0 : Plane) 1
  let E := planarPairExteriorDomain
  let U (i : Fin 2) := ballDomain (planarPairCoreCenter i) (1 / 4)
  let w (x : Plane) := if x ∈ (U 0).val then u 0 x else if x ∈ (U 1).val then u 1 x else P.field x
  let Dw (x : Plane) := if x ∈ (U 0).val then Du 0 x else if x ∈ (U 1).val then Du 1 x else P.columns x
  have hE (i : Fin 2) {x : Plane} (hx : x ∈ E.val) : (3 / 16 : ℝ) < dist x (planarPairCoreCenter i) :=
    mem_iInter.1 hx.2 i
  have hAgree (i : Fin 2) : EqOn (u i) P.field ((U i).val ∩ E.val) := by
    intro x hx
    exact (planarCore_eval_near_rim hε (hRay i) (hεcut.le.trans (hE i hx.2).le)).trans
      (P.inner_collar i x hx.2 hx.1).symm
  have hColAgree (i : Fin 2) : ∀ᵐ x ∂volume.restrict E.val, x ∈ (U i).val → Du i x = P.columns x := by
    let V : OpenDomain 2 := ⟨(U i).val ∩ E.val, (U i).property.inter E.property⟩
    have hV₁ := restrict_memW12 (V := V) (hU i) inter_subset_left
    have hV₂ := restrict_memW12 (V := V) P.sobolev inter_subset_right
    have hD : Du i =ᵐ[volume.restrict V.val] P.columns :=
      hV₁.1.ae_eq_of_ae_eq_map hV₂.1 ((ae_restrict_mem V.property.measurableSet).mono (fun _ hx => hAgree i hx))
    apply (ae_restrict_iff' (U i).property.measurableSet).1
    rwa [Measure.restrict_restrict (U i).property.measurableSet]
  have hwU (i : Fin 2) : EqOn w (u i) (U i).val := by
    intro x hx
    fin_cases i
    · exact if_pos hx
    · exact (if_neg (Set.disjoint_left.1 pairCore_balls_disjoint · hx)).trans (if_pos hx)
  have hDU (i : Fin 2) : EqOn Dw (Du i) (U i).val := by
    intro x hx
    fin_cases i
    · exact if_pos hx
    · exact (if_neg (Set.disjoint_left.1 pairCore_balls_disjoint · hx)).trans (if_pos hx)
  have hwE : w =ᵐ[volume.restrict E.val] P.field := by
    filter_upwards [ae_restrict_mem E.property.measurableSet] with x hx
    by_cases hi : x ∈ (U 0).val
    · exact (hwU 0 hi).trans (hAgree 0 ⟨hi, hx⟩)
    by_cases hj : x ∈ (U 1).val
    · exact (hwU 1 hj).trans (hAgree 1 ⟨hj, hx⟩)
    · exact (if_neg hi).trans (if_neg hj)
  have hDE : Dw =ᵐ[volume.restrict E.val] P.columns := by
    filter_upwards [hColAgree 0, hColAgree 1] with x h₀ h₁
    by_cases hi : x ∈ (U 0).val
    · exact (hDU 0 hi).trans (h₀ hi)
    by_cases hj : x ∈ (U 1).val
    · exact (hDU 1 hj).trans (h₁ hj)
    · exact (if_neg hi).trans (if_neg hj)
  have hGraphE : MemW12 E w Dw := P.sobolev.congr_ae hwE.symm hDE.symm
  have hGraphU (i : Fin 2) : MemW12 (U i) w Dw :=
    (hU i).congr_ae
      ((ae_restrict_mem (U i).property.measurableSet).mono fun _ hx => (hwU i hx).symm)
      ((ae_restrict_mem (U i).property.measurableSet).mono fun _ hx => (hDU i hx).symm)
  have hChoose (x : Plane) (hx : x ∈ Ω.val) :
      (x ∈ (U 0).val ∨ x ∈ (U 1).val) ∨ x ∈ E.val := by
    by_cases h₀ : x ∈ (U 0).val
    · exact Or.inl (Or.inl h₀)
    by_cases h₁ : x ∈ (U 1).val
    · exact Or.inl (Or.inr h₁)
    right
    refine ⟨hx, mem_iInter.2 fun i => ?_⟩
    have hi : x ∉ (U i).val := by fin_cases i <;> assumption
    exact (by norm_num : (3 / 16 : ℝ) < 1 / 4).trans_le (le_of_not_gt fun h => hi (mem_ball.2 h))
  have hSub : Ω.val ⊆ ((U 0).val ∪ (U 1).val) ∪ E.val := hChoose
  have hwLp : MemLp w 2 (volume.restrict Ω.val) :=
    (memLp_two_union (memLp_two_union (hGraphU 0).2.1 (hGraphU 1).2.1) hGraphE.2.1).mono_measure
      (Measure.restrict_mono_set _ hSub)
  have hDLp (i : Fin 2) : MemLp (fun x => Dw x i) 2 (volume.restrict Ω.val) :=
    (memLp_two_union (memLp_two_union ((hGraphU 0).2.2 i) ((hGraphU 1).2.2 i)) (hGraphE.2.2 i)).mono_measure
      (Measure.restrict_mono_set _ hSub)
  let O : Option (Fin 2) → OpenDomain 2 := fun i => i.elim E U
  have hO (i : Option (Fin 2)) : MemW12 (O i) w Dw := by cases i with
    | none => exact hGraphE
    | some j => exact hGraphU j
  have hCover (x : Plane) (hx : x ∈ Ω.val) : ∃ i : Option (Fin 2), x ∈ (O i).val := by
    rcases hChoose x hx with (h | h) | h
    · exact ⟨some 0, h⟩
    · exact ⟨some 1, h⟩
    · exact ⟨none, h⟩
  have hw : MemW12 Ω w Dw := memW12_of_open_cover_sobolev_pair hwLp hDLp O hCover hO
  have hOut (x : Plane) (hx : x ∉ ⋃ i, (U i).val) :
      w x = P.field x ∧ Dw x = P.columns x := by
    have hi (i : Fin 2) : x ∉ (U i).val := fun h => hx (mem_iUnion.2 ⟨i, h⟩)
    simp only [w, Dw, if_neg (hi 0), if_neg (hi 1), and_self]
  refine ⟨w, Dw, hw, hwU, hDU, fun x hx => (hOut x hx.2).1, fun x hx => (hOut x hx.2).2, ?_⟩
  intro r hr θ
  have hN : ‖r • θ.val‖ = r := by
    rw [norm_smul, Real.norm_of_nonneg ((by norm_num : (0 : ℝ) ≤ 7 / 8).trans hr),
      mem_sphere_zero_iff_norm.1 θ.property, mul_one]
  have ht : r • θ.val ∉ ⋃ i, (U i).val := by
    intro h
    obtain ⟨i, hi⟩ := mem_iUnion.1 h
    have hb : dist (r • θ.val) (planarPairCoreCenter i) < 1 / 4 := mem_ball.1 hi
    have hCr := dist_triangle (r • θ.val) (planarPairCoreCenter i) 0
    rw [dist_zero_right, dist_zero_right, hN, norm_planarPairCoreCenter] at hCr
    linarith only [hCr, hr, hb]
  exact (hOut _ ht).1.trans (P.outer_collar r hr θ)

/-- The two actual trivial or light cores have the sum of their own
logarithmic costs in the fixed reference exterior. -/
theorem exists_planarPairCores_of_fixed_exterior (a : BulkCoefficients)
    (hPolar : External.PeriodicAngularSobolev) (v : Sphere3) (g : Fin 2 → QuaternionGroup 2)
    (hg : ∀ i, g i = 1 ∨ IsLightQuaternion (g i)) (b₀ : C(NativeCircle, vacuum a)) :
    ∃ (b : Fin 2 → C(NativeCircle, vacuum a))
      (hBase : ∀ i, vacuumQuaternionProjection a v = b i nativeCircleLoopBase),
      (∀ i, nativeVacuumLoopWord a (b i) v (hBase i) = g i) ∧
      (∀ i, MemSphereW12 (le_refl 2) (fun θ => frobeniusCoordinateEquiv (b i θ).val)) ∧
      (PlanarPairExterior a b₀ b → ∃ C : ℝ, 0 ≤ C ∧ ∀ {ε : ℝ}, 0 < ε → ε < 3 / 16 →
        ∃ (w : Plane → Ambient 5) (Dw : Plane → HarmonicMaps.Gradient 2 5),
          MemW12 (ballDomain (0 : Plane) 1) w Dw ∧
          (∀ᵐ x ∂volume.restrict (ball (0 : Plane) 1), ‖w x‖ ≤ Real.sqrt 2 * vacuumRadius a) ∧
          (∀ r ≥ (7 / 8 : ℝ), ∀ θ : NativeCircle, w (r • θ.val) = frobeniusCoordinateEquiv (b₀ θ).val) ∧
          planarWeakEnergy a ε w Dw 1 ≤
            (vacuumSplittingCost a v (g 0) + vacuumSplittingCost a v (g 1)) * Real.log (1 / ε) + C) := by
  classical
  let cost (i : Fin 2) := vacuumSplittingCost a v (g i)
  have hNonneg (i : Fin 2) : 0 ≤ cost i := by
    dsimp only [cost]
    rw [vacuumSplittingCost_eq]
    exact mul_nonneg (kappaStar_pos a).le (Nat.cast_nonneg _)
  have hCore (i : Fin 2) := exists_lightOrTrivialVacuumCore_on_ball a hPolar v (hg i)
  choose b hBase hWord hb C hC hBuild using hCore
  refine ⟨b, hBase, hWord, hb, ?_⟩
  intro P
  let B := Real.sqrt 2 * vacuumRadius a
  let E := planarPairExteriorDomain
  let Ω := ball (0 : Plane) 1
  let U (i : Fin 2) := ball (planarPairCoreCenter i) (1 / 4)
  let A := Ω \ (⋃ i, U i)
  let L := (1 / 2 : ℝ) * ∫ x in E.val, hsNormSq (P.columns x)
  have hL : 0 ≤ L := mul_nonneg (by norm_num) (integral_nonneg fun _ => hsNormSq_nonneg _)
  refine ⟨C 0 + C 1 + L, add_nonneg (add_nonneg (hC 0) (hC 1)) hL, ?_⟩
  intro ε hε hεcut
  have hεR : ε < 1 / 4 := hεcut.trans (by norm_num)
  have hBuilt (i : Fin 2) := hBuild i (planarPairCoreCenter i) hε hεR
  choose u Du hU hUB hUR hCost using hBuilt
  obtain ⟨w, Dw, hw, hwU, hDU, hwA, hDA, hTrace⟩ := exists_planarPair_gluing P hε hεcut u Du hU hUR
  have hA : A ⊆ E.val := by
    intro x hx
    refine ⟨hx.1, mem_iInter.2 fun i => ?_⟩
    have hOut : x ∉ U i := fun h => hx.2 (mem_iUnion.2 ⟨i, h⟩)
    have hR : (1 / 4 : ℝ) ≤ dist x (planarPairCoreCenter i) :=
      le_of_not_gt fun h => hOut (mem_ball.2 h)
    exact (by norm_num : (3 / 16 : ℝ) < 1 / 4).trans_le hR
  have hwB : ∀ᵐ x ∂volume.restrict Ω, ‖w x‖ ≤ B := by
    have hP := (ae_restrict_iff' E.property.measurableSet).1 P.vacuum_ae
    have hU₀ := (ae_restrict_iff' measurableSet_ball).1 (hUB 0)
    have hU₁ := (ae_restrict_iff' measurableSet_ball).1 (hUB 1)
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_ball, ae_restrict_of_ae hP,
      ae_restrict_of_ae hU₀, ae_restrict_of_ae hU₁] with x hx hN h₀ h₁
    by_cases hi : x ∈ U 0
    · rw [hwU 0 hi]
      exact h₀ hi
    by_cases hj : x ∈ U 1
    · rw [hwU 1 hj]
      exact h₁ hj
    · have hxA : x ∈ A := ⟨hx, fun h => by
        obtain ⟨i, hi'⟩ := mem_iUnion.1 h
        fin_cases i
        · exact hi hi'
        · exact hj hi'⟩
      rw [hwA hxA, ← frobeniusCoordinateEquiv.symm.norm_map]
      exact (vacuum_norm (hN (hA hxA))).le
  refine ⟨w, Dw, hw, hwB, hTrace, ?_⟩
  let G (x : Plane) := hsNormSq (Dw x)
  let F (x : Plane) := planarCoordinateBulkPotential a (w x)
  have hG : IntegrableOn G Ω := hw.integrable_hsNormSq
  have hF : IntegrableOn F Ω := by
    letI : IsFiniteMeasure (volume.restrict Ω) := isFiniteMeasure_restrict.2 measure_ball_ne_top
    have h : AEStronglyMeasurable w (volume.restrict Ω) := hw.2.1.aestronglyMeasurable
    exact integrable_planarCoordinateBulkPotential_of_bound a h hwB
  have hExtE : (∫ x in A, G x) ≤ ∫ x in E.val, hsNormSq (P.columns x) := by
    have hEq : (∫ x in A, G x) = ∫ x in A, hsNormSq (P.columns x) :=
      setIntegral_congr_fun (measurableSet_ball.diff (MeasurableSet.iUnion fun _ => measurableSet_ball))
        fun x hx => congrArg hsNormSq (hDA hx)
    rw [hEq]
    apply setIntegral_mono_set P.sobolev.integrable_hsNormSq (ae_of_all _ fun _ => hsNormSq_nonneg _)
    exact Eventually.of_forall hA
  have hExtF : (∫ x in A, F x) = 0 := by
    have hVac := ae_restrict_of_ae_restrict_of_subset hA P.vacuum_ae
    have hAmeas : MeasurableSet A :=
      measurableSet_ball.diff (MeasurableSet.iUnion fun _ => measurableSet_ball)
    have hEq : F =ᵐ[volume.restrict A] (fun _ => (0 : ℝ)) := by
      filter_upwards [hVac, ae_restrict_mem (μ := volume) hAmeas] with x hx h
      change planarCoordinateBulkPotential a (w x) = 0
      rw [hwA h]
      exact (bulkPotential_eq_zero_iff a _).2 hx
    rw [integral_congr_ae hEq, integral_zero]
  have hJ : (⋃ i, U i) = U 0 ∪ U 1 := by
    apply Set.ext
    intro x
    rw [mem_iUnion, mem_union]
    constructor
    · rintro ⟨i, hi⟩
      fin_cases i
      · exact Or.inl hi
      · exact Or.inr hi
    · rintro (h | h)
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
  have hJsub : (⋃ i, U i) ⊆ Ω := iUnion_subset pairCore_ball_subset
  have hSplit (f : Plane → ℝ) (hf : IntegrableOn f Ω) :
      (∫ x in Ω, f x) = (∫ x in U 0, f x) + (∫ x in U 1, f x) + (∫ x in A, f x) := by
    have hJM : MeasurableSet (⋃ i, U i) := MeasurableSet.iUnion fun _ => measurableSet_ball
    have h := setIntegral_sdiff hJM hf hJsub
    change (∫ x in A, f x) = (∫ x in Ω, f x) - ∫ x in (⋃ i, U i), f x at h
    rw [hJ, setIntegral_union pairCore_balls_disjoint measurableSet_ball
      (hf.mono_set (pairCore_ball_subset 0)) (hf.mono_set (pairCore_ball_subset 1))] at h
    linarith only [h]
  have hCostW (i : Fin 2) : ((1 / 2 : ℝ) * (∫ x in U i, G x) + ε⁻¹ ^ 2 * (∫ x in U i, F x)) ≤
      cost i * Real.log ((1 / 4 : ℝ) / ε) + C i := by
    have hGi : (∫ x in U i, G x) = ∫ x in U i, hsNormSq (Du i x) :=
      setIntegral_congr_fun measurableSet_ball fun x hx => congrArg hsNormSq (hDU i hx)
    have hFi : (∫ x in U i, F x) = ∫ x in U i, planarCoordinateBulkPotential a (u i x) :=
      setIntegral_congr_fun measurableSet_ball fun x hx => congrArg (planarCoordinateBulkPotential a) (hwU i hx)
    rw [hGi, hFi]
    exact hCost i
  have hLog : Real.log ((1 / 4 : ℝ) / ε) ≤ Real.log (1 / ε) :=
    Real.log_le_log (div_pos (by norm_num) hε) (div_le_div_of_nonneg_right (by norm_num) hε.le)
  change ((1 / 2 : ℝ) * (∫ x in Ω, G x) + ε⁻¹ ^ 2 * (∫ x in Ω, F x)) ≤ _
  rw [hSplit G hG, hSplit F hF, hExtF, add_zero]
  calc
    _ = ((1 / 2 : ℝ) * (∫ x in U 0, G x) + ε⁻¹ ^ 2 * (∫ x in U 0, F x)) +
        ((1 / 2 : ℝ) * (∫ x in U 1, G x) + ε⁻¹ ^ 2 * (∫ x in U 1, F x)) +
        (1 / 2 : ℝ) * ∫ x in A, G x := by ring
    _ ≤ (cost 0 * Real.log ((1 / 4 : ℝ) / ε) + C 0) +
        (cost 1 * Real.log ((1 / 4 : ℝ) / ε) + C 1) + L :=
      add_le_add (add_le_add (hCostW 0) (hCostW 1)) (mul_le_mul_of_nonneg_left hExtE (by norm_num))
    _ ≤ (cost 0 * Real.log (1 / ε) + C 0) + (cost 1 * Real.log (1 / ε) + C 1) + L := by
      have h₀ := mul_le_mul_of_nonneg_left hLog (hNonneg 0)
      have h₁ := mul_le_mul_of_nonneg_left hLog (hNonneg 1)
      linarith only [h₀, h₁]
    _ = _ := by ring

end Thesis
