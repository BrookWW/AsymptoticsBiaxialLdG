module

public import Thesis.Interpolation.QuaternionSphereSobolevLift
import StratificationTheory.Frozen.SphereRadialBallExtension
import StratificationTheory.Compactness.RellichBall
import StratificationTheory.Compactness.GradientWeakSubsequence
import StratificationTheory.Compactness.WeakEnergyLowerSemicontinuity
import StratificationTheory.Compactness.WeakGradientClosure
import StratificationTheory.Foundation.RadialL2Transfer
import StratificationTheory.Foundation.HigherDimensionalRadialL2
import StratificationTheory.Foundation.AngularL2Membership
import HarmonicMaps.Analysis.AffineSobolevTransform
import HarmonicMaps.Analysis.SobolevAECongruence

/-! Sobolev compactness of native quaternion sphere data via radial extensions. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set StratificationTheory StratificationTheory.Compactness
open scoped ENNReal NNReal RealInnerProductSpace Topology

namespace Thesis

private theorem exists_strong_weak_subsequence_radial_balls
    (u : ℕ → Domain 3 → Ambient 4) (D : ℕ → Domain 3 → HarmonicMaps.Gradient 3 4)
    (hu : ∀ k, MemW12 (ballDomain 0 2) (u k) (D k)) (A C : ℝ≥0)
    (hMap : ∀ k, (∫ x in ball (0 : Domain 3) 2, ‖u k x‖ ^ 2) ≤ A)
    (hEnergy : ∀ k, HarmonicMaps.dirichletEnergy (D k) (ball (0 : Domain 3) 2) ≤ C) :
    ∃ (κ : ℕ → ℕ) (w : Domain 3 → Ambient 4) (Dw : Domain 3 → HarmonicMaps.Gradient 3 4),
      StrictMono κ ∧ MemW12 (ballDomain 0 1) w Dw ∧
      Tendsto (fun k => eLpNorm (u (κ k) - w) 2 (volume.restrict (ball (0 : Domain 3) 1)))
        atTop (𝓝 0) ∧
      (∀ (i : Fin 3) (z : Lp (Ambient 4) 2 (volume.restrict (ball (0 : Domain 3) 1))),
        Tendsto (fun k => ∫ x in ball (0 : Domain 3) 1, ⟪D (κ k) x i, z x⟫)
          atTop (𝓝 (∫ x in ball (0 : Domain 3) 1, ⟪Dw x i, z x⟫))) := by
  obtain ⟨κ, w, hκ, hw, hStrong⟩ := memW12_exists_strong_L2_subsequence_ball
    (0 : Domain 3) (by norm_num : (0 : ℝ) < 2) (by norm_num : (1 : ℝ) < 2)
    u D hu A C hMap hEnergy
  have hInner (k : ℕ) : MemW12 (ballDomain (0 : Domain 3) 1) (u (κ k)) (D (κ k)) :=
    (hu (κ k)).to_memW12Loc.memW12_ball (closedBall_subset_ball (by norm_num))
  have hE (k : ℕ) : HarmonicMaps.dirichletEnergy (D (κ k)) (ball (0 : Domain 3) 1) ≤ C :=
    (lintegral_mono_set (ball_subset_ball (by norm_num))).trans (hEnergy (κ k))
  obtain ⟨j, Dw, hj, hDw, _, hWeak⟩ := exists_weakly_convergent_gradient_field_ball
    (0 : Domain 3) 1 (D ∘ κ) (fun k i => (hInner k).2.2 i) C hE
  letI : IsFiniteMeasure (volume.restrict (ballDomain (0 : Domain 3) 1).val) :=
    isFiniteMeasure_restrict.mpr measure_ball_ne_top
  have hStrong' := hStrong.comp hj.tendsto_atTop
  have hw' := memW12_of_strong_map_weak_gradient_limit (fun k => hInner (j k)) hw hDw hStrong' hWeak
  exact ⟨κ ∘ j, w, Dw, hκ.comp hj, hw', hStrong', hWeak⟩

private theorem radialLp_ball_one_eq {p : UnitBoundarySphere 3 → Ambient 4} {w : Domain 3 → Ambient 4}
    (hp : MemLp p 2 (unitBoundarySurface 3))
    (hRay : ∀ (ρ : PositiveRadius) (θ : UnitBoundarySphere 3), w (ρ.val • θ.val) = p θ) :
    MemLp w 2 (volume.restrict (ball (0 : Domain 3) 1)) ∧
    eLpNorm w 2 (volume.restrict (ball (0 : Domain 3) 1)) =
      (ENNReal.ofReal (1 / 3 : ℝ)) ^ (1 / 2 : ℝ) * eLpNorm p 2 (unitBoundarySurface 3) := by
  have hσ : unitBoundarySurface 3 = (volume : Measure (Domain 3)).toSphere :=
    euclideanHausdorffMeasure_unitSphere_eq_toSphere (by decide : 0 < 3)
  rw [hσ] at hp ⊢
  simpa only [one_pow, Nat.cast_ofNat] using
    memLp_two_radial_ball_and_norm (by decide : 0 < 3) hp hRay zero_lt_one

private theorem exists_angular_limit_of_strong_radial_limit
    (u : ℕ → Domain 3 → Ambient 4) (v : ℕ → UnitBoundarySphere 3 → Ambient 4)
    (hv : ∀ k, MemLp (v k) 2 (unitBoundarySurface 3))
    (hRay : ∀ (k : ℕ) (ρ : PositiveRadius) (θ : UnitBoundarySphere 3), u k (ρ.val • θ.val) = v k θ)
    {w : Domain 3 → Ambient 4} (hw : MemLp w 2 (volume.restrict (ball (0 : Domain 3) 1)))
    (hStrong : Tendsto (fun k => eLpNorm (u k - w) 2 (volume.restrict (ball (0 : Domain 3) 1)))
      atTop (𝓝 0)) :
    ∃ v₀ : UnitBoundarySphere 3 → Ambient 4, MemLp v₀ 2 (unitBoundarySurface 3) ∧
      Tendsto (fun k => eLpNorm (v k - v₀) 2 (unitBoundarySurface 3)) atTop (𝓝 0) ∧
      ∀ base : UnitBoundarySphere 3,
        w =ᵐ[volume.restrict (ball (0 : Domain 3) 1)] v₀ ∘ sphereRadialDirection base := by
  let μ := volume.restrict (ball (0 : Domain 3) 1)
  let σ := unitBoundarySurface 3
  let c : ℝ≥0∞ := (ENNReal.ofReal (1 / 3 : ℝ)) ^ (1 / 2 : ℝ)
  have hcpos : 0 < c := ENNReal.rpow_pos (by norm_num) ENNReal.ofReal_ne_top
  have hcFin : c ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
  have hcReal : 0 < c.toReal := ENNReal.toReal_pos hcpos.ne' hcFin
  have hu (k : ℕ) : MemLp (u k) 2 μ := (radialLp_ball_one_eq (hv k) (hRay k)).1
  let U (k : ℕ) := (hu k).toLp (u k)
  let V (k : ℕ) := (hv k).toLp (v k)
  have hU : Tendsto U atTop (𝓝 (hw.toLp w)) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' u hu w hw).2 hStrong
  have hDist (k j : ℕ) : dist (U k) (U j) = c.toReal * dist (V k) (V j) := by
    have hEq := (radialLp_ball_one_eq ((hv k).sub (hv j)) (w := u k - u j)
      (fun ρ θ => by simp only [Pi.sub_apply, hRay k ρ θ, hRay j ρ θ])).2
    rw [dist_edist, dist_edist]
    dsimp only [U, V]
    rw [Lp.edist_toLp_toLp, Lp.edist_toLp_toLp, hEq, ENNReal.toReal_mul]
  have hC : CauchySeq V := by
    have hCU := Metric.cauchySeq_iff.1 hU.cauchySeq
    apply Metric.cauchySeq_iff.2
    intro ε hε
    obtain ⟨N, hN⟩ := hCU (c.toReal * ε) (mul_pos hcReal hε)
    refine ⟨N, fun k hk j hj => ?_⟩
    have h := hN k hk j hj
    rw [hDist] at h
    exact (mul_lt_mul_iff_of_pos_left hcReal).1 h
  obtain ⟨Z, hZ⟩ := cauchySeq_tendsto_of_complete hC
  let v₀ : UnitBoundarySphere 3 → Ambient 4 := Z
  have hv₀ : MemLp v₀ 2 σ := Lp.memLp Z
  have hV : Tendsto (fun k => eLpNorm (v k - v₀) 2 σ) atTop (𝓝 0) := by
    apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' v hv v₀ hv₀).1
    rw [show hv₀.toLp v₀ = Z from Lp.toLp_coeFn _ _]
    exact hZ
  refine ⟨v₀, hv₀, hV, ?_⟩
  intro base
  let w₀ := v₀ ∘ sphereRadialDirection base
  have hRaw (ρ : PositiveRadius) (θ : UnitBoundarySphere 3) : w₀ (ρ.val • θ.val) = v₀ θ := by
    simp only [w₀, Function.comp_apply, sphereRadialDirection_smul base ρ.property, sphereRadialDirection_unit]
  have hw₀ : MemLp w₀ 2 μ := (radialLp_ball_one_eq hv₀ hRaw).1
  have hE (k : ℕ) : eLpNorm (u k - w₀) 2 μ = c * eLpNorm (v k - v₀) 2 σ :=
    (radialLp_ball_one_eq ((hv k).sub hv₀) (w := u k - w₀)
      (fun ρ θ => by simp only [Pi.sub_apply, hRay k ρ θ, hRaw ρ θ])).2
  have hU₀ : Tendsto (fun k => eLpNorm (u k - w₀) 2 μ) atTop (𝓝 0) := by
    simp_rw [hE]
    simpa only [mul_zero, Function.comp_def] using (ENNReal.continuous_const_mul hcFin).continuousAt.tendsto.comp hV
  exact tendstoInMeasure_ae_unique
    (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (fun k => (hu k).aestronglyMeasurable) hw.aestronglyMeasurable hStrong)
    (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (fun k => (hu k).aestronglyMeasurable) hw₀.aestronglyMeasurable hU₀)

private theorem radial_dirichletEnergy_ball_one {v : UnitBoundarySphere 3 → Ambient 4}
    (hv : MemSphereW12 (by decide : 2 ≤ 3) v)
    {w : Domain 3 → Ambient 4} {D : Domain 3 → HarmonicMaps.Gradient 3 4}
    (hw : MemW12 (ballDomain 0 1) w D)
    (hRay : ∀ (ρ : PositiveRadius) (θ : UnitBoundarySphere 3), w (ρ.val • θ.val) = v θ) :
    HarmonicMaps.dirichletEnergy D (ball (0 : Domain 3) 1) =
      ENNReal.ofReal (quaternionBoundaryEnergy (by decide : 2 ≤ 3) v hv) := by
  obtain ⟨w₀, D₀, hw₀, hRaw, _, hD₀, hE, _⟩ :=
    exists_radial_ball_sobolev_extension (by decide : 3 ≤ 3) v hv zero_lt_one
  have hSame : w =ᵐ[volume.restrict (ball (0 : Domain 3) 1)] w₀ :=
    ae_eq_radial_ball_of_ae_rays (by decide : 0 < 3) zero_lt_one
      hw.2.1.aestronglyMeasurable hw₀.2.1.aestronglyMeasurable
      (fun ρ => ae_of_all _ fun θ => (hRay ρ θ).trans (hRaw ρ θ).symm)
  have hD := hw.1.ae_eq_of_ae_eq_map hw₀.1 hSame
  have hd : HarmonicMaps.dirichletEnergy D (ball (0 : Domain 3) 1) =
      HarmonicMaps.dirichletEnergy D₀ (ball (0 : Domain 3) 1) :=
    lintegral_congr_ae (hD.mono fun x hx => congrArg (fun A => ENNReal.ofReal (hsNormSq A)) hx)
  rw [hd, HarmonicMaps.dirichletEnergy_eq_ofReal_integral hD₀, hE]
  norm_num [quaternionBoundaryEnergy, hsNormSq, unitBoundarySurface]

/-- Bounded quaternion lifts on the two-sphere are compact in strong `L²`,
with lower semicontinuity for the original native tangential energy. -/
theorem exists_quaternionSphere_Sobolev_subsequence (base : UnitBoundarySphere 3)
    (v : ℕ → UnitBoundarySphere 3 → Ambient 4)
    (hv : ∀ k, MemSphereW12 (by decide : 2 ≤ 3) (v k))
    (hUnit : ∀ k, ∀ᵐ θ ∂unitBoundarySurface 3, ‖v k θ‖ = 1)
    (C : ℝ≥0) (hEnergy : ∀ k, quaternionBoundaryEnergy (by decide : 2 ≤ 3) (v k) (hv k) ≤ C) :
    ∃ (κ : ℕ → ℕ) (v₀ : UnitBoundarySphere 3 → Ambient 4)
      (hv₀ : MemSphereW12 (by decide : 2 ≤ 3) v₀),
      StrictMono κ ∧ (∀ᵐ θ ∂unitBoundarySurface 3, ‖v₀ θ‖ = 1) ∧
      Tendsto (fun k => eLpNorm (v (κ k) - v₀) 2 (unitBoundarySurface 3)) atTop (𝓝 0) ∧
      ENNReal.ofReal (quaternionBoundaryEnergy (by decide : 2 ≤ 3) v₀ hv₀) ≤
        atTop.liminf (fun k => ENNReal.ofReal (quaternionBoundaryEnergy (by decide : 2 ≤ 3) (v (κ k)) (hv (κ k)))) := by
  have hR (k : ℕ) := exists_radial_ball_sobolev_extension (by decide : 3 ≤ 3) (v k) (hv k)
    (by norm_num : 0 < (2 : ℝ))
  choose u D hU hRay _ hDI hE hProp using hR
  let A : ℝ≥0 := ⟨(volume : Measure (Domain 3)).real (ball 0 2), ENNReal.toReal_nonneg⟩
  have hMap (k : ℕ) : (∫ x in ball (0 : Domain 3) 2, ‖u k x‖ ^ 2) ≤ A := by
    have ha := hProp k (fun x => ‖x‖ = 1) (hUnit k)
    calc
      _ = ∫ _ : Domain 3 in ball 0 2, (1 : ℝ) := integral_congr_ae (ha.mono fun x hx => by rw [hx, one_pow])
      _ ≤ A := by
        simp only [setIntegral_const, smul_eq_mul, mul_one]
        exact le_rfl
  have hEE (k : ℕ) : HarmonicMaps.dirichletEnergy (D k) (ball (0 : Domain 3) 2) ≤ ((2 : ℝ≥0) * C : ℝ≥0) := by
    have he : (∫ x in ball (0 : Domain 3) 2, hsNormSq (D k x)) =
        2 * quaternionBoundaryEnergy (by decide : 2 ≤ 3) (v k) (hv k) := by
      rw [hE k]
      norm_num [quaternionBoundaryEnergy, hsNormSq, unitBoundarySurface]
    rw [HarmonicMaps.dirichletEnergy_eq_ofReal_integral (hDI k), he, ← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hEnergy k) (by norm_num : 0 ≤ (2 : ℝ)))
  obtain ⟨κ, w, Dw, hκ, hW, hwconv, hWeak⟩ :=
    exists_strong_weak_subsequence_radial_balls u D hU A (2 * C) hMap hEE
  obtain ⟨v₀, hv₀, hvConv, hwRaw⟩ := exists_angular_limit_of_strong_radial_limit (u ∘ κ) (v ∘ κ)
    (fun k => (hv (κ k)).1) (fun k => hRay (κ k)) hW.2.1 hwconv
  have hUnit₀ : ∀ᵐ θ ∂unitBoundarySurface 3, ‖v₀ θ‖ = 1 := by
    have hMeasure := tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (fun k => (hv (κ k)).1.aestronglyMeasurable) hv₀.aestronglyMeasurable hvConv
    obtain ⟨j, _, hj⟩ := hMeasure.exists_seq_tendsto_ae
    have hAll := ae_all_iff.2 (fun k => hUnit (κ (j k)))
    filter_upwards [hj, hAll] with θ hθ hAllθ
    have ht : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 ‖v₀ θ‖) := by
      simpa only [Function.comp_apply, hAllθ] using hθ.norm
    exact tendsto_nhds_unique ht tendsto_const_nhds
  let z := v₀ ∘ sphereRadialDirection base
  have hz : MemW12 (ballDomain (0 : Domain 3) 1) z Dw :=
    hW.congr_ae (hwRaw base) (EventuallyEq.refl _ _)
  have hZray (ρ : PositiveRadius) (θ : UnitBoundarySphere 3) : z (ρ.val • θ.val) = v₀ θ := by
    simp only [z, Function.comp_apply, sphereRadialDirection_smul base ρ.property, sphereRadialDirection_unit]
  have hScale := hz.affinePullback_ball (by norm_num : 0 < (1 / 2 : ℝ))
  have hZ₂ : (fun x => z (ballAffine 0 (1 / 2) x)) = z := by
    funext x
    simp only [ballAffine, sub_zero, zero_add, z, Function.comp_apply,
      sphereRadialDirection_smul base (by norm_num : 0 < (1 / 2 : ℝ))]
  rw [show (1 : ℝ) / (1 / 2) = 2 by norm_num, hZ₂] at hScale
  let Ω : OpenDomain 3 := ⟨ball 0 2 \ {0}, isOpen_ball.sdiff (isClosed_singleton (x := 0))⟩
  have hSub : Ω.val ⊆ ball (0 : Domain 3) 2 := sdiff_subset
  have hZ' : MemW12 Ω z (fun x i => (1 / 2 : ℝ) • Dw (ballAffine 0 (1 / 2) x) i) := by
    refine ⟨(hScale.to_memW12Loc.mono hSub).1,
      hScale.2.1.mono_measure (Measure.restrict_mono_set _ hSub),
      fun i => (hScale.2.2 i).mono_measure (Measure.restrict_mono_set _ hSub)⟩
  have hSphere : sphere (0 : Domain 3) 1 ⊆ Ω.val := by
    intro θ hθ
    have hNorm : ‖θ‖ = 1 := mem_sphere_zero_iff_norm.1 hθ
    refine ⟨by rw [mem_ball, dist_zero_right, hNorm]; norm_num, ?_⟩
    intro hZero
    rw [show θ = 0 from hZero, norm_zero] at hNorm
    exact zero_ne_one hNorm
  have hvF : MemSphereW12 (by decide : 2 ≤ 3) v₀ :=
    ⟨hv₀, Ω, hSphere, fun h => h.2 rfl, z, _, hZ', fun ρ θ _ => hZray ρ θ⟩
  refine ⟨κ, v₀, hvF, hκ, hUnit₀, hvConv, ?_⟩
  have hUk (k : ℕ) : MemW12 (ballDomain (0 : Domain 3) 1) (u (κ k)) (D (κ k)) :=
    (hU (κ k)).to_memW12Loc.memW12_ball (closedBall_subset_ball (by norm_num))
  have hWeakE := dirichletEnergy_le_liminf_of_weak_columns
    (fun k i => (hUk k).2.2 i) hW.2.2 hWeak
  change HarmonicMaps.dirichletEnergy Dw (ball (0 : Domain 3) 1) ≤ atTop.liminf
    (fun k => HarmonicMaps.dirichletEnergy (D (κ k)) (ball (0 : Domain 3) 1)) at hWeakE
  have heq : (fun k => HarmonicMaps.dirichletEnergy (D (κ k)) (ball (0 : Domain 3) 1)) =
      fun k => ENNReal.ofReal (quaternionBoundaryEnergy (by decide : 2 ≤ 3) (v (κ k)) (hv (κ k))) :=
    funext fun k => radial_dirichletEnergy_ball_one (hv (κ k)) (hUk k) (hRay (κ k))
  rwa [radial_dirichletEnergy_ball_one hvF hz hZray, heq] at hWeakE

end Thesis
