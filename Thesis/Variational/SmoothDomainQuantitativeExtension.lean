module

public import Thesis.Variational.SmoothDomainSobolevDensity
import Thesis.Foundation.WeakGradient
import Thesis.Upstream.Rellich
import HarmonicMaps.Analysis.SobolevL2Closure
import HarmonicMaps.SobolevRestriction
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Topology.Sequences

/-! Quantitative extension of the actual Sobolev graph to a containing ball. -/

public section

noncomputable section

open Filter Function HarmonicMaps MeasureTheory Metric Set Topology
open scoped ContDiff ENNReal NNReal Matrix.Norms.Frobenius

namespace Thesis

local instance quantitativeExtensionTensorComplete : CompleteSpace S0 := complete_of_proper

local instance quantitativeExtensionTensorENorm : ENormedAddMonoid S0 := NormedAddGroup.toENormedAddMonoid

private theorem gradient_ae_eq_of_columns {μ : Measure Point} {D G : Point → Thesis.Gradient}
    (h : ∀ j : Fin 3, (fun x => D x j) =ᵐ[μ] fun x => G x j) : D =ᵐ[μ] G :=
  (ae_all_iff.mpr h).mono fun _ h => funext h

private theorem memH1_zero (U : Set Point) : MemH1 U (0 : Point → S0) (0 : Point → Thesis.Gradient) := by
  have hV : MemLp (0 : Point → S0) 2 (volume.restrict U) := by
    with_unfolding_all exact MemLp.zero
  have hD (j : Fin 3) : MemLp (fun x : Point => (0 : Point → Thesis.Gradient) x j) 2
      (volume.restrict U) := hV
  refine ⟨hV,hD,?_⟩
  intro j φ hφ
  simp only [Pi.zero_apply, smul_zero, integral_zero, neg_zero]

private def weakH1GraphSubmodule (U : Set Point) : Submodule ℝ (H1Graph U) where
  carrier := {p | MemH1 U p.1 (fun x j => p.2 j x)}
  zero_mem' := by
    exact (memH1_zero U).congr_ae (Lp.coeFn_zero S0 2 _).symm
      (gradient_ae_eq_of_columns fun _ => (Lp.coeFn_zero S0 2 _).symm)
  add_mem' := by
    intro p q hp hq
    exact (MemH1.add hp hq).congr_ae (Lp.coeFn_add p.1 q.1).symm
      (gradient_ae_eq_of_columns fun j => (Lp.coeFn_add (p.2 j) (q.2 j)).symm)
  smul_mem' := by
    intro c p hp
    exact (MemH1.const_smul hp c).congr_ae (Lp.coeFn_smul c p.1).symm
      (gradient_ae_eq_of_columns fun j => (Lp.coeFn_smul c (p.2 j)).symm)

private theorem eLpNorm_frobenius_sub (u v : Point → S0) (μ : Measure Point) :
    eLpNorm (frobeniusField u - frobeniusField v) 2 μ = eLpNorm (u - v) 2 μ := by
  have h : frobeniusField u - frobeniusField v = frobeniusField (u - v) := by
    funext x
    exact (frobeniusCoordinateEquiv.map_sub _ _).symm
  rw [h,eLpNorm_frobeniusField]

private theorem weakH1GraphSubmodule_isClosed {U : Set Point} (hU : IsOpen U)
    (hB : Bornology.IsBounded U) : IsClosed (weakH1GraphSubmodule U : Set (H1Graph U)) := by
  apply isSeqClosed_iff_isClosed.mp
  intro p w hp hLim
  let Ω : OpenDomain 3 := ⟨U,hU⟩
  let μ : Measure Point := volume.restrict U
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.2 hB.measure_lt_top.ne
  let F (n : ℕ) (x : Point) := frobeniusCoordinateEquiv ((p n).1 x)
  let D (n : ℕ) (x : Point) (j : Fin 3) := frobeniusCoordinateEquiv ((p n).2 j x)
  let f (x : Point) := frobeniusCoordinateEquiv (w.1 x)
  let G (x : Point) (j : Fin 3) := frobeniusCoordinateEquiv (w.2 j x)
  have hSob (n : ℕ) : MemW12 Ω (F n) (D n) :=
    (memH1_iff_memW12 Ω _ _).mp (hp n)
  have hf : MemLp f 2 μ := (frobeniusCoordinateEquiv_memLp_iff μ 2 _).mpr (Lp.memLp w.1)
  have hG (j : Fin 3) : MemLp (fun x => G x j) 2 μ :=
    (frobeniusCoordinateEquiv_memLp_iff μ 2 _).mpr (Lp.memLp (w.2 j))
  have h₁ : Tendsto (fun n => eLpNorm (F n - f) 2 μ) atTop (𝓝 0) := by
    have hPf : Tendsto (fun n => (p n).1) atTop (𝓝 w.1) := continuous_fst.continuousAt.tendsto.comp hLim
    have h := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' (fun n => (p n).1) w.1).1 hPf
    refine h.congr fun n => ?_
    exact (eLpNorm_frobenius_sub ((p n).1 : Point → S0) w.1 μ).symm
  have h₂ (j : Fin 3) : Tendsto (fun n => eLpNorm (fun x => D n x j - G x j) 2 μ) atTop (𝓝 0) := by
    have hPt : Tendsto (fun n => (p n).2) atTop (𝓝 w.2) := continuous_snd.continuousAt.tendsto.comp hLim
    have hPi := tendsto_pi_nhds.mp hPt j
    have h := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' (fun n => (p n).2 j) (w.2 j)).1 hPi
    refine h.congr fun n => ?_
    exact (eLpNorm_frobenius_sub ((p n).2 j : Point → S0) (w.2 j) μ).symm
  exact (memH1_iff_memW12 Ω _ _).mpr (MemW12.of_L2_limit hSob hf hG h₁ h₂)

private def lpRestrictLinearMap {μ ν : Measure Point} (hν : ν ≤ μ) :
    Lp S0 2 μ →ₗ[ℝ] Lp S0 2 ν where
  toFun a := ((Lp.memLp a).mono_measure hν).toLp a
  map_add' a b := by
    apply Lp.ext
    have ha := ((Lp.memLp a).mono_measure hν).coeFn_toLp
    have hb := ((Lp.memLp b).mono_measure hν).coeFn_toLp
    have hab := ((Lp.memLp (a+b)).mono_measure hν).coeFn_toLp
    filter_upwards [hab,ha,hb,(Lp.coeFn_add a b).filter_mono (ae_mono hν),
      Lp.coeFn_add (((Lp.memLp a).mono_measure hν).toLp a) (((Lp.memLp b).mono_measure hν).toLp b)]
      with x h₁ h₂ h₃ h₄ h₅
    exact (h₁.trans h₄).trans ((congrArg₂ (· + ·) h₂ h₃).symm.trans h₅.symm)
  map_smul' c a := by
    apply Lp.ext
    have ha := ((Lp.memLp a).mono_measure hν).coeFn_toLp
    have hca := ((Lp.memLp (c • a)).mono_measure hν).coeFn_toLp
    filter_upwards [hca,ha,(Lp.coeFn_smul c a).filter_mono (ae_mono hν),
      Lp.coeFn_smul c (((Lp.memLp a).mono_measure hν).toLp a)] with x h₁ h₂ h₃ h₄
    exact (h₁.trans h₃).trans ((congrArg (c • ·) h₂).symm.trans h₄.symm)

private theorem lpRestrictLinearMap_apply_ae {μ ν : Measure Point} (hν : ν ≤ μ)
    (a : Lp S0 2 μ) : (lpRestrictLinearMap hν a : Point → S0) =ᵐ[ν] a :=
  ((Lp.memLp a).mono_measure hν).coeFn_toLp

private theorem norm_lpRestrictLinearMap_le {μ ν : Measure Point} (hν : ν ≤ μ)
    (a : Lp S0 2 μ) : ‖lpRestrictLinearMap hν a‖ ≤ ‖a‖ := by
  change ‖((Lp.memLp a).mono_measure hν).toLp a‖ ≤ _
  rw [Lp.norm_toLp, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.memLp a).eLpNorm_ne_top (eLpNorm_mono_measure _ hν)

private def graphRestrictLinearMap {U W : Set Point} (hSub : U ⊆ W) :
    weakH1GraphSubmodule W →ₗ[ℝ] weakH1GraphSubmodule U where
  toFun p := by
    let hμ := Measure.restrict_mono_set (volume : Measure Point) hSub
    let V := lpRestrictLinearMap hμ
    let q : H1Graph U := (V p.val.1, fun j => V (p.val.2 j))
    have hSob : MemH1 U (p.val.1 : Point → S0) (fun x j => p.val.2 j x) :=
      (show MemH1 W (p.val.1 : Point → S0) (fun x j => p.val.2 j x) from p.property).mono hSub
    exact ⟨q,hSob.congr_ae (lpRestrictLinearMap_apply_ae hμ p.val.1).symm
      (gradient_ae_eq_of_columns fun j => (lpRestrictLinearMap_apply_ae hμ (p.val.2 j)).symm)⟩
  map_add' p q := by
    apply Subtype.ext
    apply Prod.ext
    · exact (lpRestrictLinearMap (Measure.restrict_mono_set volume hSub)).map_add _ _
    · funext j
      exact (lpRestrictLinearMap (Measure.restrict_mono_set volume hSub)).map_add _ _
  map_smul' c p := by
    apply Subtype.ext
    apply Prod.ext
    · exact (lpRestrictLinearMap (Measure.restrict_mono_set volume hSub)).map_smul _ _
    · funext j
      exact (lpRestrictLinearMap (Measure.restrict_mono_set volume hSub)).map_smul _ _

private theorem norm_graphRestrictLinearMap_le {U W : Set Point}
    (hSub : U ⊆ W) (p : weakH1GraphSubmodule W) :
    ‖graphRestrictLinearMap hSub p‖ ≤ ‖p‖ := by
  let hμ := Measure.restrict_mono_set (volume : Measure Point) hSub
  change ‖((lpRestrictLinearMap hμ p.val.1,
    fun j => lpRestrictLinearMap hμ (p.val.2 j)) : H1Graph U)‖ ≤ ‖p.val‖
  rw [Prod.norm_def,Prod.norm_def]
  refine max_le ?_ ?_
  · exact (norm_lpRestrictLinearMap_le hμ _).trans (le_max_left _ _)
  · apply (pi_norm_le_iff_of_nonneg (le_trans (norm_nonneg p.val.1) (le_max_left _ _))).2
    intro j
    exact (norm_lpRestrictLinearMap_le hμ _).trans ((norm_le_pi_norm p.val.2 j).trans (le_max_right _ _))

private theorem graphRestrictLinearMap_surjective {U W : Set Point} (hU : IsSmoothDomain U)
    (hSub : U ⊆ W) (hW : IsOpen W) :
    Surjective (graphRestrictLinearMap hSub) := by
  intro p
  let Ω : OpenDomain 3 := ⟨U,hU.1.1⟩
  let V : OpenDomain 3 := ⟨W,hW⟩
  have hp : MemW12 Ω (frobeniusField (p.val.1 : Point → S0))
      (frobeniusGradient (fun x j => p.val.2 j x)) :=
    (memH1_iff_memW12 Ω _ _).mp p.property
  obtain ⟨f,D,hF,hFagree,hDagree⟩ := hU.exists_global_memW12_extension hp
  let w (x : Point) := frobeniusCoordinateEquiv.symm (f x)
  let G (x : Point) (j : Fin 3) := frobeniusCoordinateEquiv.symm (D x j)
  have hFrob : frobeniusField w = f := funext fun x => frobeniusCoordinateEquiv.apply_symm_apply _
  have hFrobD : frobeniusGradient G = D := funext fun x => funext fun j =>
    frobeniusCoordinateEquiv.apply_symm_apply _
  have hVμ := Measure.restrict_mono_set (volume : Measure Point) (subset_univ W)
  have hNative : MemW12 V f D :=
    ⟨hF.1.mono (subset_univ W),hF.2.1.mono_measure hVμ,fun j => (hF.2.2 j).mono_measure hVμ⟩
  have hw : MemH1 W w G := (memH1_iff_memW12 V _ _).mpr (by simpa only [hFrob,hFrobD] using hNative)
  let q : H1Graph W := (hw.1.toLp w, fun j => (hw.2.1 j).toLp (fun x => G x j))
  have hqa : (q.1 : Point → S0) =ᵐ[volume.restrict W] w := hw.1.coeFn_toLp
  have hqb (j : Fin 3) : (q.2 j : Point → S0) =ᵐ[volume.restrict W] fun x => G x j :=
    (hw.2.1 j).coeFn_toLp
  refine ⟨⟨q,hw.congr_ae hqa.symm (gradient_ae_eq_of_columns fun j => (hqb j).symm)⟩,?_⟩
  have hμ := Measure.restrict_mono_set (volume : Measure Point) hSub
  apply Subtype.ext
  apply Prod.ext
  · apply Lp.ext
    have hL := lpRestrictLinearMap_apply_ae hμ q.1
    have hwP : w =ᵐ[volume.restrict U] p.val.1 := by
      filter_upwards [ae_restrict_mem hU.1.1.measurableSet] with x hx
      change frobeniusCoordinateEquiv.symm (f x) = _
      rw [hFagree hx]
      exact frobeniusCoordinateEquiv.symm_apply_apply _
    exact hL.trans ((hqa.filter_mono (ae_mono hμ)).trans hwP)
  · funext j
    apply Lp.ext
    have hL := lpRestrictLinearMap_apply_ae hμ (q.2 j)
    have hGP : (fun x => G x j) =ᵐ[volume.restrict U] p.val.2 j := by
      filter_upwards [hDagree] with x hx
      have h := congrFun hx j
      change frobeniusCoordinateEquiv.symm (D x j) = _
      rw [h]
      exact frobeniusCoordinateEquiv.symm_apply_apply _
    exact hL.trans (((hqb j).filter_mono (ae_mono hμ)).trans hGP)

/-- The actual weak graph on a smooth bounded domain extends to any
containing bounded open domain with a uniform graph-norm estimate. -/
theorem IsSmoothDomain.exists_memH1_extension_bound {U W : Set Point} (hU : IsSmoothDomain U)
    (hSub : U ⊆ W) (hW : IsOpen W) (hB : Bornology.IsBounded W) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : Point → S0) (D : Point → Thesis.Gradient)
      (hu : MemH1 U u D), ∃ (w : Point → S0) (G : Point → Thesis.Gradient) (hw : MemH1 W w G),
      w =ᵐ[volume.restrict U] u ∧ G =ᵐ[volume.restrict U] D ∧
      ‖(hw.1.toLp w, fun j => (hw.2.1 j).toLp (fun x => G x j))‖ ≤
        C * ‖(hu.1.toLp u, fun j => (hu.2.1 j).toLp (fun x => D x j))‖ := by
  let R := graphRestrictLinearMap hSub
  let T := R.mkContinuous 1 (fun p => by rw [one_mul]; exact norm_graphRestrictLinearMap_le _ p)
  letI : CompleteSpace (weakH1GraphSubmodule W) :=
    (weakH1GraphSubmodule_isClosed hW hB).completeSpace_coe
  letI : CompleteSpace (weakH1GraphSubmodule U) :=
    (weakH1GraphSubmodule_isClosed hU.1.1 hU.1.2.2).completeSpace_coe
  have hS : Surjective T := graphRestrictLinearMap_surjective hU hSub hW
  obtain ⟨C,hC,hT⟩ := T.exists_preimage_norm_le hS
  refine ⟨C,hC,?_⟩
  intro u D hu
  let p : H1Graph U := (hu.1.toLp u, fun j => (hu.2.1 j).toLp (fun x => D x j))
  have hpa : (p.1 : Point → S0) =ᵐ[volume.restrict U] u := hu.1.coeFn_toLp
  have hpb (j : Fin 3) : (p.2 j : Point → S0) =ᵐ[volume.restrict U] fun x => D x j :=
    (hu.2.1 j).coeFn_toLp
  let a : weakH1GraphSubmodule U :=
    ⟨p,hu.congr_ae hpa.symm (gradient_ae_eq_of_columns fun j => (hpb j).symm)⟩
  obtain ⟨b,hb,hNorm⟩ := hT a
  let w (x : Point) := b.val.1 x
  let G (x : Point) (j : Fin 3) := b.val.2 j x
  have hw : MemH1 W w G := b.property
  have hμ := Measure.restrict_mono_set (volume : Measure Point) hSub
  have hbEq : R b = a := hb
  have hVal : lpRestrictLinearMap hμ b.val.1 = p.1 := congrArg (fun z : weakH1GraphSubmodule U => z.val.1) hbEq
  have hCol (j : Fin 3) : lpRestrictLinearMap hμ (b.val.2 j) = p.2 j :=
    congrArg (fun z : weakH1GraphSubmodule U => z.val.2 j) hbEq
  refine ⟨w,G,hw,?_,?_,?_⟩
  · have h := (lpRestrictLinearMap_apply_ae hμ b.val.1).symm
    rw [hVal] at h
    exact h.trans hpa
  · have h (j : Fin 3) : (fun x => G x j) =ᵐ[volume.restrict U] fun x => D x j := by
      have he := (lpRestrictLinearMap_apply_ae hμ (b.val.2 j)).symm
      rw [hCol] at he
      exact he.trans (hpb j)
    filter_upwards [ae_all_iff.mpr h] with x hx
    exact funext hx
  · have hPair :
      ((hw.1.toLp w, fun j => (hw.2.1 j).toLp (fun x => G x j)) : H1Graph W) = b.val := by
      apply Prod.ext
      · exact Lp.ext hw.1.coeFn_toLp
      · funext j
        exact Lp.ext (hw.2.1 j).coeFn_toLp
    rw [hPair]
    exact hNorm

end Thesis
