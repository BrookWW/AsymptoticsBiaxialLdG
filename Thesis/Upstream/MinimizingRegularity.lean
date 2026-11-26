module

public import Thesis.Upstream.MinimizingSobolev
public import StratificationTheory.Stratification.SingularIsolation
public import HolderToCK.Frozen.SmallEnergySmoothRegularity

/-! Interior regular points of the tensor minimizer in its Frobenius coordinates. -/

public section

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ContDiff ENNReal NNReal Matrix.Norms.Frobenius

namespace Thesis

/-- The two regular-point definitions differ only by the choice of coordinates
and the use of a ball rather than an arbitrary open neighborhood. -/
theorem upstreamIsRegularPoint_iff (Ω : HarmonicMaps.OpenDomain 3) (u : Point → S0)
    (a : Ω.val) : StratificationTheory.IsRegularPoint Ω (frobeniusField u) a ↔
      ∃ (W : Set Point) (v : Point → S0),
        IsOpen W ∧ a.val ∈ W ∧ W ⊆ Ω.val ∧ ContDiffOn ℝ ∞ v W ∧
          u =ᵐ[volume.restrict W] v := by
  constructor
  · rintro ⟨r, hr, hB, w, hw, hwu⟩
    let v (x : Point) : S0 := frobeniusCoordinateEquiv.symm (w x)
    have hes : ContDiff ℝ ∞ (frobeniusCoordinateEquiv.symm : HarmonicMaps.Ambient 5 → S0) :=
      frobeniusCoordinateEquiv.symm.toContinuousLinearEquiv.toContinuousLinearMap.contDiff
    have hvs : ContDiffOn ℝ ∞ v (Metric.ball a.val r) := hes.comp_contDiffOn hw
    refine ⟨Metric.ball a.val r, v, Metric.isOpen_ball, Metric.mem_ball_self hr, hB, hvs, ?_⟩
    filter_upwards [hwu] with x h
    change w x = frobeniusCoordinateEquiv (u x) at h
    simp only [v, h, LinearIsometryEquiv.symm_apply_apply]
  · rintro ⟨W, v, hW, haW, hWΩ, hv, huv⟩
    obtain ⟨r, hr, hB⟩ := Metric.isOpen_iff.mp hW a.val haW
    have he : ContDiff ℝ ∞ (frobeniusCoordinateEquiv : S0 → HarmonicMaps.Ambient 5) :=
      frobeniusCoordinateEquiv.toContinuousLinearEquiv.toContinuousLinearMap.contDiff
    have hvs : ContDiffOn ℝ ∞ (frobeniusField v) (Metric.ball a.val r) :=
      he.comp_contDiffOn (hv.mono hB)
    refine ⟨r, hr, hB.trans hWΩ, frobeniusField v, hvs, ?_⟩
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hB huv] with x h
    exact congrArg frobeniusCoordinateEquiv h.symm

theorem mem_singularSet_iff_upstream (Ω : HarmonicMaps.OpenDomain 3) (u : Point → S0)
    (a : Ω.val) :
    a.val ∈ singularSet Ω.val u ↔ a ∈ StratificationTheory.singularSet Ω (frobeniusField u) := by
  change (a.val ∈ Ω.val ∧ _) ↔ ¬ StratificationTheory.IsRegularPoint Ω (frobeniusField u) a
  rw [upstreamIsRegularPoint_iff Ω u a]
  simp only [a.property, true_and]

theorem singularSet_eq_upstream_image (Ω : HarmonicMaps.OpenDomain 3) (u : Point → S0) :
    singularSet Ω.val u = Subtype.val '' StratificationTheory.singularSet Ω (frobeniusField u) := by
  ext x
  constructor
  · intro hx
    have hxΩ : x ∈ Ω.val := hx.1
    exact ⟨⟨x, hxΩ⟩, (mem_singularSet_iff_upstream Ω u ⟨x, hxΩ⟩).1 hx, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact (mem_singularSet_iff_upstream Ω u a).2 ha

/-- Isolating balls at every interior point give finiteness on compact subsets. -/
theorem locallyFiniteIn_of_isolating_balls {U S : Set Point}
    (h : ∀ a ∈ U, ∃ r : ℝ, 0 < r ∧ ∀ x ∈ S, dist x a < r → x = a) :
    LocallyFiniteIn U S := by
  classical
  intro K hK hKU
  have hKiso : ∀ a : K, ∃ r : ℝ, 0 < r ∧ ∀ x ∈ S, dist x a.val < r → x = a.val :=
    fun a => h a.val (hKU a.property)
  choose r hr hIso using hKiso
  have hcover : K ⊆ ⋃ a : K, Metric.ball a.val (r a) := by
    intro a ha
    exact mem_iUnion.mpr ⟨⟨a, ha⟩, Metric.mem_ball_self (hr ⟨a, ha⟩)⟩
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover (fun a : K => Metric.ball a.val (r a))
    (fun _ => Metric.isOpen_ball) hcover
  refine (s.finite_toSet.image (@Subtype.val Point (fun x => x ∈ K))).subset ?_
  intro x hx
  obtain ⟨a, ha⟩ := mem_iUnion.mp (hs hx.2)
  obtain ⟨has, hxB⟩ := mem_iUnion.mp ha
  exact ⟨a, has, (hIso a x hx.1 hxB).symm⟩

/-- Apply the upstream singular-isolation theorem to a given bundled target
whose carrier is precisely the vacuum image in Frobenius coordinates. -/
theorem singularSet_no_interior_accumulation_of_upstreamTarget (a : BulkCoefficients)
    (Ω : HarmonicMaps.OpenDomain 3) (N : HarmonicMaps.CompactSmoothEmbeddedTarget 5)
    (hN : N.carrierSet = (frobeniusCoordinateEquiv : S0 → HarmonicMaps.Ambient 5) '' vacuum a)
    (u : Point → S0) (D : Point → Gradient) (h : IsLocalDirichletMinimizer a Ω.val u D) :
    ∀ b ∈ Ω.val, ∃ r : ℝ, 0 < r ∧ ∀ x ∈ singularSet Ω.val u, dist x b < r → x = b := by
  obtain ⟨hu, huN, huMin⟩ := (isLocalDirichletMinimizer_iff_upstream a Ω N hN u D).1 h
  intro b hb
  obtain ⟨r, hr, hIso⟩ := StratificationTheory.singularSet_no_accumulation_three
    N Ω (frobeniusField u) (frobeniusGradient D) hu huN huMin ⟨b, hb⟩
  refine ⟨r, hr, ?_⟩
  intro x hx hdist
  let x' : Ω.val := ⟨x, hx.1⟩
  exact congrArg Subtype.val
    (hIso x' ((mem_singularSet_iff_upstream Ω u x').1 hx) hdist)

theorem locallyFiniteIn_singularSet_of_upstreamTarget (a : BulkCoefficients)
    (Ω : HarmonicMaps.OpenDomain 3) (N : HarmonicMaps.CompactSmoothEmbeddedTarget 5)
    (hN : N.carrierSet = (frobeniusCoordinateEquiv : S0 → HarmonicMaps.Ambient 5) '' vacuum a)
    (u : Point → S0) (D : Point → Gradient) (h : IsLocalDirichletMinimizer a Ω.val u D) :
    LocallyFiniteIn Ω.val (singularSet Ω.val u) :=
  locallyFiniteIn_of_isolating_balls
    (singularSet_no_interior_accumulation_of_upstreamTarget a Ω N hN u D h)

/-- The normalized three-dimensional Dirichlet energy has the same factor of
one half as the unscaled tensor energy. -/
theorem normalizedDirichletEnergy_eq_half_upstream (D : Point → Gradient)
    (c : Point) (R : HarmonicMaps.PositiveRadius) :
    ENNReal.ofReal (R.val⁻¹) * dirichletEnergy (Metric.ball c R.val) D =
      ENNReal.ofReal (1 / 2 : ℝ) * HarmonicMaps.normalizedEnergy (frobeniusGradient D) c R := by
  rw [dirichletEnergy_eq_half_upstream, HarmonicMaps.normalizedEnergy]
  rw [show (2 : ℤ) - (↑(3 : ℕ) : ℤ) = -1 by decide, zpow_neg_one]
  ac_rfl

/-- The small-energy smooth representative and its estimates transfer to tensor
coordinates. The energy threshold uses the upstream normalization. -/
theorem smallEnergySmoothRegularity_of_upstreamTarget (a : BulkCoefficients)
    (N : HarmonicMaps.CompactSmoothEmbeddedTarget 5)
    (hN : N.carrierSet = (frobeniusCoordinateEquiv : S0 → HarmonicMaps.Ambient 5) '' vacuum a) :
    ∃ ε γ : ℝ, ∃ C : ℕ → ℝ≥0, 0 < ε ∧ 0 < γ ∧ γ < 1 ∧
      ∀ (Ω : HarmonicMaps.OpenDomain 3) (u : Point → S0) (D : Point → Gradient),
        IsLocalDirichletMinimizer a Ω.val u D →
        ∀ (c : Point) (R : HarmonicMaps.PositiveRadius),
          Metric.closedBall c R.val ⊆ Ω.val →
          let E := HarmonicMaps.normalizedEnergy (frobeniusGradient D) c R
          E ≤ ENNReal.ofReal ε →
          ∃ v : Point → S0,
            ContDiffOn ℝ ∞ v (Metric.ball c (R.val / 2)) ∧
            u =ᵐ[volume.restrict (Metric.ball c (R.val / 2))] v ∧
            (∀ x ∈ Metric.ball c (R.val / 2), v x ∈ vacuum a) ∧
            (∀ x ∈ Metric.ball c (R.val / 2), ‖v x - v c‖ ≤ (C 0 : ℝ) * Real.sqrt E.toReal) ∧
            (∀ k : ℕ, 1 ≤ k → ∀ x ∈ Metric.ball c (R.val / 2),
              ‖iteratedFDeriv ℝ k v x‖ ≤ (C k : ℝ) *
                Real.rpow R.val (-(k : ℝ)) * Real.sqrt E.toReal) ∧
            (∀ k : ℕ, 1 ≤ k → HolderToCK.HolderBoundOn (Metric.ball c (R.val / 2))
              (iteratedFDeriv ℝ k v) γ
              ((C k : ℝ) * Real.rpow R.val (-((k : ℝ) + γ)) * Real.sqrt E.toReal)) ∧
            ∀ z : Point → S0, ContinuousOn z (Metric.ball c (R.val / 2)) →
              u =ᵐ[volume.restrict (Metric.ball c (R.val / 2))] z →
              EqOn z v (Metric.ball c (R.val / 2)) := by
  obtain ⟨ε, γ, C, hε, hγ, hγone, hreg⟩ :=
    HolderToCK.smallEnergySmoothRegularity (by decide : 2 ≤ 3) N
  refine ⟨ε, γ, C, hε, hγ, hγone, ?_⟩
  intro Ω u D h c R hc E hE
  obtain ⟨hu, hvalues, hmin⟩ := (isLocalDirichletMinimizer_iff_upstream a Ω N hN u D).1 h
  obtain ⟨w, hw, hrep, hpoint, hosc, hderiv, hHolder, _⟩ :=
    hreg Ω (frobeniusField u) (frobeniusGradient D) hu hvalues hmin c R hc hE
  let v : Point → S0 := frobeniusCoordinateEquiv.symm ∘ w
  have hes : ContDiff ℝ ∞ (frobeniusCoordinateEquiv.symm : HarmonicMaps.Ambient 5 → S0) :=
    frobeniusCoordinateEquiv.symm.toContinuousLinearEquiv.toContinuousLinearMap.contDiff
  have hvae : u =ᵐ[volume.restrict (Metric.ball c (R.val / 2))] v := by
    have hball : MeasurableSet (Metric.ball c (R.val / 2)) := Metric.isOpen_ball.measurableSet
    filter_upwards [hrep.2, ae_restrict_mem hball] with x hx hxb
    have h : w x = frobeniusCoordinateEquiv (u x) := hx hxb
    simp only [v, Function.comp_apply, h, LinearIsometryEquiv.symm_apply_apply]
  have hvs : ContDiffOn ℝ ∞ v (Metric.ball c (R.val / 2)) := hes.comp_contDiffOn hw
  refine ⟨v, hvs, hvae, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    have h := hpoint x hx
    rw [hN] at h
    obtain ⟨A, hA, hAw⟩ := h
    change frobeniusCoordinateEquiv.symm (w x) ∈ vacuum a
    rw [← hAw, LinearIsometryEquiv.symm_apply_apply]
    exact hA
  · intro x hx
    change ‖frobeniusCoordinateEquiv.symm (w x) - frobeniusCoordinateEquiv.symm (w c)‖ ≤ _
    rw [← map_sub frobeniusCoordinateEquiv.symm, LinearIsometryEquiv.norm_map]
    exact hosc x hx
  · intro k hk x hx
    change ‖iteratedFDeriv ℝ k (frobeniusCoordinateEquiv.symm ∘ w) x‖ ≤ _
    rw [LinearIsometryEquiv.norm_iteratedFDeriv_comp_left]
    exact hderiv k hk x hx
  · intro k hk x hx y hy
    let L := frobeniusCoordinateEquiv.symm.toLinearIsometry.toContinuousLinearMap
    have hcomp (z : Point) : iteratedFDeriv ℝ k v z =
        L.compContinuousMultilinearMap (iteratedFDeriv ℝ k w z) :=
      frobeniusCoordinateEquiv.symm.toContinuousLinearEquiv.iteratedFDeriv_comp_left
    have hsub : L.compContinuousMultilinearMap (iteratedFDeriv ℝ k w x) -
        L.compContinuousMultilinearMap (iteratedFDeriv ℝ k w y) =
        L.compContinuousMultilinearMap (iteratedFDeriv ℝ k w x - iteratedFDeriv ℝ k w y) := by
      apply ContinuousMultilinearMap.ext
      intro m
      simp [ContinuousLinearMap.compContinuousMultilinearMap_coe]
    rw [hcomp x, hcomp y, hsub]
    change ‖L.compContinuousMultilinearMap (iteratedFDeriv ℝ k w x - iteratedFDeriv ℝ k w y)‖ ≤ _
    dsimp only [L]
    rw [LinearIsometry.norm_compContinuousMultilinearMap]
    exact hHolder k hk x hx y hy
  · intro z hz huzae
    exact Measure.eqOn_open_of_ae_eq (huzae.symm.trans hvae) Metric.isOpen_ball hz hvs.continuousOn

end Thesis
end
end
