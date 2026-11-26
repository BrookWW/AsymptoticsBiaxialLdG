module

public import Thesis.Variational.SmoothDomainLocalZeroTrace
import Thesis.Variational.BoundaryLimit
import Thesis.Upstream.ZeroTraceSmoothTransport
import StratificationTheory.Foundation.CompactSobolevCutoff
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-! The bounded trace on a smooth domain has exactly the original
compact-smooth zero-trace closure as its kernel. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set Topology
open scoped BigOperators ContDiff ENNReal Manifold Matrix.Norms.Frobenius

namespace Thesis

variable {Ω : Set Point}

local instance smoothTraceTensorContinuousENorm : ContinuousENorm S0 :=
  @SeminormedAddGroup.toContinuousENorm S0 inferInstance

private theorem exists_zeroTrace_cutoff_at_closure
    (hΩ : IsSmoothDomain Ω)
    {u : Point → Ambient 5} {D : Point → HarmonicMaps.Gradient 3 5}
    (hu : MemW12 ⟨Ω,hΩ.1.1⟩ u D)
    (hZero : ∀ (B : SmoothDomainEpigraphBox Ω) (H : B.NormalTrace 5 B.radius),
      B.RepresentsNormalTrace u H → H ⟨0,le_rfl,B.radius_pos.le⟩ = 0)
    {x : Point} (hx : x ∈ closure Ω) :
    ∃ (V : OpenDomain 3), x ∈ V.val ∧ Bornology.IsBounded V.val ∧
      ∀ {χ : Point → ℝ}, ContDiff ℝ ∞ χ → HasCompactSupport χ → tsupport χ ⊆ V.val →
        ∃ G : Point → HarmonicMaps.Gradient 3 5,
          HasZeroBoundaryValues ⟨Ω,hΩ.1.1⟩ (fun y => χ y • u y) G := by
  by_cases hi : x ∈ Ω
  · refine ⟨⟨Ω,hΩ.1.1⟩,hi,hΩ.1.2.2,?_⟩
    intro χ hχ hc hSupp
    let G (y : Point) (j : Fin 3) := coordinateDerivative χ hχ j y • u y + χ y • D y j
    have h := hu.to_memW12Loc.smoothCutoff_univ hχ hc hSupp
    have hVal : Function.support (fun y => χ y • u y) ⊆ tsupport χ :=
      (Function.support_smul_subset_left _ _).trans (subset_tsupport χ)
    have hGrad (j : Fin 3) : Function.support (fun y => G y j) ⊆ tsupport χ := by
      intro y hy
      by_contra hn
      have hX : χ y = 0 := image_eq_zero_of_notMem_tsupport hn
      have hDχ : coordinateDerivative χ hχ j y = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h => hn (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single j 1) h))
      exact hy (by simp only [G,hX,hDχ,zero_smul,add_zero])
    exact ⟨G,hasZeroBoundaryValues_of_compact_global_graph ⟨Ω,hΩ.1.1⟩ h hc hSupp hVal hGrad⟩
  · have hFront : x ∈ frontier Ω := by rw [frontier,hΩ.1.1.interior_eq]; exact ⟨hx,hi⟩
    obtain ⟨B,hB⟩ := hΩ.exists_epigraph_box hFront
    obtain ⟨_,_,hTrace⟩ := B.exists_normalTrace_bound (q := 5) hΩ.1.1 B.radius_pos le_rfl
    obtain ⟨H,hH,_⟩ := hTrace hu
    have hZ := hZero B H hH
    refine ⟨B.physicalRectangle (-B.radius) B.radius,B.normalChart_mem_zero hB B.radius_pos,
      B.isBounded_physicalRectangle le_rfl le_rfl,?_⟩
    intro χ hχ hc hSupp
    exact B.hasZeroBoundaryValues_cutoff_of_normalTrace_zero hΩ.1 B.radius_pos le_rfl hu H hH hZ hχ hc hSupp

private theorem hasZeroTrace_sum (hΩ : IsOpen Ω) {ι : Type*} (I : Finset ι)
    {f : ι → Point → S0} {G : ι → Point → Gradient}
    (h : ∀ i ∈ I, HasZeroTrace Ω (f i) (G i)) :
    HasZeroTrace Ω (∑ i ∈ I, f i) (∑ i ∈ I, G i) := by
  classical
  induction I using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have hGrad : ClassicalGradient (0 : Point → S0) = 0 := by
      funext x j
      simp [ClassicalGradient, coordDeriv]
    have h0 : HasZeroTrace Ω (0 : Point → S0) (ClassicalGradient 0) :=
      hasZeroTrace_of_contDiff_hasCompactSupport hΩ contDiff_const HasCompactSupport.zero (by simp)
    simpa only [hGrad] using h0
  | @insert i I hi ih =>
    simp only [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).add hΩ (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

private theorem hasZeroTrace_of_zero_normalTraces
    (hΩ : IsSmoothDomain Ω) {u : Point → S0} {D : Point → Gradient} (hu : MemH1 Ω u D)
    (hZero : ∀ (B : SmoothDomainEpigraphBox Ω) (H : B.NormalTrace 5 B.radius),
      B.RepresentsNormalTrace (frobeniusField u) H → H ⟨0,le_rfl,B.radius_pos.le⟩ = 0) :
    HasZeroTrace Ω u D := by
  classical
  let O : OpenDomain 3 := ⟨Ω,hΩ.1.1⟩
  have huW := (memH1_iff_memW12 O u D).1 hu
  let K := closure Ω
  have hK : IsCompact K := hΩ.1.2.2.isCompact_closure
  have hLocal (x : K) := exists_zeroTrace_cutoff_at_closure hΩ huW hZero x.property
  choose V hMem hBound hPieces using hLocal
  have hCover : K ⊆ ⋃ x : K, (V x).val := fun x hx => mem_iUnion.2 ⟨⟨x,hx⟩,hMem ⟨x,hx⟩⟩
  obtain ⟨I,hI⟩ := hK.elim_finite_subcover (fun x : K => (V x).val) (fun x => (V x).property) hCover
  have hFin : K ⊆ ⋃ i : I, (V i).val := by rwa [iUnion_subtype]
  obtain ⟨ρ,hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, Point)
    isClosed_closure (fun i : I => (V i).val) (fun i => (V i).property) hFin
  let χ (i : I) (x : Point) := ρ i x
  have hC (i : I) : ContDiff ℝ ∞ (χ i) := (ρ i).contMDiff.contDiff
  have hc (i : I) : HasCompactSupport (χ i) :=
    (hBound i).isCompact_closure.of_isClosed_subset (isClosed_tsupport (χ i)) ((hρ i).trans subset_closure)
  choose A hA using fun i : I => hPieces i (hC i) (hc i) (hρ i)
  let f (i : I) (x : Point) := χ i x • u x
  let G (i : I) (x : Point) (j : Fin 3) := frobeniusCoordinateEquiv.symm (A i x j)
  have hG (i : I) : frobeniusGradient (G i) = A i := by
    funext x j
    exact frobeniusCoordinateEquiv.apply_symm_apply _
  have hF (i : I) : frobeniusField (f i) = fun x => χ i x • frobeniusField u x := by
    funext x
    exact frobeniusCoordinateEquiv.map_smul _ _
  have h0 (i : I) : HasZeroTrace Ω (f i) (G i) := by
    apply (hasZeroTrace_iff_hasZeroBoundaryValues O _ _).2
    rw [hF,hG]
    exact hA i
  have hFull := hasZeroTrace_sum hΩ.1.1 Finset.univ (fun i _ => h0 i)
  have hEq : (∑ i : I, f i) =ᵐ[volume.restrict Ω] u := by
    filter_upwards [ae_restrict_mem hΩ.1.1.measurableSet] with x hx
    have hSum : ∑ i : I, χ i x = 1 := ρ.sum_finsupport' x (subset_closure hx) (Finset.subset_univ _)
    simp only [Finset.sum_apply, f, ← Finset.sum_smul, hSum, one_smul]
  have hPair := hFull.1.congr_ae hEq EventuallyEq.rfl
  letI : IsFiniteMeasure (volume.restrict Ω) := isFiniteMeasure_restrict.mpr hΩ.1.2.2.measure_lt_top.ne
  have hLoc {w : Point → S0} (hw : MemLp w 2 (volume.restrict Ω)) : LocallyIntegrableOn w Ω volume :=
    (show IntegrableOn w Ω volume from hw.integrable (by norm_num)).locallyIntegrableOn
  have hGrad := hPair.2.2.ae_eq hu.2.2 hΩ.1.1 (fun j => hLoc (hPair.2.1 j)) (fun j => hLoc (hu.2.1 j))
  exact hFull.congr_ae hEq hGrad

private theorem hasZeroTrace_of_nativeTraceExtension_zero
    (hΩ : IsSmoothDomain Ω) (T : SobolevL2Coordinates Ω →L[ℝ] SobolevTraceL2 Ω)
    (hT : ∀ {f : Point → Ambient 5} (hf : ContDiff ℝ ∞ f),
      T (nativeSobolevL2Point hΩ.1.1 (hΩ.memW12_of_smooth hf)) =
        (hΩ.memLp_continuous_frontier hf.continuous).toLp (fun x : frontier Ω => f x))
    {u : Point → S0} {D : Point → Gradient} (hu : MemH1 Ω u D)
    (hZero : T (sobolevL2Point hu) = 0) : HasZeroTrace Ω u D := by
  let O : OpenDomain 3 := ⟨Ω,hΩ.1.1⟩
  have huW := (memH1_iff_memW12 O u D).1 hu
  have hNativeEq : sobolevL2Point hu = nativeSobolevL2Point hΩ.1.1 huW :=
    sobolevL2Point_eq_upstream hu hΩ.1.1 huW
  have hZero' : T (nativeSobolevL2Point hΩ.1.1 huW) = 0 := hNativeEq ▸ hZero
  apply hasZeroTrace_of_zero_normalTraces hΩ hu
  intro B H hH
  exact hΩ.normalTrace_zero_of_boundaryExtension_zero T hT huW hZero' B B.radius_pos le_rfl H hH

/-- The original values of a continuous weak graph determine its zero trace
on the smooth boundary. -/
theorem IsSmoothDomain.hasZeroTrace_of_continuousOn_zero_frontier
    (hΩ : IsSmoothDomain Ω) {u : Point → S0} {D : Point → Gradient} (hu : MemH1 Ω u D)
    (hc : ContinuousOn u (closure Ω)) (hB : EqOn u (fun _ => 0) (frontier Ω)) :
    HasZeroTrace Ω u D := by
  apply hasZeroTrace_of_zero_normalTraces hΩ hu
  intro B H hH
  have hCont : ContinuousOn (frobeniusField u) (closure Ω) :=
    frobeniusCoordinateEquiv.continuous.comp_continuousOn hc
  let z : Icc (0 : ℝ) B.radius := ⟨0,le_rfl,B.radius_pos.le⟩
  obtain ⟨hL,hRaw⟩ := hH.eq_raw_of_continuousOn_closure (B := B) B.radius_pos le_rfl hCont z
  rw [hRaw]
  apply Lp.ext
  filter_upwards [hL.coeFn_toLp,Lp.coeFn_zero (Ambient 5) 2 (volume.restrict B.planeDomain.val),
    ae_restrict_mem B.planeDomain.property.measurableSet] with y hy hZero hMem
  rw [hy,hZero]
  have h := (B.wallMap ⟨y,hMem⟩).property
  change B.normalParameter (y,0) ∈ frontier Ω at h
  change frobeniusCoordinateEquiv (u (B.normalParameter (y,0))) = 0
  rw [hB h,map_zero]

private theorem nativeTraceExtension_zero_of_hasZeroTrace
    (hΩ : IsSmoothDomain Ω) (T : SobolevL2Coordinates Ω →L[ℝ] SobolevTraceL2 Ω)
    (hT : ∀ {f : Point → Ambient 5} (hf : ContDiff ℝ ∞ f),
      T (nativeSobolevL2Point hΩ.1.1 (hΩ.memW12_of_smooth hf)) =
        (hΩ.memLp_continuous_frontier hf.continuous).toLp (fun x : frontier Ω => f x))
    {u : Point → S0} {D : Point → Gradient} (hu : MemH1 Ω u D)
    (h : HasZeroTrace Ω u D) : T (sobolevL2Point hu) = 0 := by
  let O : OpenDomain 3 := ⟨Ω,hΩ.1.1⟩
  obtain ⟨hU,f,hf,hSupp,hF,hD⟩ := (hasZeroTrace_iff_hasZeroBoundaryValues O _ _).1 h
  have hNativeEq : sobolevL2Point hu = nativeSobolevL2Point hΩ.1.1 hU :=
    sobolevL2Point_eq_upstream hu hΩ.1.1 hU
  have hJ := nativeSobolevL2Point_tendsto hΩ.1.1 (fun n => hΩ.memW12_of_smooth (hf n)) hU hF hD
  have hLim := (T.continuous.tendsto _).comp hJ
  have hZero (n : ℕ) : T (nativeSobolevL2Point hΩ.1.1 (hΩ.memW12_of_smooth (hf n))) = 0 := by
    rw [hT]
    apply Lp.ext
    filter_upwards [(hΩ.memLp_continuous_frontier (hf n).continuous).coeFn_toLp,
      Lp.coeFn_zero (Ambient 5) 2 (frontierSurfaceMeasure Ω)] with x h₁ h₂
    rw [h₁,h₂]
    exact image_eq_zero_of_notMem_tsupport (fun hX =>
      Set.disjoint_left.mp (disjoint_frontier_iff_isOpen.mpr hΩ.1.1) x.property ((hSupp n).2 hX))
  have hZeroLim : Tendsto (fun n => T (nativeSobolevL2Point hΩ.1.1 (hΩ.memW12_of_smooth (hf n))))
      atTop (𝓝 0) := tendsto_const_nhds.congr (fun n => (hZero n).symm)
  rw [hNativeEq]
  exact tendsto_nhds_unique hLim hZeroLim

/-- The true Sobolev trace on the smooth domain, with the literal Frobenius
restriction on smooth maps and exactly the intrinsic Dirichlet kernel. -/
theorem IsSmoothDomain.exists_sobolevTraceOperator (hΩ : IsSmoothDomain Ω) :
    Nonempty (SobolevTraceOperator Ω) := by
  obtain ⟨T,hT⟩ := hΩ.exists_smoothTraceExtension
  refine ⟨⟨T,?_,?_⟩⟩
  · intro u D hu
    exact ⟨hasZeroTrace_of_nativeTraceExtension_zero hΩ T hT hu,
      nativeTraceExtension_zero_of_hasZeroTrace hΩ T hT hu⟩
  · intro B hB hBH
    have hF : ContDiff ℝ ∞ (frobeniusField B) := frobeniusCoordinateEquiv.contDiff.comp hB
    have hCol (x : Point) (i : Fin 3) :
        coordinateDerivative (frobeniusField B) hF i x = frobeniusGradient (ClassicalGradient B) x i := by
      let L := frobeniusCoordinateEquiv.toContinuousLinearEquiv.toContinuousLinearMap
      have hChain := (L.hasFDerivAt.comp x (hB.differentiable (by simp) x).hasFDerivAt).fderiv
      exact congrArg (fun l : Point →L[ℝ] Ambient 5 => l (axis i)) hChain
    have hEq : (fun x i => coordinateDerivative (frobeniusField B) hF i x) =
        frobeniusGradient (ClassicalGradient B) := funext fun x => funext (hCol x)
    have hW := hΩ.memW12_of_smooth hF
    rw [hEq] at hW
    have hNative : sobolevL2Point hBH = nativeSobolevL2Point hΩ.1.1 (hΩ.memW12_of_smooth hF) := by
      rw [sobolevL2Point_eq_upstream hBH hΩ.1.1 hW]
      ext1 i
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · change (hW.2.2 j).toLp _ = ((hΩ.memW12_of_smooth hF).2.2 j).toLp _
        exact MemLp.toLp_congr _ _ (Eventually.of_forall fun x => (hCol x j).symm)
    rw [hNative,hT]
    exact (hΩ.memLp_continuous_frontier hF.continuous).coeFn_toLp

end Thesis
