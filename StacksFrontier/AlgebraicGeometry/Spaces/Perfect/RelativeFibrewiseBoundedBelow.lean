module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.AffinePseudoCoherentSections
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.InverseImageSliceTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LocallyBoundedBelow
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RelativeSchemeCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ResidueFibreCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherentCohomologyUnconditional
public import StacksFrontier.Homology.RelativelyPerfect.Criterion
public import StacksFrontier.Homology.TorAmplitude.CanonicalCertificate
public import StacksFrontier.Homology.TorAmplitude.CanonicalFiniteTorDimension

/-!
# Relative perfectness of algebraic spaces and boundedness below on the fibres

This file collects the ingredients of Stacks 0GFK: for a morphism `f : X ⟶ S` from an algebraic
space to a scheme which is flat and locally of finite presentation and a pseudo-coherent
`E ∈ D(𝒪_X)`, `E` is `S`-perfect exactly when `E` and all its derived fibres are locally bounded
below. Everything is local, and on an affine square of étale charts the statement is the algebra
of Stacks 0GHJ.

## Main results

* `AlgebraicGeometry.Space.isRelativelyPerfectCanonical_iff_isGE`: Stacks 0GHJ for a flat ring
  map of finite presentation, with the canonical derived tensor product.
* `AlgebraicGeometry.Space.isPerfectRelativeToCanonical_iff_isLocallyBoundedBelow`:
  Stacks 0GFK, with the canonical derived tensor product.

## References

* [Stacks Project, Tag 0GFK](https://stacks.math.columbia.edu/tag/0GFK)
* [Stacks Project, Tag 0GHJ](https://stacks.math.columbia.edu/tag/0GHJ)
-/

@[expose] public noncomputable section

attribute [local instance] AlgebraicGeometry.Space.sheafTensor_additive_inverseImageRingedSite_over
  AlgebraicGeometry.Space.sheafTensor_obj_additive_inverseImageRingedSite_over
  AlgebraicGeometry.Space.hasMapBifunctor_sheafTensor_inverseImageRingedSite_over

attribute [local instance] AlgebraicGeometry.RingedSite.sliceHasSheafify
  AlgebraicGeometry.RingedSite.sliceWEqualsLocallyBijective

open CategoryTheory CategoryTheory.Limits StacksDraft.TorAmplitude

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance 5000] SheafOfModules.instAbelian

/-- **Stacks 0GHJ along a flat ring map of finite presentation, at the canonical derived tensor
product.** For `φ : R ⟶ A` flat and of finite presentation and `K ∈ D(A)` pseudo-coherent, `K` is
`R`-perfect (pseudo-coherent with finite Tor dimension over `R`) exactly when `K` is bounded below
and every derived fibre `K ⊗^L_R κ(p)` is bounded below. -/
theorem isRelativelyPerfectCanonical_iff_isGE {R A : Type u} [CommRing R] [CommRing A]
    (φ : R →+* A) (hfl : φ.Flat) (hfp : φ.FinitePresentation)
    (K : DerivedCategory (ModuleCat.{u} A)) (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K) :
    (StacksDraft.PseudoCoherence.IsPseudoCoherent K ∧
        HasFiniteTorDimensionCanonical R ((ModuleCat.restrictScalars φ).mapDerivedCategory.obj K)) ↔
      (∃ a : ℤ, K.IsGE a) ∧
        ∀ p : PrimeSpectrum R, ∃ a : ℤ,
          ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
              (algebraMap R p.asIdeal.ResidueField)).functor.obj
            ((ModuleCat.restrictScalars φ).mapDerivedCategory.obj K)).IsGE a := by
  let := φ.toAlgebra
  have : Module.Flat R A := hfl
  have : Algebra.FinitePresentation R A := hfp
  rw [hasFiniteTorDimensionCanonical_iff]
  exact PseudoCoherence.isRelativelyPerfect_iff_isBoundedBelow_and_fibres_isBoundedBelow
    (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R).tensor
    (canonicalTensorComparison R)
    (canonicalTensorIsLeftDerived R) K hK

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {T : BigFppfOver B S hS}
  {X : AlgebraicSpaces B S hS}

private theorem exists_isAffineOpen_mem_of_scheme {Y : Scheme} (t : Y) :
    ∃ O : Y.Opens, IsAffineOpen O ∧ t ∈ O := by
  obtain ⟨O, hO, htO, -⟩ := exists_isAffineOpen_mem_and_subset (U := (⊤ : Y.Opens)) (x := t) trivial
  exact ⟨O, hO, htO⟩

/-- The derived sections of a pseudo-coherent `E` on the chart of an affine chart square are
pseudo-coherent. -/
private theorem isPseudoCoherent_representedAffineDerivedSections_chart {f : X ⟶ representedSpace T}
    (c : OpenAffineChartSquare f) (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherent E) (hEq : QcohDerived B S hS X E) :
    StacksDraft.PseudoCoherence.IsPseudoCoherent
      ((representedAffineDerivedSections B S hS
        ((SmallEtale.toOver B S hS X.1).obj c.toChartDiagram.U)).obj
        ((smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X c.toChartDiagram.U)).obj
          E)) :=
  (StacksDraft.PseudoCoherence.pseudoCoherent_iff_all _).2 fun m =>
    (isPseudoCoherentFrom_iff_forall_isAffineChart X E hEq m).1
      ((RingedSite.isPseudoCoherent_iff_forall_isPseudoCoherentFrom _ E).1 hE m)
      c.toChartDiagram.U c.isAffine_U

/-- **Stacks 0GHJ on an affine chart square.** The pullback of a pseudo-coherent `E` to the chart
of an affine chart square is perfect relative to the base chart exactly when its derived sections
and all their derived fibres are bounded below. -/
private theorem isPerfectRelativeToCanonical_chart_iff_isGE (f : X ⟶ representedSpace T)
    (hfl : IsFlat B S hS f.hom) (hlfp : IsLocallyOfFinitePresentation B S hS f.hom)
    (c : OpenAffineChartSquare f) (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherent E) (hEq : QcohDerived B S hS X E) :
    IsPerfectRelativeToCanonical.{u, u + 1, u + 1} B S hS
        (representedSpaceMap B S hS c.toChartDiagram.g)
        (isFlat_yoneda_map B S hS c.toChartDiagram.g (flat_chartDiagram_g f hfl c.toChartDiagram))
        (isLocallyOfFinitePresentation_yoneda_map B S hS c.toChartDiagram.g
          (locallyOfFinitePresentation_chartDiagram_g f hlfp c.toChartDiagram))
        ((smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X c.toChartDiagram.U)).obj
          E) ↔
      (∃ a : ℤ, ((representedAffineDerivedSections B S hS
          ((SmallEtale.toOver B S hS X.1).obj c.toChartDiagram.U)).obj
          ((smallEtaleDerivedModulePullback B S hS
            (chartToSpace B S hS X c.toChartDiagram.U)).obj E)).IsGE a) ∧
        ∀ p : PrimeSpectrum Γ(chartScheme c.toChartDiagram.V, ⊤), ∃ a : ℤ,
            ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
                (algebraMap _ p.asIdeal.ResidueField)).functor.obj
              ((ModuleCat.restrictScalars
                ((BigFppfOver.toScheme B S hS).map
                  c.toChartDiagram.g).appTop.hom).mapDerivedCategory.obj
                ((representedAffineDerivedSections B S hS
                  ((SmallEtale.toOver B S hS X.1).obj c.toChartDiagram.U)).obj
                  ((smallEtaleDerivedModulePullback B S hS
                    (chartToSpace B S hS X c.toChartDiagram.U)).obj E)))).IsGE a :=
  (isPerfectRelativeToCanonical_chart_iff f hfl hlfp c.toChartDiagram E hEq).trans
    ((isPerfectRelativeTo_chartObject_iff_of_isAffine f hfl hlfp c.toChartDiagram E hEq).trans
      (isRelativelyPerfectCanonical_iff_isGE _
        (HasRingHomProperty.appTop (P := @Flat) _ (flat_chartDiagram_g f hfl c.toChartDiagram))
        (HasRingHomProperty.appTop (P := @LocallyOfFinitePresentation) _
          (locallyOfFinitePresentation_chartDiagram_g f hlfp c.toChartDiagram)) _
        (isPseudoCoherent_representedAffineDerivedSections_chart c E hE hEq)))

/-- The forward direction of Stacks 0GFK: a `T`-perfect pseudo-coherent `E` is locally bounded
below, and so are its derived pullbacks to the fibres. -/
private theorem isLocallyBoundedBelow_of_isPerfectRelativeToCanonical (f : X ⟶ representedSpace T)
    (hfl : IsFlat B S hS f.hom) (hlfp : IsLocallyOfFinitePresentation B S hS f.hom)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherent E)
    (hrel : IsPerfectRelativeToCanonical.{u, u + 1, u + 1} B S hS f hfl hlfp E) :
    IsLocallyBoundedBelow X E ∧ ∀ s : (BigFppfOver.toScheme B S hS).obj T,
      IsLocallyBoundedBelow (residueFibre f s)
        ((smallEtaleDerivedModulePullback B S hS (residueFibreι f s)).obj E) := by
  have hEq : QcohDerived B S hS X E :=
    derivedCategoryB_of_isPseudoCoherent_unconditional B S hS X.1 X.2 E hE
  have hc := fun c : OpenAffineChartSquare f =>
    (isPerfectRelativeToCanonical_chart_iff_isGE f hfl hlfp c E hE hEq).1
      (isPerfectRelativeToCanonical_smallEtaleDerivedModulePullback_of_isEtale
        (chartToSpace B S hS X c.toChartDiagram.U) (representedSpaceMap B S hS c.toChartDiagram.g) f
        (chartToSpace B S hS (representedSpace T) c.toChartDiagram.V) hfl hlfp _ _
        (isEtale_chartToSpace B S hS X c.toChartDiagram.U)
        (isEtale_chartToSpace B S hS (representedSpace T) c.toChartDiagram.V)
        (chartToSpace_comp_eq f c.toChartDiagram) E hrel)
  refine ⟨fun x => ?_, fun s x => ?_⟩
  · obtain ⟨O, hO, hxO⟩ :=
      exists_isAffineOpen_mem_of_scheme (pointsToScheme B S hS T (pointsMap B S hS _ f.hom x))
    obtain ⟨c, rfl, hx⟩ := OpenAffineChartSquare.exists_of_mem x O hO hxO
    obtain ⟨a, ha⟩ := (hc c).1
    have := c.isAffine_U
    refine ⟨c.U, hx, a, fun i hi => (isZero_over_homology_iff X E c.U i).2 ?_⟩
    exact (isZero_homology_iff_representedAffineDerivedSections
      ((SmallEtale.toOver B S hS X.1).obj c.toChartDiagram.U) _
      (derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _
        (chartToSpace B S hS X c.U) E hEq)
      i).2 ((DerivedCategory.isGE_iff _ a).1 ha i hi)
  · have hxs := pointsToScheme_pointsMap_residueFibreι f s x
    obtain ⟨O, hO, hsO⟩ := exists_isAffineOpen_mem_of_scheme s
    obtain ⟨c, rfl, hx⟩ := OpenAffineChartSquare.exists_of_mem
      (pointsMap B S hS _ (residueFibreι f s).hom x) O hO (hxs.symm ▸ hsO)
    have hs : s ∈ c.O := hsO
    have := c.isAffine_U
    have := c.isAffine_residueFibreChart s hs
    have := (OpenAffineChartSquare.isField_siteObject (T := T) s).isDomain
    obtain ⟨a, ha⟩ :=
      (hc c).2 ⟨RingHom.ker (c.residuePoint s hs).appTop.hom, RingHom.ker_isPrime _⟩
    have h1 := (c.isGE_representedAffineDerivedExtension_residueFibreChartFst_iff s hfl hs _ a).2 ha
    have h2 := (forall_isZero_homology_residueFibreChart_iff f s c.U E hEq a).2 h1
    exact ⟨residueFibreChart f s c.U, mem_range_residueFibreChart f s c.U x hx, a,
      fun i hi => (isZero_over_homology_iff _ _ _ i).2 (h2 i hi)⟩

/-- The reverse direction of Stacks 0GFK: a pseudo-coherent `E` which is locally bounded below,
together with its derived pullbacks to the fibres, is `T`-perfect. -/
private theorem isPerfectRelativeToCanonical_of_isLocallyBoundedBelow (f : X ⟶ representedSpace T)
    (hfl : IsFlat B S hS f.hom) (hlfp : IsLocallyOfFinitePresentation B S hS f.hom)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherent E)
    (hbdd : IsLocallyBoundedBelow X E)
    (hfib : ∀ s : (BigFppfOver.toScheme B S hS).obj T, IsLocallyBoundedBelow (residueFibre f s)
      ((smallEtaleDerivedModulePullback B S hS (residueFibreι f s)).obj E)) :
    IsPerfectRelativeToCanonical.{u, u + 1, u + 1} B S hS f hfl hlfp E := by
  have hEq : QcohDerived B S hS X E :=
    derivedCategoryB_of_isPseudoCoherent_unconditional B S hS X.1 X.2 E hE
  refine isPerfectRelativeToCanonical_of_forall_isEtale f hfl hlfp (ι := OpenAffineChartSquare f)
    (fun c => chartToSpace B S hS X c.toChartDiagram.U)
    (fun c => representedSpaceMap B S hS c.toChartDiagram.g)
    (fun c => chartToSpace B S hS (representedSpace T) c.toChartDiagram.V)
    (fun c => isFlat_yoneda_map B S hS c.toChartDiagram.g
      (flat_chartDiagram_g f hfl c.toChartDiagram))
    (fun c => isLocallyOfFinitePresentation_yoneda_map B S hS c.toChartDiagram.g
      (locallyOfFinitePresentation_chartDiagram_g f hlfp c.toChartDiagram))
    (fun c => isEtale_chartToSpace B S hS X c.toChartDiagram.U) (fun x => ?_)
    (fun c => isEtale_chartToSpace B S hS (representedSpace T) c.toChartDiagram.V)
    (fun c => chartToSpace_comp_eq f c.toChartDiagram) E (fun c => ?_)
  · obtain ⟨O, hO, hxO⟩ :=
      exists_isAffineOpen_mem_of_scheme (pointsToScheme B S hS T (pointsMap B S hS _ f.hom x))
    obtain ⟨c, -, y, hy⟩ := OpenAffineChartSquare.exists_of_mem x O hO hxO
    exact ⟨c, y, hy⟩
  · refine (isPerfectRelativeToCanonical_chart_iff_isGE f hfl hlfp c E hE hEq).2 ⟨?_, fun p => ?_⟩
    · have := c.isAffine_U
      exact (isLocallyBoundedBelow_iff_exists_isGE_representedAffineDerivedSections
        ((SmallEtale.toOver B S hS X.1).obj c.toChartDiagram.U) _
        (derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _
          (chartToSpace B S hS X c.toChartDiagram.U) E hEq)).1
        (isLocallyBoundedBelow_smallEtaleDerivedModulePullback _
          (isEtale_chartToSpace B S hS X c.toChartDiagram.U) E hbdd)
    · have key := c.exists_ker_residuePoint_eq p
      obtain ⟨s, hs, hker⟩ := key
      have := (OpenAffineChartSquare.isField_siteObject (T := T) s).isDomain
      have := RingHom.ker_isPrime (c.residuePoint s hs).appTop.hom
      have := c.isAffine_U
      have := c.isAffine_residueFibreChart s hs
      have hN0 := exists_isZero_homology_chartToSpace_of_isLocallyBoundedBelow
        (residueFibre f s) _ (hfib s) (residueFibreChart f s c.U)
        (c.isAffine_residueFibreChart s hs)
      obtain ⟨N, hN⟩ := hN0
      have h1 := (forall_isZero_homology_residueFibreChart_iff f s c.U E hEq N).1 hN
      exact ⟨N,
        (CochainComplex.DerivedExtensionScalars.isGE_totalDerivedExtensionScalars_residueField_congr
          hker _ N).1
          ((c.isGE_representedAffineDerivedExtension_residueFibreChartFst_iff s hfl hs _ N).1 h1)⟩

/-- **Stacks 0GFK.** Let `f : X ⟶ T` be a morphism from an algebraic space to a scheme which is
flat and locally of finite presentation, and let `E ∈ D(𝒪_X)` be pseudo-coherent. Then `E` is
`T`-perfect exactly when `E` is locally bounded below and, for every point `s ∈ T`, the derived
pullback `L(X_s ⟶ X)^*E` to the fibre `X_s = X ×_T Spec κ(s)` is locally bounded below. -/
@[stacks 0GFK]
theorem isPerfectRelativeToCanonical_iff_isLocallyBoundedBelow (f : X ⟶ representedSpace T)
    (hfl : IsFlat B S hS f.hom) (hlfp : IsLocallyOfFinitePresentation B S hS f.hom)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherent E) :
    IsPerfectRelativeToCanonical.{u, u + 1, u + 1} B S hS f hfl hlfp E ↔
      IsLocallyBoundedBelow X E ∧ ∀ s : (BigFppfOver.toScheme B S hS).obj T,
        IsLocallyBoundedBelow (residueFibre f s)
          ((smallEtaleDerivedModulePullback B S hS (residueFibreι f s)).obj E) :=
  ⟨isLocallyBoundedBelow_of_isPerfectRelativeToCanonical f hfl hlfp E hE,
    fun ⟨hbdd, hfib⟩ =>
      isPerfectRelativeToCanonical_of_isLocallyBoundedBelow f hfl hlfp E hE hbdd hfib⟩

end AlgebraicGeometry.Space

end
