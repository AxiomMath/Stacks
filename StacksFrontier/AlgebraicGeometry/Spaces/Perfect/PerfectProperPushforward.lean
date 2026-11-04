module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineQuasicoherentDerivedPerfect
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentGenericFreeChart
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedPushforwardBoundedBelow
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.PerfectFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.SyntomicDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModuleExtensionByZeroExact
public import StacksFrontier.AlgebraicGeometry.Spaces.LiftDifferenceDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.Perfect
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ChartSlicePerfectness
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedPushforwardEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectPushforwardTorDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectBounded
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedPushforwardCoherentProperSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherent.CoherentCohomology
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentStalkLocalProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportClosedFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperClosedSubset
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyNoetherianFiniteType
public import StacksFrontier.Homology.PseudoCoherent.Coherent

/-!
# The derived direct image of a perfect object along a perfect proper morphism of spaces

Let `S` be a scheme, let `Y` be a Noetherian algebraic space over `S`, let `f : X ⟶ Y` be a
perfect proper morphism of algebraic spaces over `S`, and let `E` be a perfect object of
`D(𝒪_X)`.  Then `Rf_*E` is a perfect object of `D(𝒪_Y)` (Stacks 0E4U).

Perfectness on `Y` is read on the affine étale charts `V` of `Y`
(`AlgebraicGeometry.Space.isPerfect_of_forall_isAffineChart`).  Over such a chart the base change
`g : X ×_Y V ⟶ V` is again perfect (Stacks 06BZ is stable under flat base change) and proper,
the pullback of `E` is perfect, and the restriction of `Rf_*E` to `V` is `Rg_*` of that pullback
(Stacks 08GE).  So it suffices to treat an affine target `V = Spec R`, with `R` Noetherian.

There `Rg_*E` lies in `D_QCoh` (Stacks 08FA), so it is the associated object of the complex
`M = RΓ(V, Rg_*E)` of `R`-modules, and it suffices that `M` be perfect, which by Stacks 0658 is
pseudo-coherence together with finite Tor dimension:

* **pseudo-coherence**: `E` is bounded
  (`AlgebraicGeometry.Space.exists_isZero_homology_of_isPerfect`) with coherent cohomology sheaves
  (Stacks 08IK), whose supports are proper over `V` because `g` is; so `Rg_*E` has bounded
  coherent cohomology (Stacks 08GK), the cohomology modules of `M` are their modules of sections,
  which are finite over the Noetherian ring `R`;
* **finite Tor dimension**: this is
  `AlgebraicGeometry.Space.preservesFiniteTorDimensionSections_of_isPerfect`, the Tor-dimension
  half of Stacks 08EV, proved by the induction principle of Stacks 08GP from the affine case.

## Main results

* `AlgebraicGeometry.Space.isPerfect_derivedModulePushforward_of_isProper_of_isAffine`: the case
  of an affine target.
* `AlgebraicGeometry.Space.isPerfect_derivedModulePushforward_of_isProper`: **Stacks 0E4U.**

## Implementation notes

The source deduces Stacks 0E4U from Stacks 08IS, whose Tor-dimension condition is finite Tor
dimension of `E` over `f⁻¹𝒪_Y`, checked through Stacks 0DK7 and 069C.  Neither that predicate on
an algebraic space nor the projection formula behind Stacks 08IS is used here: the Tor-dimension
half is proved directly for perfect `E` over an affine base, by Mayer–Vietoris induction down to
a morphism of affine schemes, where it is Stacks 066K for the ring map of the perfect morphism.

`Rf_*` is `Stacks.DerivedFunctor.totalRightDerived` of the direct image of modules of Stacks 03LU,
which exists for every morphism of algebraic spaces.  The hypothesis `hZ`, that the big fppf site
contains the final scheme, is the one the library's notion of a Noetherian algebraic space
(Stacks 03EA, through absolute quasi-separatedness) is stated under.

## References

* [Stacks Project, Tag 0E4U](https://stacks.math.columbia.edu/tag/0E4U)
* [Stacks Project, Tag 08EV](https://stacks.math.columbia.edu/tag/08EV)
* [Stacks Project, Tag 08GK](https://stacks.math.columbia.edu/tag/08GK)
* [Stacks Project, Tag 08GP](https://stacks.math.columbia.edu/tag/08GP)
* [Stacks Project, Tag 0658](https://stacks.math.columbia.edu/tag/0658)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 5000] CategoryTheory.IsGrothendieckAbelian.enoughInjectives

attribute [local instance] isGrothendieckAbelian_modules

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] etaleModulePullback_additive preservesFiniteLimits_etaleModulePullback
  preservesFiniteColimits_etaleModulePullback

/-- Over a Noetherian ring, an object of finite Tor dimension with finite cohomology modules is
perfect (Stacks 066E and 0658). -/
theorem _root_.StacksDraft.Perfect.isPerfect_of_hasFiniteTorDimensionCanonical_of_moduleFinite
    {R : Type u} [CommRing R] [IsNoetherianRing R] (K : DerivedCategory (ModuleCat.{u} R))
    (hTor : StacksDraft.TorAmplitude.HasFiniteTorDimensionCanonical R K)
    (hfin : ∀ i : ℤ,
      Module.Finite R ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj K)) :
    StacksDraft.Perfect.IsPerfect K := by
  obtain ⟨a, b, hab⟩ :=
    (StacksDraft.TorAmplitude.hasFiniteTorDimensionCanonical_iff_exists_hasTorAmplitudeCanonical
      _ K).1 hTor
  obtain ⟨Fl, hflat, hGE, hLE, ⟨eFl⟩⟩ :=
    (StacksDraft.TorAmplitude.hasTorAmplitudeCanonical_iff_hasFlatRepresentative _ K a b).1 hab
  have hpc : StacksDraft.PseudoCoherence.IsPseudoCoherent K :=
    ((StacksDraft.PseudoCoherence.pseudoCoherent_iff_boundedAbove_finite_homology K 0 R).2.1).2
      ⟨⟨b, fun i hi => IsZero.of_iso (DerivedCategory.isZero_of_isLE _ b i hi)
        ((DerivedCategory.homologyFunctor _ i).mapIso eFl)⟩, hfin⟩
  exact (StacksDraft.Perfect.isPerfect_iff_pseudoCoherent_and_finiteTorDimension K).1.2
    ⟨hpc, a, b, Fl, hflat, hGE, hLE, ⟨eFl⟩⟩

/-- A coherent module on `X` has proper support along a proper morphism `f : X ⟶ Y`. -/
theorem hasProperSupport_of_isCoherent_of_isProper {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hflft : IsLocallyOfFiniteType B S hS f.hom) (hfProper : IsProper B S hS f.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : IsCoherent B S hS X.1 X.2 F) :
    HasProperSupport B S hS X.2 Y.2 f.hom hflft ((SheafOfModules.toSheaf _).obj F) := by
  have := hF.toIsCoherentOnSite
  have := isFiniteTypeOnSite_of_isCoherentOnSite B S hS X F
  have hcl := isClosed_supportOfSheaf_of_isFiniteTypeOnSite B S hS X.1 X.2 F
  exact ⟨hcl, isProper_comp B S hS
    (isAlgebraicSpace_reducedClosedSubspace B S hS X.1 X.2 _ hcl) X.2 Y.2 _ f.hom
    (isProper_ι_reducedClosedSubspace B S hS X.1 X.2 _ hcl) hfProper⟩

/-- Over an affine object `U`, the derived sections of a quasi-coherent object with coherent
cohomology sheaves have finite cohomology modules. -/
theorem moduleFinite_homology_representedAffineDerivedSections (U : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
    (K : DerivedCategory (Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)))
    (hKq : QcohDerived B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ K)
    (hK : ∀ i : ℤ, IsCoherent B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)
      ((DerivedCategory.homologyFunctor _ i).obj K)) (i : ℤ) :
    Module.Finite Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))
        i).obj ((representedAffineDerivedSections B S hS U).obj K)) := by
  have := moduleFinite_representedAffineSections B S hS U _ (hKq i)
    (representedAffineFinalChart B S hS U)
    (isTerminalChartOfIso (B := B) (S := S) (hS := hS) U (Iso.refl _))
    (isAffineChart_representedAffineFinalChart B S hS U)
    (moduleFinite_sections_of_isCoherent B S hS _ _ _ (hK i)
      (isAffineChart_representedAffineFinalChart B S hS U))
  exact Module.Finite.equiv
    (representedAffineDerivedSectionsHomologyIso B S hS U K hKq i).symm.toLinearEquiv

/-- Over an affine object `U`, the derived sections of `Rf_*E` have finite Tor dimension for `f`
perfect with qcqs source and `E` perfect. -/
theorem hasFiniteTorDimensionCanonical_representedAffineDerivedSections_of_isPerfect
    (hZ : B.Contains (⊤_ Scheme.{u})) (U : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U)] {X : AlgebraicSpaces B S hS}
    (f : X ⟶ (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS))
    (hfPerfect : IsPerfect B S hS f.hom) (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect E) :
    letI := additive_modulePushforward B S hS f
    StacksDraft.TorAmplitude.HasFiniteTorDimensionCanonical
      Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
      ((representedAffineDerivedSections B S hS U).obj
        ((Stacks.DerivedFunctor.totalRightDerived (modulePushforward B S hS f)).obj E)) := by
  let := additive_modulePushforward B S hS f
  obtain ⟨I, hI, ⟨eI⟩⟩ := exists_isKInjective_iso_modules B S hS E
  obtain ⟨e'⟩ := nonempty_rightDerived_obj_iso_of_isKInjective B S hS f
    (Stacks.DerivedFunctor.totalRightDerived (modulePushforward B S hS f))
    (Functor.totalRightDerivedUnit _ _ _) I hI
  exact StacksDraft.TorAmplitude.hasFiniteTorDimensionCanonical_of_iso
    ((representedAffineDerivedSections B S hS U).mapIso
      (e'.symm ≪≫ (Stacks.DerivedFunctor.totalRightDerived
        (modulePushforward B S hS f)).mapIso eI.symm))
    (preservesFiniteTorDimensionSections_of_isPerfect B S hS U hZ f hfPerfect hXqc hXqs I hI
      (RingedSite.IsPerfect.of_iso _ hE eI))

/-- On a Noetherian algebraic space, a perfect object of `D(𝒪_X)` lies in `D^b_{Coh}`. -/
theorem derivedCategoryBBounded_isCoherent_of_isPerfect (hZ : B.Contains (⊤_ Scheme.{u}))
    {X : AlgebraicSpaces B S hS} (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXN : IsNoetherian B S hS hZ X.1) (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect E) :
    DerivedCategoryB.derivedCategoryBBounded (isCoherent.{u, u} B S hS X.1 X.2) E := by
  obtain ⟨a', b', hbd⟩ := exists_isZero_homology_of_isPerfect B S hS X hXqc E hE
  exact ⟨⟨⟨a', fun n hn => hbd n (Or.inl hn)⟩, ⟨b', fun n hn => hbd n (Or.inr hn)⟩⟩, fun i =>
    { toIsQuasicoherentOnSite := qcohDerived_of_isPerfect B S hS X E hE i
      toIsCoherentOnSite := isCoherentOnSite_homology_of_isPseudoCoherent_of_isNoetherian
        B S hS X.1 X.2 hZ hXN E (RingedSite.isPseudoCoherent_of_isPerfect_general _ hE) i }⟩

/-- **The affine case of Stacks 0E4U.**  Let `U` be an object of the big fppf site whose
underlying scheme is affine and locally Noetherian, let `f : X ⟶ yoneda.obj U` be a perfect proper
morphism of algebraic spaces and `E` a perfect object of `D(𝒪_X)`.  Then `Rf_*E` is perfect:
`RΓ(U, Rf_*E)` is pseudo-coherent (Stacks 08GK) and of finite Tor dimension, hence perfect
(Stacks 0658), and `Rf_*E` is its associated object. -/
theorem isPerfect_derivedModulePushforward_of_isProper_of_isAffine
    (hZ : B.Contains (⊤_ Scheme.{u})) (U : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
    (hU : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj U))
    {X : AlgebraicSpaces B S hS}
    (f : X ⟶ (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS))
    (hfPerfect : IsPerfect B S hS f.hom) (hfProper : IsProper B S hS f.hom)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect E) :
    letI := additive_modulePushforward B S hS f
    (smallEtaleRingedSite B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)).IsPerfect
      ((Stacks.DerivedFunctor.totalRightDerived (modulePushforward B S hS f)).obj E) := by
  let := additive_modulePushforward B S hS f
  let Y : AlgebraicSpaces B S hS := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩
  have : IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩
  have hYaff : IsAffineSpace B S hS Y.1 := isAffineSpace_yoneda B S hS U inferInstance
  have hYqc : IsQuasiCompactSpace B S hS Y.1 :=
    isQuasiCompactSpace_yoneda_of_isAffine B S hS U inferInstance
  have hfqc : IsQuasiCompact B S hS f.hom := hfProper.2.1.2
  have hfqs : IsQuasiSeparated B S hS f.hom := isQuasiSeparated_of_isSeparated B S hS hfProper.1
  have hflft : IsLocallyOfFiniteType B S hS f.hom := hfProper.2.1.1
  have hXqc : IsQuasiCompactSpace B S hS X.1 :=
    isQuasiCompactSpace_of_isQuasiCompact B S hS Y.2 hYqc f.hom hfqc
  have hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1 :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated_hom_of_isAffineSpace B S hS hZ f hfqs hYaff
  have hYN : HasEtaleLocalProperty B S hS Y.1 (fun T : Scheme.{u} => IsLocallyNoetherian T) :=
    hasEtaleLocalProperty_of_representable B S hS _ _ U (Iso.refl _) hU
  have hXN : IsNoetherian B S hS hZ X.1 :=
    ⟨hXqc, hXqs, isLocallyNoetherian_of_isLocallyOfFiniteType B S hS X.2 Y.2 f.hom hflft hYN⟩
  set K := (Stacks.DerivedFunctor.totalRightDerived (modulePushforward B S hS f)).obj E
  have hKq : QcohDerived B S hS Y K :=
    qcohDerived_rightDerived_obj B S hS f hfqc hfqs _ (Functor.totalRightDerivedUnit _ _ _) E
      (qcohDerived_of_isPerfect B S hS X E hE)
  have hEb := derivedCategoryBBounded_isCoherent_of_isPerfect B S hS hZ hXqc hXN E hE
  have hKb := derivedCategoryBBounded_derivedModulePushforward_of_hasProperSupport B S hS hZ f
    hflft ⟨hYqc, isAbsolutelyQuasiSeparated_of_isAffineSpace B S hS hZ hYaff, hYN⟩ E hEb
    fun i => hasProperSupport_of_isCoherent_of_isProper B S hS f hflft hfProper _ (hEb.2 i)
  have := isIso_representedAffineDerivedAdjunction_counit_app B S hS U K hKq
  exact RingedSite.IsPerfect.of_iso _
    (isPerfect_representedAffineDerivedAssociated_obj B S hS U _
      (StacksDraft.Perfect.isPerfect_of_hasFiniteTorDimensionCanonical_of_moduleFinite _
        (hasFiniteTorDimensionCanonical_representedAffineDerivedSections_of_isPerfect
          B S hS hZ U f hfPerfect hXqc hXqs E hE)
        (moduleFinite_homology_representedAffineDerivedSections B S hS U K hKq hKb.2)))
    (asIso ((representedAffineDerivedAdjunction B S hS U).counit.app K))

/-- **Stacks 0E4U.**  Let `S` be a scheme, let `Y` be a Noetherian algebraic space over `S`, let
`f : X ⟶ Y` be a perfect proper morphism of algebraic spaces over `S`, and let `E` be a perfect
object of `D(𝒪_X)`.  Then `Rf_*E` is a perfect object of `D(𝒪_Y)`.

Perfectness is tested on the affine étale charts of `Y`, over which the restriction of `Rf_*E` is
the derived direct image along the base change of `f` (Stacks 08GE), and the affine case is
`AlgebraicGeometry.Space.isPerfect_derivedModulePushforward_of_isProper_of_isAffine`. -/
@[stacks 0E4U]
theorem isPerfect_derivedModulePushforward_of_isProper
    (hZ : B.Contains (⊤_ Scheme.{u})) {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hY : IsNoetherian B S hS hZ Y.1) (hfPerfect : IsPerfect B S hS f.hom)
    (hfProper : IsProper B S hS f.hom)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect E) :
    (smallEtaleRingedSite B S hS Y.1 Y.2).IsPerfect
      ((Stacks.DerivedFunctor.totalRightDerived (modulePushforward B S hS f)).obj E) := by
  refine isPerfect_of_forall_isAffineChart B S hS Y _ fun V hV => ?_
  let i := chartBaseChangeInclusion B S hS f V
  let g : chartBaseChangeSpace B S hS f V ⟶ chartSpace B S hS Y V :=
    chartBaseChangeProjection B S hS f V
  have sq : IsPullback i g f (chartToSpace B S hS Y V) :=
    isPullback_chartBaseChangeInclusion B S hS f V
  have hc : IsEtale B S hS (chartToSpace B S hS Y V).hom := isEtale_chartToSpace B S hS Y V
  have hi : IsEtale B S hS i.hom := isEtale_chartBaseChangeInclusion B S hS f V
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y.1).obj V)) := hV
  have hg := isPerfect_derivedModulePushforward_of_isProper_of_isAffine B S hS hZ
    ((SmallEtale.toOver B S hS Y.1).obj V) (isLocallyNoetherian_chartScheme B S hS Y hY.2.2 V) g
    (isPerfect_of_isPullback_of_isFlat B S hS inferInstance sq (isFlat_of_isEtale B S hS hc)
      hfPerfect)
    ((isProper_isStableUnderBaseChange B S hS).of_isPullback sq hfProper) _
    (isPerfect_etaleModulePullback B S hS X i hi E hE)
  refine RingedSite.IsPerfect.of_iso _ hg ?_
  let Pc := etaleModulePullback.{u, u} B S hS (chartToSpace B S hS Y V) hc
  let Pi := etaleModulePullback.{u, u} B S hS i hi
  have hRc := Functor.isRightDerivedFunctor_of_inverts
    (HomotopyCategory.quasiIso (Modules.{u, u} B S hS Y.1 Y.2) (ComplexShape.up ℤ))
    Pc.mapDerivedCategory Pc.mapDerivedCategoryFactorsh
  have hRi := Functor.isRightDerivedFunctor_of_inverts
    (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ))
    Pi.mapDerivedCategory Pi.mapDerivedCategoryFactorsh
  exact ((derivedModulePushforwardEtaleRestrictIso B S hS sq hc
      (etaleModuleLowerShriekAdjunction B S hS i hi)
      (Stacks.DerivedFunctor.totalRightDerived (modulePushforward B S hS f))
      (Stacks.DerivedFunctor.totalRightDerived (modulePushforward B S hS g))
      Pi.mapDerivedCategory Pc.mapDerivedCategory
      (Functor.totalRightDerivedUnit _ _ _) (Functor.totalRightDerivedUnit _ _ _)
      Pi.mapDerivedCategoryFactorsh.inv Pc.mapDerivedCategoryFactorsh.inv).app E).symm ≪≫
    (Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso _ _
      (etaleModulePullbackChartToSpaceNatIso B S hS Y V)).app _ ≪≫
    (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso _ _).app _

end AlgebraicGeometry.Space
