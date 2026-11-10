module

public import
StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.ExtensionByZeroBaseChangeComparison
public import
  StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RelativeDescentHomDescentZariski
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RepresentedDerivedPullbackComparisonFac
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedDerivedPullbackQuasicoherent
public import StacksFrontier.CategoryTheory.Localization.ExactDerivedComparison

/-!
# The comparison of the derived pullbacks of the Zariski and the small étale sites

For a morphism `g : T' ⟶ T` of the big fppf site, with underlying morphism of schemes `r` and
represented morphism of algebraic spaces `h_g`, the associated-module functor `ε^*` of Stacks
03DU (4) intertwines the derived pullbacks: `L(h_g)^* ∘ ε_T^* ≅ ε_{T'}^* ∘ Lr^*`
(`AlgebraicGeometry.Space.representedDerivedPullbackComparisonIso`), induced by the underived
identification `h_g^* ∘ ε_T^* ≅ ε_{T'}^* ∘ r^*` of Stacks 03LC (1).

These identifications are compatible with the composition isomorphisms of Stacks 0D6D on the
small étale sites and of Stacks 0D5S on the Zariski sites, as soon as the underived
identifications are compatible with the underived compositors on the homotopy categories, the
proposition `AlgebraicGeometry.Space.RepresentedHomotopyPullbackCoherence`. Given it, they form
the datum `AlgebraicGeometry.Space.RepresentedDerivedPullbackComparison` for every
pseudofunctoriality datum whose identifications are characterized on complexes in the canonical
way, in particular for `AlgebraicGeometry.Space.DerivedPullbackComposition.canonical`.

## Main definitions

* `AlgebraicGeometry.Space.representedDerivedPullbackComparisonIso`:
  `ε_T^* ⋙ L(h_g)^* ≅ Lr^* ⋙ ε_{T'}^*`.
* `AlgebraicGeometry.Space.RepresentedHomotopyPullbackCoherence`: the compatibility of the
  underived identifications with the underived compositors.
* `AlgebraicGeometry.Space.representedDerivedPullbackComparisonOfCoherence`,
  `AlgebraicGeometry.Space.representedDerivedPullbackComparisonCanonical`: the datum
  `AlgebraicGeometry.Space.RepresentedDerivedPullbackComparison`.

## Main results

* `AlgebraicGeometry.Space.representedDerivedPullbackComparisonIso_comp`: the identifications
  `ε^* ⋙ L(h_g)^* ≅ Lr^* ⋙ ε^*` are compatible with composition.

## References

* [Stacks Project, Tag 0DKV](https://stacks.math.columbia.edu/tag/0DKV)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03LC](https://stacks.math.columbia.edu/tag/03LC)
* [Stacks Project, Tag 0G7E](https://stacks.math.columbia.edu/tag/0G7E)
* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits

attribute [local instance 6000] preadditive_smallEtaleModules_model

attribute [local instance]
  _root_.AlgebraicGeometry.SmallEtale.preservesFiniteLimits_associatedModule

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The functors on modules -/

/-- `ε^* : Mod(𝒪_T) ⥤ Mod(𝒪_{h_T})`, the functor
`AlgebraicGeometry.Space.representedAssociatedModule`. -/
abbrev zariskiRepresentedAssociatedModule (T : BigFppfOver B S hS) :
    SheafOfModules.{u} (structureSheafRing ((BigFppfOver.toScheme B S hS).obj T).toRingedSpace) ⥤
      SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
        ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩) :=
  representedAssociatedModule B S hS T (isAlgebraicSpace_yoneda B S hS T)

/-- `AlgebraicGeometry.Space.zariskiRepresentedAssociatedModule` is additive. -/
instance additive_zariskiRepresentedAssociatedModule (T : BigFppfOver B S hS) :
    (zariskiRepresentedAssociatedModule B S hS T).Additive :=
  additive_representedAssociatedModule B S hS T (isAlgebraicSpace_yoneda B S hS T)

/-- The inverse image of modules along the morphism of ringed spaces underlying a morphism of the
big fppf site. -/
abbrev zariskiModulePullback {T' T : BigFppfOver B S hS} (g : T' ⟶ T) :
    SheafOfModules.{u} (structureSheafRing ((BigFppfOver.toScheme B S hS).obj T).toRingedSpace) ⥤
      SheafOfModules.{u}
        (structureSheafRing ((BigFppfOver.toScheme B S hS).obj T').toRingedSpace) :=
  RingedSpaceModuleAdjunction.modulePullback ((BigFppfOver.toScheme B S hS).map g).toLRSHom.toShHom

/-- `AlgebraicGeometry.Space.zariskiModulePullback` is additive. -/
instance additive_zariskiModulePullback {T' T : BigFppfOver B S hS} (g : T' ⟶ T) :
    (zariskiModulePullback B S hS g).Additive :=
  RingedSpaceModuleAdjunction.modulePullback_additive _

/-- The pullback of modules along the morphism of small étale ringed topoi of a represented
morphism. -/
abbrev representedPullbackModules {T' T : BigFppfOver B S hS} (g : T' ⟶ T) :
    SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
        ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩) ⥤
      SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
        ⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩) :=
  (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS g)).toModulesHom.pullbackModules

/-- `AlgebraicGeometry.Space.representedPullbackModules` is additive. -/
instance additive_representedPullbackModules {T' T : BigFppfOver B S hS} (g : T' ⟶ T) :
    (representedPullbackModules B S hS g).Additive :=
  pullbackModules_smallEtaleRingedToposHom_additive B S hS (representedSpaceMap B S hS g)

/-! ### The functor `ε^*` on homotopy categories -/

/-- `ε^*` on the unbounded homotopy categories, degreewise. -/
abbrev representedAssociatedModuleHomotopy (T : BigFppfOver B S hS) :
    HomotopyCategory (SheafOfModules.{u}
      (structureSheafRing ((BigFppfOver.toScheme B S hS).obj T).toRingedSpace))
        (ComplexShape.up ℤ) ⥤
      HomotopyCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
        ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩)) (ComplexShape.up ℤ) :=
  (zariskiRepresentedAssociatedModule B S hS T).mapHomotopyCategory (ComplexShape.up ℤ)

/-- `ε^* : D(𝒪_T) ⥤ D(𝒪_{h_T})` is induced by `ε^*` on homotopy categories. -/
def zariskiEtaleDerivedFactors (T : BigFppfOver B S hS) :
    DerivedCategory.Qh ⋙ zariskiEtaleDerived B S hS T ≅
      representedAssociatedModuleHomotopy B S hS T ⋙ DerivedCategory.Qh :=
  (representedAssociatedModule B S hS T
    (isAlgebraicSpace_yoneda B S hS T)).mapDerivedCategoryFactorsh

/-! ### The underived identification -/

variable {B S hS}

/-- **`h_g^* ∘ ε_T^* ≅ ε_{T'}^* ∘ r^*` on modules** (Stacks 03LC (1)). -/
def representedAssociatedModulePullbackModulesIso {T' T : BigFppfOver B S hS} (g : T' ⟶ T) :
    zariskiRepresentedAssociatedModule B S hS T ⋙ representedPullbackModules B S hS g ≅
      zariskiModulePullback B S hS g ⋙ zariskiRepresentedAssociatedModule B S hS T' :=
  Functor.isoWhiskerLeft (representedAssociatedModule B S hS T (isAlgebraicSpace_yoneda B S hS T))
      (eqToIso (pullbackModules_eq_modulePullback B S hS (representedSpaceMap B S hS g))) ≪≫
    representedAssociatedModulePullbackFunctorIso B S hS g ≪≫
    Functor.isoWhiskerRight
      (Stacks.ProjectiveBundleQuotients.pullbackIso ((BigFppfOver.toScheme B S hS).map g))
      (representedAssociatedModule B S hS T' (isAlgebraicSpace_yoneda B S hS T'))

/-- `AlgebraicGeometry.Space.representedAssociatedModulePullbackModulesIso` on the unbounded
homotopy categories. -/
def representedAssociatedModulePullbackHomotopyIso {T' T : BigFppfOver B S hS} (g : T' ⟶ T) :
    representedAssociatedModuleHomotopy B S hS T ⋙
        smallEtaleModulePullbackMapHomotopy (representedSpaceMap B S hS g) ≅
      schemeModulePullbackHomotopy ((BigFppfOver.toScheme B S hS).map g) ⋙
        representedAssociatedModuleHomotopy B S hS T' :=
  Functor.mapHomotopyCategoryCompIso (Iso.refl _) (ComplexShape.up ℤ) ≪≫
    Stacks.Homology.mapHomotopyCategoryIso (representedAssociatedModulePullbackModulesIso g)
      (ComplexShape.up ℤ) ≪≫
    (Functor.mapHomotopyCategoryCompIso (Iso.refl _) (ComplexShape.up ℤ)).symm

/-! ### The resolving class -/

variable (B S hS) in
/-- The K-flat complexes with flat terms of `𝒪_T`-modules on the Zariski site, as a property of
objects of the unbounded homotopy category. -/
def zariskiKFlatFlatComplexes (T : BigFppfOver B S hS) :
    ObjectProperty (HomotopyCategory (SheafOfModules.{u}
      (structureSheafRing ((BigFppfOver.toScheme B S hS).obj T).toRingedSpace))
        (ComplexShape.up ℤ)) :=
  fun M ↦ Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex
      ((BigFppfOver.toScheme B S hS).obj T).toRingedSpace M.as ∧
    ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      (O := ((BigFppfOver.toScheme B S hS).obj T).toRingedSpace.sheaf) (M.as.X i)

/-- K-flat complexes with flat terms resolve every complex (Stacks 06YF). -/
theorem zariskiKFlatFlatComplexes_resolves (T : BigFppfOver B S hS)
    (M : HomotopyCategory (SheafOfModules.{u}
      (structureSheafRing ((BigFppfOver.toScheme B S hS).obj T).toRingedSpace))
        (ComplexShape.up ℤ)) :
    ∃ (N : HomotopyCategory (SheafOfModules.{u}
      (structureSheafRing ((BigFppfOver.toScheme B S hS).obj T).toRingedSpace))
        (ComplexShape.up ℤ)) (_ : zariskiKFlatFlatComplexes B S hS T N) (s : N ⟶ M),
      HomotopyCategory.quasiIso _ _ s := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective M
  obtain ⟨N, s, hN, hNf, hs, -⟩ :=
    Stacks.Cohomology.KFlatDerivedPullback.exists_kFlatResolution
      ((BigFppfOver.toScheme B S hS).obj T).toRingedSpace K
  exact ⟨(HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj N, ⟨hN, hNf⟩,
    (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map s,
    (HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 hs⟩

/-- Degreewise pullback along `r` inverts the quasi-isomorphisms between K-flat complexes with
flat terms. -/
theorem zariskiKFlatFlatComplexes_inverts {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
    {M N : HomotopyCategory (SheafOfModules.{u}
      (structureSheafRing ((BigFppfOver.toScheme B S hS).obj T).toRingedSpace))
        (ComplexShape.up ℤ)} (s : M ⟶ N) (hs : HomotopyCategory.quasiIso _ _ s)
    (hM : zariskiKFlatFlatComplexes B S hS T M) (hN : zariskiKFlatFlatComplexes B S hS T N) :
    IsIso ((schemeModulePullbackHomotopy ((BigFppfOver.toScheme B S hS).map g) ⋙
      DerivedCategory.Qh).map s) :=
  Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.pullbackInvertsQuasiIso_isKFlat
    ((BigFppfOver.toScheme B S hS).map g).toLRSHom.toShHom s hs hM.1 hN.1

/-- The comparison of `L(h_g)^*` with degreewise pullback is invertible at `ε^*` of a K-flat
complex with flat terms. -/
theorem isIso_smallEtaleDerivedModulePullbackComparison_representedAssociatedModuleHomotopy
    {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
    (M : HomotopyCategory (SheafOfModules.{u}
      (structureSheafRing ((BigFppfOver.toScheme B S hS).obj T).toRingedSpace))
        (ComplexShape.up ℤ)) (hM : zariskiKFlatFlatComplexes B S hS T M) :
    IsIso ((smallEtaleDerivedModulePullbackComparison' (representedSpaceMap B S hS g)).app
      ((representedAssociatedModuleHomotopy B S hS T).obj M)) := by
  have hres : Stacks.Cohomology.DerivedPullbackOfToposHom.HasResolutions
      (Y := smallEtaleRingedTopos B S hS ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩)
      (Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat
        (Y := smallEtaleRingedTopos B S hS ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩)) :=
    fun N ↦ by
      obtain ⟨K, hK, t, ht⟩ :=
        Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.hasResolutions_isKFlat
          (Y := smallEtaleRingedTopos B S hS ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩) N
      exact ⟨K, hK, t, ht⟩
  have hK := isKFlat_representedAssociatedModule B S hS T M.as ⟨hM.1, hM.2⟩
  exact Stacks.Cohomology.DerivedPullbackOfToposHom.isIso_derivedPullbackComparison_app
    (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS g)) _ hres
    (Stacks.Cohomology.DerivedPullbackOfToposHom.pullbackInvertsQuasiIso_isKFlat
      (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS g))) _ hK

/-- `Lr^* ⋙ ε_{T'}^*` is a left derived functor of degreewise pullback followed by `ε_{T'}^*`. -/
theorem isLeftDerivedFunctor_derivedPullback_comp_zariskiEtaleDerived
    {T' T : BigFppfOver B S hS} (g : T' ⟶ T) :
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        ((BigFppfOver.toScheme B S hS).map g).toLRSHom.toShHom ⋙
      zariskiEtaleDerived B S hS T').IsLeftDerivedFunctor
      ((Functor.associator DerivedCategory.Qh
          (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
            ((BigFppfOver.toScheme B S hS).map g).toLRSHom.toShHom)
          (zariskiEtaleDerived B S hS T')).inv ≫
        Functor.whiskerRight
          (schemeDerivedPullbackComparison ((BigFppfOver.toScheme B S hS).map g))
          (zariskiEtaleDerived B S hS T'))
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) :=
  Functor.isLeftDerivedFunctor_comp_of_inverts_on_resolutions
    (schemeDerivedPullbackComparison ((BigFppfOver.toScheme B S hS).map g))
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) (zariskiKFlatFlatComplexes B S hS T)
    (zariskiKFlatFlatComplexes_resolves T) (zariskiKFlatFlatComplexes_inverts g)

/-! ### The derived identification -/

/-- **`ε_T^* ⋙ L(h_g)^* ⟶ Lr^* ⋙ ε_{T'}^*`**, induced by the underived identification. -/
def representedDerivedPullbackComparisonHom {T' T : BigFppfOver B S hS} (g : T' ⟶ T) :
    zariskiEtaleDerived B S hS T ⋙
        smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g) ⟶
      Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          ((BigFppfOver.toScheme B S hS).map g).toLRSHom.toShHom ⋙
        zariskiEtaleDerived B S hS T' :=
  haveI := isLeftDerivedFunctor_derivedPullback_comp_zariskiEtaleDerived g
  Functor.exactDerivedComparison (zariskiEtaleDerivedFactors B S hS T)
    (zariskiEtaleDerivedFactors B S hS T')
    (schemeDerivedPullbackComparison ((BigFppfOver.toScheme B S hS).map g))
    (smallEtaleDerivedModulePullbackComparison' (representedSpaceMap B S hS g))
    (representedAssociatedModulePullbackHomotopyIso g)
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))

/-- The characterization of `AlgebraicGeometry.Space.representedDerivedPullbackComparisonHom` on
complexes. -/
theorem representedDerivedPullbackComparisonHom_app_fac {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
    (M : HomotopyCategory (SheafOfModules.{u}
      (structureSheafRing ((BigFppfOver.toScheme B S hS).obj T).toRingedSpace))
        (ComplexShape.up ℤ)) :
    (representedDerivedPullbackComparisonHom g).app (DerivedCategory.Qh.obj M) ≫
        (zariskiEtaleDerived B S hS T').map
          ((schemeDerivedPullbackComparison ((BigFppfOver.toScheme B S hS).map g)).app M) =
      (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g)).map
          ((zariskiEtaleDerivedFactors B S hS T).hom.app M) ≫
        (smallEtaleDerivedModulePullbackComparison' (representedSpaceMap B S hS g)).app
          ((representedAssociatedModuleHomotopy B S hS T).obj M) ≫
        DerivedCategory.Qh.map ((representedAssociatedModulePullbackHomotopyIso g).hom.app M) ≫
        (zariskiEtaleDerivedFactors B S hS T').inv.app
          ((schemeModulePullbackHomotopy ((BigFppfOver.toScheme B S hS).map g)).obj M) :=
  have := isLeftDerivedFunctor_derivedPullback_comp_zariskiEtaleDerived g
  Functor.exactDerivedComparison_app_fac _ _ _ _ _ _ M

/-- `AlgebraicGeometry.Space.representedDerivedPullbackComparisonHom` is invertible. -/
theorem isIso_representedDerivedPullbackComparisonHom {T' T : BigFppfOver B S hS} (g : T' ⟶ T) :
    IsIso (representedDerivedPullbackComparisonHom g) :=
  have := isLeftDerivedFunctor_derivedPullback_comp_zariskiEtaleDerived g
  Functor.isIso_exactDerivedComparison _ _ _ _ _ _ (zariskiKFlatFlatComplexes B S hS T)
    (zariskiKFlatFlatComplexes_resolves T) (zariskiKFlatFlatComplexes_inverts g)
    (isIso_smallEtaleDerivedModulePullbackComparison_representedAssociatedModuleHomotopy g)

/-- **`ε^*` intertwines the derived pullbacks**: `ε_T^* ⋙ L(h_g)^* ≅ Lr^* ⋙ ε_{T'}^*` for a
morphism `g : T' ⟶ T` of the big fppf site with underlying morphism of schemes `r`. -/
def representedDerivedPullbackComparisonIso {T' T : BigFppfOver B S hS} (g : T' ⟶ T) :
    zariskiEtaleDerived B S hS T ⋙
        smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g) ≅
      Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          ((BigFppfOver.toScheme B S hS).map g).toLRSHom.toShHom ⋙
        zariskiEtaleDerived B S hS T' :=
  haveI := isIso_representedDerivedPullbackComparisonHom g
  asIso (representedDerivedPullbackComparisonHom g)

/-! ### Compatibility with composition -/

variable (B S hS) in
/-- **The underived identifications are compatible with the underived compositors.** For
`f : T'' ⟶ T'` and `g : T' ⟶ T` in the big fppf site, on the unbounded homotopy categories: the
compositor of the pullbacks along the represented morphisms (Stacks 03D6 and the 2-isomorphism of
Stacks 03G8, `AlgebraicGeometry.Space.smallEtalePullbackMapHomotopyFactorIso`) followed by the
identification `h_{f ≫ g}^* ∘ ε^* ≅ ε^* ∘ (f ≫ g)^*` is the identification for `g` pushed by
`h_f^*`, then the identification for `f`, then `ε^*` of the compositor of the inverse images of
modules on the Zariski sites (`AlgebraicGeometry.Space.schemeFactorMapHomotopyIso`). -/
def RepresentedHomotopyPullbackCoherence : Prop :=
  ∀ {T'' T' T : BigFppfOver B S hS} (f : T'' ⟶ T') (g : T' ⟶ T),
    Functor.UnderivedCompCoherence (representedAssociatedModulePullbackHomotopyIso g)
      (representedAssociatedModulePullbackHomotopyIso f)
      (representedAssociatedModulePullbackHomotopyIso (f ≫ g))
      (schemeFactorMapHomotopyIso ((BigFppfOver.toScheme B S hS).map f)
        ((BigFppfOver.toScheme B S hS).map g) ((BigFppfOver.toScheme B S hS).map (f ≫ g))
        (toScheme_map_comp_eq B S hS f g (f ≫ g) rfl)).hom
      (smallEtalePullbackMapHomotopyFactorIso (representedSpaceMap B S hS f)
        (representedSpaceMap B S hS g) (representedSpaceMap B S hS (f ≫ g))
        (representedSpaceMap_comp_eq B S hS f g (f ≫ g) rfl)).hom

/-- **The identifications `ε^* ⋙ L(h_g)^* ≅ Lr^* ⋙ ε^*` are compatible with composition**: with
the composition isomorphisms of a pseudofunctoriality datum `P` characterized on complexes in the
canonical way (`hP`) and with those of Stacks 0D5S on the
Zariski sites, given the underived compatibility
`AlgebraicGeometry.Space.RepresentedHomotopyPullbackCoherence`. -/
theorem representedDerivedPullbackComparisonIso_comp (P : DerivedPullbackComposition B S hS)
    (hP : ∀ {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z)
      (h : f ≫ g = k)
      (M : HomotopyCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z))
        (ComplexShape.up ℤ)),
      (P.iso f g k h).hom.app (DerivedCategory.Qh.obj M) ≫
          (smallEtaleDerivedModulePullbackComparison' k).app M =
        (smallEtaleDerivedModulePullback B S hS f).map
            ((smallEtaleDerivedModulePullbackComparison' g).app M) ≫
          (smallEtaleDerivedModulePullbackComparison' f).app
            ((smallEtaleModulePullbackMapHomotopy g).obj M) ≫
          DerivedCategory.Qh.map ((smallEtalePullbackMapHomotopyFactorIso f g k h).hom.app M))
    (hcoh : RepresentedHomotopyPullbackCoherence B S hS)
    {T'' T' T : BigFppfOver B S hS} (f : T'' ⟶ T') (g : T' ⟶ T) (k : T'' ⟶ T) (h : f ≫ g = k)
    (M : DerivedCategory (SheafOfModules.{u}
      (structureSheafRing ((BigFppfOver.toScheme B S hS).obj T).toRingedSpace))) :
    (P.iso (representedSpaceMap B S hS f)
        (representedSpaceMap B S hS g) (representedSpaceMap B S hS k)
        (representedSpaceMap_comp_eq B S hS f g k h)).hom.app
          ((zariskiEtaleDerived B S hS T).obj M) ≫
        (representedDerivedPullbackComparisonIso k).hom.app M =
      (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS f)).map
          ((representedDerivedPullbackComparisonIso g).hom.app M) ≫
        (representedDerivedPullbackComparisonIso f).hom.app
          ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
            ((BigFppfOver.toScheme B S hS).map g).toLRSHom.toShHom).obj M) ≫
        (zariskiEtaleDerived B S hS T'').map
          ((Stacks.DerivedPullback.schemeFactorIso ((BigFppfOver.toScheme B S hS).map f)
            ((BigFppfOver.toScheme B S hS).map g) ((BigFppfOver.toScheme B S hS).map k)
            (toScheme_map_comp_eq B S hS f g k h)).hom.app M) := by
  subst h
  have := isLeftDerivedFunctor_derivedPullback_comp_zariskiEtaleDerived (f ≫ g)
  exact Functor.exactDerivedComparison_comp (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
    (fun X ↦ schemeFactorIso_hom_app_fac ((BigFppfOver.toScheme B S hS).map f)
      ((BigFppfOver.toScheme B S hS).map g) ((BigFppfOver.toScheme B S hS).map (f ≫ g))
      (toScheme_map_comp_eq B S hS f g (f ≫ g) rfl) X)
    (fun X ↦ hP (representedSpaceMap B S hS f) (representedSpaceMap B S hS g)
      (representedSpaceMap B S hS (f ≫ g)) (representedSpaceMap_comp_eq B S hS f g (f ≫ g) rfl) X)
    (fun X ↦ representedDerivedPullbackComparisonHom_app_fac g X)
    (fun X ↦ representedDerivedPullbackComparisonHom_app_fac f X)
    (fun X ↦ representedDerivedPullbackComparisonHom_app_fac (f ≫ g) X)
    (hcoh f g) M

/-- **`ε^*` intertwines the derived pullbacks of the Zariski and the small étale sites,
coherently**, for a pseudofunctoriality datum characterized on complexes in the canonical way,
given the underived compatibility
`AlgebraicGeometry.Space.RepresentedHomotopyPullbackCoherence`. -/
def representedDerivedPullbackComparisonOfCoherence (P : DerivedPullbackComposition B S hS)
    (hP : ∀ {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z)
      (h : f ≫ g = k)
      (M : HomotopyCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z))
        (ComplexShape.up ℤ)),
      (P.iso f g k h).hom.app (DerivedCategory.Qh.obj M) ≫
          (smallEtaleDerivedModulePullbackComparison' k).app M =
        (smallEtaleDerivedModulePullback B S hS f).map
            ((smallEtaleDerivedModulePullbackComparison' g).app M) ≫
          (smallEtaleDerivedModulePullbackComparison' f).app
            ((smallEtaleModulePullbackMapHomotopy g).obj M) ≫
          DerivedCategory.Qh.map ((smallEtalePullbackMapHomotopyFactorIso f g k h).hom.app M))
    (hcoh : RepresentedHomotopyPullbackCoherence B S hS) :
    RepresentedDerivedPullbackComparison B S hS P where
  iso g := representedDerivedPullbackComparisonIso g
  iso_comp f g k h M := representedDerivedPullbackComparisonIso_comp P hP hcoh f g k h M

/-- **The datum `AlgebraicGeometry.Space.RepresentedDerivedPullbackComparison` for the canonical
pseudofunctoriality of the derived pullback** on the small étale topoi of algebraic spaces, given
the underived compatibility `AlgebraicGeometry.Space.RepresentedHomotopyPullbackCoherence`. -/
def representedDerivedPullbackComparisonCanonical
    (hcoh : RepresentedHomotopyPullbackCoherence B S hS) :
    RepresentedDerivedPullbackComparison B S hS (DerivedPullbackComposition.canonical B S hS) :=
  representedDerivedPullbackComparisonOfCoherence (DerivedPullbackComposition.canonical B S hS)
    (fun f g k h M ↦ canonical_iso_hom_app_comp f g k h M) hcoh

end AlgebraicGeometry.Space

end
