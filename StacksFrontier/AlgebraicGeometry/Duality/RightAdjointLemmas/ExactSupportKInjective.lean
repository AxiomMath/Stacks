module

public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportDerived
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.LeftTExactness

/-!
# K-injective complexes compute derived sheaf Hom with exact support

Let `i : Z ⟶ X` be a closed quotient morphism of ringed spaces, so that pushforward
`i_* : Mod(𝒪_Z) ⥤ Mod(𝒪_X)` is left adjoint to sheaf Hom with exact support
`ℰom(𝒪_Z, -) : Mod(𝒪_X) ⥤ Mod(𝒪_Z)`.  Pushforward along a closed quotient morphism is exact, so
the adjoint criterion of [Stacks, Tag 08BJ] applies: `ℰom(𝒪_Z, -)`, applied degreewise, carries
K-injective cochain complexes of `𝒪_X`-modules to K-injective cochain complexes of
`𝒪_Z`-modules.

Consequently the comparison map of the total right derived functor
`R ℰom(𝒪_Z, -) : D(𝒪_X) ⥤ D(𝒪_Z)` is invertible at a K-injective complex: such a complex
computes `R ℰom(𝒪_Z, -)` by applying `ℰom(𝒪_Z, -)` in each degree.

All names below live in the namespace
`RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces`.

## Main definitions

* `derivedSheafHomExactSupportCochainComparison` is the comparison map
  `ℰom(𝒪_Z, -) ⋙ Q ⟶ Q ⋙ R ℰom(𝒪_Z, -)` on cochain complexes, assembled from the
  homotopy-category comparison and the two canonical identifications of the localization
  functors.
* `derivedSheafHomExactSupportKInjectiveIso` is the resulting isomorphism
  `R ℰom(𝒪_Z, -)(Q I) ≅ Q (ℰom(𝒪_Z, I))` for `I` a K-injective cochain complex.

## Main results

* `isKInjective_sheafHomExactSupport` is the instantiation of [Stacks, Tag 08BJ]: sheaf Hom with
  exact support preserves K-injectivity degreewise.
* `isIso_derivedSheafHomExactSupportComparison_app`: the derived-functor comparison map is
  invertible at a K-injective complex.
* `derivedSheafHomExactSupportKInjectiveIso_inv` pins the isomorphism down by naming its
  inverse.
* `derivedSheafHomExactSupportKInjectiveIso_natural` is naturality of the isomorphism in the
  K-injective complex.

## Implementation notes

`DerivedCategory.Q` is not literally `HomotopyCategory.quotient _ _ ⋙ DerivedCategory.Qh`, and
`ℰom(𝒪_Z, -)` on the homotopy category is not literally the degreewise functor followed by the
quotient; the two gaps are bridged by `DerivedCategory.quotientCompQhIso` and
`CategoryTheory.Functor.mapHomotopyCategoryFactors`.  Rather than inserting those two
identifications at each use, they are whiskered onto the homotopy-category comparison once, in
`derivedSheafHomExactSupportCochainComparison`.  The isomorphism of a K-injective complex is
then the inverse of a single component of that natural transformation, so its characterisation
is the component formula and its naturality is naturality of a natural transformation.

Exactness of `i_*`, which is what [Stacks, Tag 08BJ] consumes, is finite-colimit preservation
from `preservesFiniteColimits_modulePushforward` together with finite-limit preservation, which
holds because `i_*` is a right adjoint by `modulePushforward_isRightAdjoint`.

## References

* [Stacks Project, Tag 08BJ](https://stacks.math.columbia.edu/tag/08BJ)
* [Stacks Project, Tag 0A75](https://stacks.math.columbia.edu/tag/0A75)
* [Stacks Project, Tag 0A76](https://stacks.math.columbia.edu/tag/0A76)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u

namespace RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces

variable (S : ClosedQuotientMorphismOfRingedSpaces.{u})

/-- **[Stacks, Tag 08BJ].** Sheaf Hom with exact support along a closed quotient morphism of
ringed spaces, applied degreewise, carries a K-injective cochain complex of `𝒪_X`-modules to a
K-injective cochain complex of `𝒪_Z`-modules: it is the right adjoint of the exact functor
`i_*`. -/
instance isKInjective_sheafHomExactSupport
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing S.X)) ℤ) [I.IsKInjective] :
    CochainComplex.IsKInjective
      ((S.sheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
  CochainComplex.isKInjective_mapHomologicalComplex_of_exact _ (modulePushforward S.i)
    S.modulePushforwardSheafHomExactSupportAdjunction I

/-- The comparison map from sheaf Hom with exact support to its right derived functor is
invertible at a K-injective complex. -/
instance isIso_derivedSheafHomExactSupportComparison_app
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing S.X)) ℤ) [I.IsKInjective] :
    IsIso (S.derivedSheafHomExactSupportComparison.app
      ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing S.X))
        (ComplexShape.up ℤ)).obj I)) :=
  Stacks.DerivedFunctor.isIso_totalRightDerivedUnit_app_of_isKInjective
    S.sheafHomExactSupport I

/-- The comparison map `ℰom(𝒪_Z, -) ⋙ Q ⟶ Q ⋙ R ℰom(𝒪_Z, -)` between the degreewise functor
followed by the localization and the localization followed by the right derived functor. -/
noncomputable def derivedSheafHomExactSupportCochainComparison :
    S.sheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ S.derivedSheafHomExactSupport :=
  Functor.whiskerLeft (S.sheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ))
      (DerivedCategory.quotientCompQhIso (SheafOfModules.{u} (structureSheafRing S.Z))).inv ≫
    Functor.whiskerRight
        (S.sheafHomExactSupport.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv
        DerivedCategory.Qh ≫
      Functor.whiskerLeft
          (HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing S.X))
            (ComplexShape.up ℤ))
          S.derivedSheafHomExactSupportComparison ≫
        Functor.whiskerRight
          (DerivedCategory.quotientCompQhIso (SheafOfModules.{u} (structureSheafRing S.X))).hom
          S.derivedSheafHomExactSupport

/-- The component of the cochain-level comparison map at a cochain complex, as the composite of
the homotopy-category comparison map with the two canonical identifications. -/
theorem derivedSheafHomExactSupportCochainComparison_app
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing S.X)) ℤ) :
    S.derivedSheafHomExactSupportCochainComparison.app I =
      (DerivedCategory.quotientCompQhIso (SheafOfModules.{u} (structureSheafRing S.Z))).inv.app
          ((S.sheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ≫
        DerivedCategory.Qh.map
            ((S.sheafHomExactSupport.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app I) ≫
          S.derivedSheafHomExactSupportComparison.app
              ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing S.X))
                (ComplexShape.up ℤ)).obj I) ≫
            S.derivedSheafHomExactSupport.map
              ((DerivedCategory.quotientCompQhIso
                (SheafOfModules.{u} (structureSheafRing S.X))).hom.app I) :=
  rfl

/-- The cochain-level comparison map is invertible at a K-injective complex: all four of its
factors are. -/
instance isIso_derivedSheafHomExactSupportCochainComparison_app
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing S.X)) ℤ) [I.IsKInjective] :
    IsIso (S.derivedSheafHomExactSupportCochainComparison.app I) := by
  rw [S.derivedSheafHomExactSupportCochainComparison_app I]
  infer_instance

/-- A K-injective complex computes `R ℰom(𝒪_Z, -)`: the right derived functor at the image of a
K-injective cochain complex `I` in the derived category is the image of `ℰom(𝒪_Z, I)`, the
degreewise sheaf Hom with exact support. -/
noncomputable def derivedSheafHomExactSupportKInjectiveIso
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing S.X)) ℤ) [I.IsKInjective] :
    S.derivedSheafHomExactSupport.obj (DerivedCategory.Q.obj I) ≅
      DerivedCategory.Q.obj
        ((S.sheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
  (asIso (S.derivedSheafHomExactSupportCochainComparison.app I)).symm

/-- The inverse of the isomorphism computing `R ℰom(𝒪_Z, -)` at a K-injective complex is the
component of the derived-functor comparison map, composed with the two canonical
identifications of the localization functors. -/
theorem derivedSheafHomExactSupportKInjectiveIso_inv
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing S.X)) ℤ) [I.IsKInjective] :
    (S.derivedSheafHomExactSupportKInjectiveIso I).inv =
      (DerivedCategory.quotientCompQhIso (SheafOfModules.{u} (structureSheafRing S.Z))).inv.app
          ((S.sheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ≫
        DerivedCategory.Qh.map
            ((S.sheafHomExactSupport.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app I) ≫
          S.derivedSheafHomExactSupportComparison.app
              ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing S.X))
                (ComplexShape.up ℤ)).obj I) ≫
            S.derivedSheafHomExactSupport.map
              ((DerivedCategory.quotientCompQhIso
                (SheafOfModules.{u} (structureSheafRing S.X))).hom.app I) :=
  S.derivedSheafHomExactSupportCochainComparison_app I

/-- The isomorphism computing `R ℰom(𝒪_Z, -)` at a K-injective complex is natural in that
complex. -/
theorem derivedSheafHomExactSupportKInjectiveIso_natural
    {I J : CochainComplex (SheafOfModules.{u} (structureSheafRing S.X)) ℤ}
    [I.IsKInjective] [J.IsKInjective] (f : I ⟶ J) :
    S.derivedSheafHomExactSupport.map (DerivedCategory.Q.map f) ≫
        (S.derivedSheafHomExactSupportKInjectiveIso J).hom =
      (S.derivedSheafHomExactSupportKInjectiveIso I).hom ≫
        DerivedCategory.Q.map
          ((S.sheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).map f) := by
  have h := S.derivedSheafHomExactSupportCochainComparison.naturality f
  simp only [Functor.comp_map] at h
  show _ ≫ inv (S.derivedSheafHomExactSupportCochainComparison.app J) =
    inv (S.derivedSheafHomExactSupportCochainComparison.app I) ≫ _
  rw [IsIso.comp_inv_eq, Category.assoc, h, IsIso.inv_hom_id_assoc]

end RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces

end
