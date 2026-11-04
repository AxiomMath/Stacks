module

public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfToSmallEtaleDerived
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedSquareTransComposition
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusComparisons
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusResolution

/-!
# Étale and fppf cohomology of an algebraic space

Let `T` be a big fppf site of algebraic spaces over a scheme `S`, `E` a big étale site of
algebraic spaces over the same big fppf site of schemes, and `X` an algebraic space, with
`a_X : Sh((Spaces/X)_fppf) ⟶ Sh(X_étale)` (Stacks 0DGI). This file proves Stacks 0DGH, granted
the scheme case of Stacks 0DDS (1) (`AlgebraicGeometry.SchemeFppfEtaleHigherVanishing`):

1. `H^q(X_étale, F) = H^q_fppf(X, a_X⁻¹F)` for an abelian sheaf `F` on `X_étale`;
2. `H^q(X_étale, K) = H^q_fppf(X, a_X⁻¹K)` for `K` in `D⁺(X_étale)`;

and for an abelian group `A`, `H^q_étale(X, A) = H^q_fppf(X, A)` for the constant sheaves.

## Main definitions

* `AlgebraicGeometry.BigFppfSpaceSite.etaleGlobalSections`,
  `AlgebraicGeometry.BigFppfSpaceSite.fppfGlobalSections`: sections over the final objects.
* `AlgebraicGeometry.BigFppfSpaceSite.fppfGlobalSectionsIso`: `Γ_fppf = Γ_étale ∘ a_{X,*}`.
* `AlgebraicGeometry.BigFppfSpaceSite.derivedGlobalSectionsIso_of`: `RΓ_étale = RΓ_fppf ∘ a_X⁻¹`
  on `D⁺(X_étale)`, granted the scheme case.

## Main results

* `AlgebraicGeometry.BigFppfSpaceSite.etaleCohomologyIso_of`,
  `AlgebraicGeometry.BigFppfSpaceSite.etaleCohomologyDerivedIso_of`,
  `AlgebraicGeometry.BigFppfSpaceSite.etaleCohomologyConstantIso_of`: the two parts of Stacks 0DGH
  and its example, granted the scheme case.

## Implementation notes

As in Stacks 08J6, `Γ_fppf = Γ_étale ∘ a_{X,*}` and `a_{X,*}` carries injective sheaves to
injective sheaves, being right adjoint to the exact `a_X⁻¹`; so
`RΓ_fppf = RΓ_étale ∘ Ra_{X,*}`
(`CategoryTheory.Functor.rightDerivedFunctorPlusCompIsoOfRightAcyclic`), and Stacks 0DGG,
`K ≅ Ra_{X,*}a_X⁻¹K`, finishes. The constant sheaves correspond because `a_X⁻¹` of a constant
sheaf and the constant sheaf are both left adjoint to `Γ_fppf`.

## References

* [Stacks Project, Tag 0DGH](https://stacks.math.columbia.edu/tag/0DGH)
* [Stacks Project, Tag 08J6](https://stacks.math.columbia.edu/tag/08J6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.BigFppfSpaceSite

attribute [local instance 2000]
  HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {S : Scheme.{u}} (T : BigFppfSpaceSite S) (E : BigEtaleSpaceSite S)
  (h : T.schemeSite = E.fppfSite) (X : T.Spaces)

/-- Global sections on the small étale site of `X`: sections over its final object. -/
abbrev etaleGlobalSections :
    Sheaf (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem (etaleSpace T E h X))
        AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1} :=
  (sheafSections _ AddCommGrpCat.{u + 1}).obj
    (op (Space.SpacesEtale.final E.fppfSite S E.fppf_mem (etaleSpace T E h X)))

/-- Global sections on the big fppf site of `X`: sections over its final object `X ⟶ X`. -/
abbrev fppfGlobalSections :
    Sheaf (BigFppfSpaceOver.topology T X) AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1} :=
  (sheafSections _ AddCommGrpCat.{u + 1}).obj (op (Over.mk (𝟙 X)))

/-- The final object of the small étale site of `X`, carried into the big fppf slice at `X`, is
final there. -/
def finalImageIsTerminal :
    IsTerminal ((Over.postEquiv (canonicalSpaceEquivalence T E h).1 (X := X)).inverse.obj
      ((Space.SpacesEtale.inclusion E.fppfSite S E.fppf_mem (etaleSpace T E h X)).obj
        (Space.SpacesEtale.final E.fppfSite S E.fppf_mem (etaleSpace T E h X)))) :=
  ((Space.SpacesEtale.final_isTerminal E.fppfSite S E.fppf_mem (etaleSpace T E h X)).isTerminalObj
    _).isTerminalObj _

/-- **`Γ_fppf = Γ_étale ∘ a_{X,*}`.** -/
def fppfGlobalSectionsIso :
    fppfGlobalSections T X ≅
      fppfToSmallEtaleAbelianPushforward T E h X ⋙ etaleGlobalSections T E h X :=
  (sheafSections _ AddCommGrpCat.{u + 1}).mapIso
    ((finalImageIsTerminal T E h X).uniqueUpToIso (Over.mkIdTerminal (X := X))).op

/-- **`a_X⁻¹` carries constant sheaves to constant sheaves**: both `a_X⁻¹` of the constant
étale sheaf and the constant fppf sheaf are left adjoint to `Γ_fppf = Γ_étale ∘ a_{X,*}`. -/
def constantSheafCompFppfToSmallEtaleIso :
    constantSheaf (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem (etaleSpace T E h X))
        AddCommGrpCat.{u + 1} ⋙
        CategoryTheory.Sites.abelianInverseImage (fppfToSmallEtaleMorphism T E h X) ≅
      constantSheaf (BigFppfSpaceOver.topology T X) AddCommGrpCat.{u + 1} :=
  (((constantSheafAdj _ AddCommGrpCat.{u + 1}
      (Space.SpacesEtale.final_isTerminal E.fppfSite S E.fppf_mem (etaleSpace T E h X))).comp
    (fppfToSmallEtaleAbelianAdjunction T E h X)).ofNatIsoRight
      (fppfGlobalSectionsIso T E h X).symm).leftAdjointUniq
    (constantSheafAdj _ AddCommGrpCat.{u + 1} (Over.mkIdTerminal (X := X)))

variable [HasDerivedCategory (Sheaf (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem
    (etaleSpace T E h X)) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory (Sheaf (E.bigEtaleTopology (etaleSpace T E h X)) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory (Sheaf (BigFppfSpaceOver.topology T X) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory AddCommGrpCat.{u + 1}]

/-- `RΓ_fppf = RΓ_étale ∘ Ra_{X,*}` on `D⁺((Spaces/X)_fppf)` (Stacks 08J6): `a_{X,*}` carries
injective sheaves to injective sheaves. -/
def fppfDerivedGlobalSectionsIso :
    (fppfGlobalSections T X).rightDerivedFunctorPlus ≅
      (fppfToSmallEtaleAbelianPushforward T E h X).rightDerivedFunctorPlus ⋙
        (etaleGlobalSections T E h X).rightDerivedFunctorPlus :=
  haveI : (fppfToSmallEtaleAbelianPushforward T E h X).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (fppfToSmallEtaleAbelianAdjunction T E h X)
  Functor.rightDerivedFunctorPlusNatIso (fppfGlobalSectionsIso T E h X) ≪≫
    Functor.rightDerivedFunctorPlusCompIsoOfRightAcyclic _ _ fun _ _ ↦
      Functor.rightAcyclic_of_injective _ _

/-- **The canonical map `RΓ(X_étale, K) ⟶ RΓ_fppf(X, a_X⁻¹K)`**: the unit `K ⟶ Ra_{X,*}a_X⁻¹K`
followed by `RΓ_étale ∘ Ra_{X,*} = RΓ_fppf` (Stacks 08J6). -/
def etaleToFppfDerivedGlobalSections :
    (etaleGlobalSections T E h X).rightDerivedFunctorPlus ⟶
      (CategoryTheory.Sites.abelianInverseImage
        (fppfToSmallEtaleMorphism T E h X)).mapDerivedCategoryPlus ⋙
        (fppfGlobalSections T X).rightDerivedFunctorPlus :=
  (Functor.leftUnitor _).inv ≫
    Functor.whiskerRight (Stacks.ComparingTopologies.derivedPlusAdjunction
      (fppfToSmallEtaleAbelianAdjunction T E h X)).unit _ ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft _ (fppfDerivedGlobalSectionsIso T E h X).inv

/-- **Stacks 0DGH (2) in `D⁺`, granted the scheme case**: the canonical map
`RΓ(X_étale, K) ⟶ RΓ_fppf(X, a_X⁻¹K)` is an isomorphism for every `K` in `D⁺(X_étale)`. -/
theorem isIso_etaleToFppfDerivedGlobalSections_of
    (hsch : SchemeFppfEtaleHigherVanishing E.fppfSite) :
    IsIso (etaleToFppfDerivedGlobalSections T E h X) := by
  have : ∀ K, IsIso ((Stacks.ComparingTopologies.derivedPlusAdjunction
      (fppfToSmallEtaleAbelianAdjunction T E h X)).unit.app K) := fun K ↦
    (isIso_fppfToSmallEtale_derivedUnits_of T E h X hsch K).2
  have := NatIso.isIso_of_isIso_app (Stacks.ComparingTopologies.derivedPlusAdjunction
      (fppfToSmallEtaleAbelianAdjunction T E h X)).unit
  unfold etaleToFppfDerivedGlobalSections
  infer_instance

/-- `RΓ(X_étale, K) = RΓ_fppf(X, a_X⁻¹K)`, naturally in `K`, granted the scheme case: the canonical
map `etaleToFppfDerivedGlobalSections`. -/
def derivedGlobalSectionsIso_of (hsch : SchemeFppfEtaleHigherVanishing E.fppfSite) :
    (etaleGlobalSections T E h X).rightDerivedFunctorPlus ≅
      (CategoryTheory.Sites.abelianInverseImage
        (fppfToSmallEtaleMorphism T E h X)).mapDerivedCategoryPlus ⋙
        (fppfGlobalSections T X).rightDerivedFunctorPlus :=
  haveI := isIso_etaleToFppfDerivedGlobalSections_of T E h X hsch
  asIso (etaleToFppfDerivedGlobalSections T E h X)

/-- **Stacks 0DGH (2), granted the scheme case**: the map
`H^q(X_étale, K) ⟶ H^q_fppf(X, a_X⁻¹K)` induced by the canonical map is an isomorphism, for every
`K` in `D⁺(X_étale)` and every `q`. -/
theorem isIso_etaleToFppfCohomology_of (hsch : SchemeFppfEtaleHigherVanishing E.fppfSite)
    (q : ℤ) :
    IsIso (Functor.whiskerRight (etaleToFppfDerivedGlobalSections T E h X)
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} q)) := by
  have := isIso_etaleToFppfDerivedGlobalSections_of T E h X hsch
  infer_instance

/-- **Stacks 0DGH (2), granted the scheme case**: `H^q(X_étale, K) = H^q_fppf(X, a_X⁻¹K)` for
`K` in `D⁺(X_étale)`, naturally in `K`. -/
def etaleCohomologyDerivedIso_of (hsch : SchemeFppfEtaleHigherVanishing E.fppfSite) (q : ℤ) :
    (etaleGlobalSections T E h X).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} q ≅
      (CategoryTheory.Sites.abelianInverseImage
        (fppfToSmallEtaleMorphism T E h X)).mapDerivedCategoryPlus ⋙
        (fppfGlobalSections T X).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} q :=
  Functor.isoWhiskerRight (derivedGlobalSectionsIso_of T E h X hsch) _ ≪≫
    Functor.associator _ _ _

/-- **Stacks 0DGH (1), granted the scheme case**: `H^q(X_étale, F) = H^q_fppf(X, a_X⁻¹F)` for an
abelian sheaf `F` on `X_étale`. -/
def etaleCohomologyIso_of (hsch : SchemeFppfEtaleHigherVanishing E.fppfSite)
    (F : Sheaf (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem (etaleSpace T E h X))
      AddCommGrpCat.{u + 1}) (q : ℕ) :
    ((etaleGlobalSections T E h X).rightDerived q).obj F ≅
      ((fppfGlobalSections T X).rightDerived q).obj
        ((CategoryTheory.Sites.abelianInverseImage (fppfToSmallEtaleMorphism T E h X)).obj F) :=
  (CategoryTheory.rightDerivedPlusObjIso _ F q).symm ≪≫
    (etaleCohomologyDerivedIso_of T E h X hsch q).app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F) ≪≫
    (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} q).mapIso
      ((fppfGlobalSections T X).rightDerivedFunctorPlus.mapIso
        (Functor.mapDerivedCategoryPlusObjSingleIso _ F)) ≪≫
    CategoryTheory.rightDerivedPlusObjIso _ _ q

/-- **The example of Stacks 0DGH, granted the scheme case**: for an abelian group `A`,
`H^q_étale(X, A) = H^q_fppf(X, A)` for the constant sheaves. -/
def etaleCohomologyConstantIso_of (hsch : SchemeFppfEtaleHigherVanishing E.fppfSite)
    (A : AddCommGrpCat.{u + 1}) (q : ℕ) :
    ((etaleGlobalSections T E h X).rightDerived q).obj
        ((constantSheaf (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem (etaleSpace T E h X))
          AddCommGrpCat.{u + 1}).obj A) ≅
      ((fppfGlobalSections T X).rightDerived q).obj
        ((constantSheaf (BigFppfSpaceOver.topology T X) AddCommGrpCat.{u + 1}).obj A) :=
  etaleCohomologyIso_of T E h X hsch _ q ≪≫
    ((fppfGlobalSections T X).rightDerived q).mapIso
      ((constantSheafCompFppfToSmallEtaleIso T E h X).app A)

end AlgebraicGeometry.BigFppfSpaceSite

end
