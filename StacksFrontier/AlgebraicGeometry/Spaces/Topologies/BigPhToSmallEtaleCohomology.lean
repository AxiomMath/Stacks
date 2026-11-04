module

public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigPhToSmallEtaleDerivedTorsion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.TorsionConstantSheaf
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedSquareTransComposition
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusComparisons
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusResolution

/-!
# Étale and ph cohomology of torsion sheaves on an algebraic space (Stacks 0DGV)

Let `P` be a big ph site of algebraic spaces over `S`, `E` a big étale site over the same big fppf
site of schemes, `X` an algebraic space, and `a_X` the comparison morphism of Stacks 0DGW from the
big ph topos of `X` to its small étale topos. Stacks 0DGV says:

1. `H^q(X_étale, F) = H^q_ph(X, a_X⁻¹F)` for a torsion abelian sheaf `F` on `X_étale`;
2. `H^q(X_étale, K) = H^q_ph(X, a_X⁻¹K)` for `K` in `D⁺(X_étale)` with torsion cohomology sheaves;

and, for a torsion abelian group `A`, `H^q_étale(X, A) = H^q_ph(X, A)`.

## Main results

* `AlgebraicGeometry.BigPHSpaceSite.isIso_etaleToPhDerivedGlobalSections_app`: the canonical map
  `RΓ(X_étale, K) ⟶ RΓ_ph(X, a_X⁻¹K)` is an isomorphism for `K` with torsion cohomology sheaves.
* `AlgebraicGeometry.BigPHSpaceSite.etaleCohomologyDerivedIsoOfTorsion`: **Stacks 0DGV (2)**.
* `AlgebraicGeometry.BigPHSpaceSite.etaleCohomologyIsoOfTorsion`: **Stacks 0DGV (1)**.
* `AlgebraicGeometry.BigPHSpaceSite.etaleCohomologyConstantIsoOfTorsion`: the example.

## Implementation notes

The source deduces 0DGV from Stacks 0DGU by Stacks 08J6: `RΓ_ph = RΓ_étale ∘ Ra_{X,*}`, because
`a_{X,*}` carries injective sheaves to injective sheaves, so the unit `K ⟶ Ra_{X,*}a_X⁻¹K` of
Stacks 0DGU gives `RΓ(X_étale, K) = RΓ_ph(X, a_X⁻¹K)`. The comparisons of global sections are the
ph analogues of those of the fppf case, Stacks 0DGH. The derived categories are those of
Stacks 0DGU, in the model `HasDerivedCategory.standard`.

## References

* [Stacks Project, Tag 0DGV](https://stacks.math.columbia.edu/tag/0DGV)
* [Stacks Project, Tag 0DGU](https://stacks.math.columbia.edu/tag/0DGU)
* [Stacks Project, Tag 08J6](https://stacks.math.columbia.edu/tag/08J6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.BigPHSpaceSite

attribute [local instance 2000]
  HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

attribute [local instance] HasDerivedCategory.standard

variable {S : Scheme.{u}} (P : BigPHSpaceSite S) (E : BigEtaleSpaceSite S)
  (h : P.fppfSite = E.fppfSite) (X : P.Spaces)

/-- Global sections on the small étale site of `X`: sections over its final object. -/
abbrev etaleGlobalSections :
    Sheaf (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem (etaleSpace P E h X))
        AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1} :=
  (sheafSections _ AddCommGrpCat.{u + 1}).obj
    (op (Space.SpacesEtale.final E.fppfSite S E.fppf_mem (etaleSpace P E h X)))

/-- Global sections on the big ph site of `X`: sections over its final object `X ⟶ X`. -/
abbrev phGlobalSections :
    Sheaf (BigPHSpaceOver.topology P X) AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1} :=
  (sheafSections _ AddCommGrpCat.{u + 1}).obj (op (Over.mk (𝟙 X)))

/-- The final object of the small étale site of `X`, carried into the big ph slice at `X`, is
final there. -/
def finalImageIsTerminal :
    IsTerminal ((Over.postEquiv (canonicalSpaceEquivalence P E h).1 (X := X)).inverse.obj
      ((Space.SpacesEtale.inclusion E.fppfSite S E.fppf_mem (etaleSpace P E h X)).obj
        (Space.SpacesEtale.final E.fppfSite S E.fppf_mem (etaleSpace P E h X)))) :=
  ((Space.SpacesEtale.final_isTerminal E.fppfSite S E.fppf_mem (etaleSpace P E h X)).isTerminalObj
    _).isTerminalObj _

/-- **`Γ_ph = Γ_étale ∘ a_{X,*}`.** -/
def phGlobalSectionsIso :
    phGlobalSections P X ≅
      phToSmallEtaleAbelianPushforward P E h X ⋙ etaleGlobalSections P E h X :=
  (sheafSections _ AddCommGrpCat.{u + 1}).mapIso
    ((finalImageIsTerminal P E h X).uniqueUpToIso (Over.mkIdTerminal (X := X))).op

/-- **`a_X⁻¹` carries constant sheaves to constant sheaves**: both `a_X⁻¹` of the constant
étale sheaf and the constant ph sheaf are left adjoint to `Γ_ph = Γ_étale ∘ a_{X,*}`. -/
def constantSheafCompPhToSmallEtaleIso :
    constantSheaf (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem (etaleSpace P E h X))
        AddCommGrpCat.{u + 1} ⋙
        CategoryTheory.Sites.abelianInverseImage (phToSmallEtaleMorphism P E h X) ≅
      constantSheaf (BigPHSpaceOver.topology P X) AddCommGrpCat.{u + 1} :=
  (((constantSheafAdj _ AddCommGrpCat.{u + 1}
      (Space.SpacesEtale.final_isTerminal E.fppfSite S E.fppf_mem (etaleSpace P E h X))).comp
    (phToSmallEtaleAbelianAdjunction P E h X)).ofNatIsoRight
      (phGlobalSectionsIso P E h X).symm).leftAdjointUniq
    (constantSheafAdj _ AddCommGrpCat.{u + 1} (Over.mkIdTerminal (X := X)))

/-- `RΓ_ph = RΓ_étale ∘ Ra_{X,*}` on `D⁺((Spaces/X)_ph)` (Stacks 08J6): `a_{X,*}` carries
injective sheaves to injective sheaves. -/
def phDerivedGlobalSectionsIso :
    (phGlobalSections P X).rightDerivedFunctorPlus ≅
      (phToSmallEtaleAbelianPushforward P E h X).rightDerivedFunctorPlus ⋙
        (etaleGlobalSections P E h X).rightDerivedFunctorPlus :=
  haveI : (phToSmallEtaleAbelianPushforward P E h X).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (phToSmallEtaleAbelianAdjunction P E h X)
  Functor.rightDerivedFunctorPlusNatIso (phGlobalSectionsIso P E h X) ≪≫
    Functor.rightDerivedFunctorPlusCompIsoOfRightAcyclic _ _ fun _ _ ↦
      Functor.rightAcyclic_of_injective _ _

/-- **The canonical map `RΓ(X_étale, K) ⟶ RΓ_ph(X, a_X⁻¹K)`**: the unit `K ⟶ Ra_{X,*}a_X⁻¹K`
followed by `RΓ_étale ∘ Ra_{X,*} = RΓ_ph` (Stacks 08J6). -/
def etaleToPhDerivedGlobalSections :
    (etaleGlobalSections P E h X).rightDerivedFunctorPlus ⟶
      (CategoryTheory.Sites.abelianInverseImage
        (phToSmallEtaleMorphism P E h X)).mapDerivedCategoryPlus ⋙
        (phGlobalSections P X).rightDerivedFunctorPlus :=
  (Functor.leftUnitor _).inv ≫
    Functor.whiskerRight (Stacks.ComparingTopologies.derivedPlusAdjunction
      (phToSmallEtaleAbelianAdjunction P E h X)).unit _ ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft _ (phDerivedGlobalSectionsIso P E h X).inv

/-- **The canonical map `RΓ(X_étale, K) ⟶ RΓ_ph(X, a_X⁻¹K)` is an isomorphism** for every `K` in
`D⁺(X_étale)` whose cohomology sheaves are torsion: it is the unit `K ⟶ Ra_{X,*}a_X⁻¹K` of
Stacks 0DGU followed by `RΓ_étale ∘ Ra_{X,*} = RΓ_ph`. -/
theorem isIso_etaleToPhDerivedGlobalSections_app
    (K : DerivedCategory.Plus (Sheaf (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem
      (etaleSpace P E h X)) AddCommGrpCat.{u + 1}))
    (hK : ∀ i : ℤ, Stacks.Torsion.torsionSheafProperty _
      ((DerivedCategory.homologyFunctor _ i).obj (DerivedCategory.Plus.ι.obj K))) :
    IsIso ((etaleToPhDerivedGlobalSections P E h X).app K) := by
  have := (isIso_phToSmallEtale_derivedUnits P E h X K hK).2
  simp only [etaleToPhDerivedGlobalSections, NatTrans.comp_app, Functor.leftUnitor_inv_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.whiskerLeft_app,
    Category.id_comp]
  infer_instance

/-- **Stacks 0DGV, part (2).** For `K` in `D⁺(X_étale)` whose cohomology sheaves are torsion,
`H^q(X_étale, K) = H^q_ph(X, a_X⁻¹K)` for every `q`, by the canonical map
`AlgebraicGeometry.BigPHSpaceSite.etaleToPhDerivedGlobalSections`. -/
@[stacks 0DGV "(2)"]
def etaleCohomologyDerivedIsoOfTorsion
    (K : DerivedCategory.Plus (Sheaf (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem
      (etaleSpace P E h X)) AddCommGrpCat.{u + 1}))
    (hK : ∀ i : ℤ, Stacks.Torsion.torsionSheafProperty _
      ((DerivedCategory.homologyFunctor _ i).obj (DerivedCategory.Plus.ι.obj K))) (q : ℤ) :
    (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} q).obj
        ((etaleGlobalSections P E h X).rightDerivedFunctorPlus.obj K) ≅
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} q).obj
        ((phGlobalSections P X).rightDerivedFunctorPlus.obj
          ((CategoryTheory.Sites.abelianInverseImage
            (phToSmallEtaleMorphism P E h X)).mapDerivedCategoryPlus.obj K)) :=
  haveI := isIso_etaleToPhDerivedGlobalSections_app P E h X K hK
  (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} q).mapIso
    (asIso ((etaleToPhDerivedGlobalSections P E h X).app K))

/-- **Stacks 0DGV, part (1).** For a torsion abelian sheaf `F` on `X_étale`,
`H^q(X_étale, F) = H^q_ph(X, a_X⁻¹F)` for every `q`. -/
@[stacks 0DGV "(1)"]
def etaleCohomologyIsoOfTorsion
    (F : Sheaf (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem (etaleSpace P E h X))
      AddCommGrpCat.{u + 1})
    (hF : Stacks.Torsion.torsionSheafProperty _ F) (q : ℕ) :
    ((etaleGlobalSections P E h X).rightDerived q).obj F ≅
      ((phGlobalSections P X).rightDerived q).obj
        ((CategoryTheory.Sites.abelianInverseImage (phToSmallEtaleMorphism P E h X)).obj F) :=
  (CategoryTheory.rightDerivedPlusObjIso _ F q).symm ≪≫
    etaleCohomologyDerivedIsoOfTorsion P E h X ((DerivedCategory.Plus.singleFunctor _ 0).obj F)
      (Stacks.Torsion.torsionCohomologyProperty_singleFunctor _ F hF) q ≪≫
    (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} q).mapIso
      ((phGlobalSections P X).rightDerivedFunctorPlus.mapIso
        (Functor.mapDerivedCategoryPlusObjSingleIso _ F)) ≪≫
    CategoryTheory.rightDerivedPlusObjIso _ _ q

/-- **The example of Stacks 0DGV.** For a torsion abelian group `A`,
`H^q_étale(X, A) = H^q_ph(X, A)` for the constant sheaves. -/
@[stacks 0DGV "the example of a torsion abelian group"]
def etaleCohomologyConstantIsoOfTorsion (A : AddCommGrpCat.{u + 1}) (hA : IsAddTorsion A)
    (q : ℕ) :
    ((etaleGlobalSections P E h X).rightDerived q).obj
        ((constantSheaf (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem (etaleSpace P E h X))
          AddCommGrpCat.{u + 1}).obj A) ≅
      ((phGlobalSections P X).rightDerived q).obj
        ((constantSheaf (BigPHSpaceOver.topology P X) AddCommGrpCat.{u + 1}).obj A) :=
  etaleCohomologyIsoOfTorsion P E h X _
      (Stacks.Torsion.torsionSheafProperty_constantSheaf_of_isAddTorsion _ A hA) q ≪≫
    ((phGlobalSections P X).rightDerived q).mapIso
      ((constantSheafCompPhToSmallEtaleIso P E h X).app A)

end AlgebraicGeometry.BigPHSpaceSite

end
