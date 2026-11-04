module

public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusComparisons
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.Cohomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ZariskiRelativeCohomology
public import StacksFrontier.Homology.DerivedIndexing.Basic

/-!
# Derived global sections on the small crystalline site

Fix a global crystalline situation `(p, (S, I, γ), X)`.  This file constructs
`RΓ(Cris(X/S), -)`, the derived-category-valued global sections of an abelian sheaf on the small
crystalline site, as the right derived functor of `Sheaf.Γ` on bounded below derived categories,
and identifies its cohomology objects with the graded groups `H^j(Cris(X/S), F)` of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/Cohomology.lean`.

## Main definitions

Everything below lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `derivedGlobalSectionsFunctor`: `RΓ(Cris(X/S), -) : D⁺(Ab(Cris(X/S))) ⥤ D⁺(Ab)`, the right
  derived functor on bounded below derived categories of `globalSections`.
* `derivedGlobalSections`: `RΓ(Cris(X/S), -)` on a single abelian sheaf, the composite of the
  degree-zero single-complex functor with `derivedGlobalSectionsFunctor`.
* `hasDerivedCategorySheaf` and `hasDerivedCategoryAddCommGrpCat`: derived category models of the
  abelian sheaves and of the coefficients, with morphisms in `Type (u + 2)`.

## Main results

* `homologyDerivedGlobalSectionsIso`: **the derived and the graded theory agree**,
  `H^j(RΓ(Cris(X/S), F)) ≅ H^j(Cris(X/S), F)`, naturally in `F`; with the object-level
  `homologyDerivedGlobalSectionsIsoObj` and the group-level
  `homologyDerivedGlobalSectionsAddEquiv`.
* `homologyZeroDerivedGlobalSectionsIso`: `H^0(RΓ(Cris(X/S), -)) ≅ Γ(Cris(X/S), -)`.
* `isZero_homology_derivedGlobalSections_of_injective`: `RΓ(Cris(X/S), F)` of an injective
  abelian sheaf is concentrated in degree zero.
* `derivedGlobalSectionsCompIso`, `derivedGlobalSectionsPushforwardIso`: **[Stacks, Tag 015M]
  for crystalline global sections**: the derived functor of `Γ(Cris(Y/S'), -) ∘ g_*` is
  `Rg_*` followed by `RΓ(Cris(Y/S'), -)`, under acyclicity resp. preservation of injectives.
* `derivedGlobalSectionsFunctorIsoPushforward` and `derivedGlobalSectionsIsoPushforward`: given
  `Γ(Cris(Y/S'), g_* -) ≅ Γ(Cris(X/S), -)`, `RΓ(Cris(X/S), -) ≅ Rg_* ⋙ RΓ(Cris(Y/S'), -)`.
* `preservesInjectiveObjects_of_preservesMonomorphisms_leftAdjoint`: a right adjoint whose left
  adjoint preserves monomorphisms preserves injective objects.

## References

* [Stacks Project, Tag 07IT](https://stacks.math.columbia.edu/tag/07IT)
* [Stacks Project, Tag 071E](https://stacks.math.columbia.edu/tag/071E)
* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe w w' w'' u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-! ### The derived category models -/

section Model

variable (S : GlobalCrystallineSituation.{u})

/-- **A derived category of the abelian sheaves on the small crystalline site**, with its
morphisms in `Type (u + 2)`. -/
@[instance_reducible]
def hasDerivedCategorySheaf :
    HasDerivedCategory.{u + 2} (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) :=
  HasDerivedCategory.standard _

/-- **A derived category of the coefficient category**, with its morphisms in `Type (u + 2)`. -/
@[instance_reducible]
def hasDerivedCategoryAddCommGrpCat :
    HasDerivedCategory.{u + 2} AddCommGrpCat.{u + 1} :=
  HasDerivedCategory.standard _

end Model

/-! ### `RΓ(Cris(X/S), -)` -/

section RGamma

variable (S : GlobalCrystallineSituation.{u})
  [HasDerivedCategory.{w} (Sheaf (smallTopology S) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} AddCommGrpCat.{u + 1}]

/-- **The derived global sections `RΓ(Cris(X/S), -)` of the small crystalline site**, as a functor
between bounded below derived categories: the right derived functor of `globalSections`. -/
def derivedGlobalSectionsFunctor :
    DerivedCategory.Plus (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory.Plus AddCommGrpCat.{u + 1} :=
  (globalSections S).rightDerivedFunctorPlus

/-- **`RΓ(Cris(X/S), F)` for a single abelian sheaf `F`**: the sheaf placed in degree zero, then
derived global sections. -/
def derivedGlobalSections :
    Sheaf (smallTopology S) AddCommGrpCat.{u + 1} ⥤
      DerivedCategory.Plus AddCommGrpCat.{u + 1} :=
  DerivedCategory.Plus.singleFunctor (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) 0 ⋙
    derivedGlobalSectionsFunctor S

/-- Taking the degree-`j` cohomology of `RΓ(Cris(X/S), -)` is the `ℤ`-indexed right derived
functor of global sections. -/
theorem derivedGlobalSections_comp_homologyFunctor (j : ℤ) :
    derivedGlobalSections S ⋙ DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} j =
      (globalSections S).rightDerivedPlus j :=
  rfl

/-- **The derived and the graded crystalline theories agree**:
`H^j(RΓ(Cris(X/S), F)) ≅ H^j(Cris(X/S), F)`, naturally in the abelian sheaf `F`. -/
def homologyDerivedGlobalSectionsIso (j : ℕ) :
    derivedGlobalSections S ⋙
        DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} (j : ℤ) ≅
      cohomologyFunctor S j :=
  (Stacks.DerivedIndexing.rightDerivedIso (globalSections S) j).symm ≪≫
    rightDerivedGlobalSectionsIso S j

/-- `H^j(RΓ(Cris(X/S), F)) ≅ H^j(Cris(X/S), F)` at a fixed abelian sheaf. -/
def homologyDerivedGlobalSectionsIsoObj (F : Sheaf (smallTopology S) AddCommGrpCat.{u + 1})
    (j : ℕ) :
    (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} (j : ℤ)).obj
        ((derivedGlobalSections S).obj F) ≅
      (cohomologyFunctor S j).obj F :=
  (homologyDerivedGlobalSectionsIso S j).app F

/-- `H^j(RΓ(Cris(X/S), F)) ≃+ H^j(Cris(X/S), F)`, the comparison read as an additive equivalence
of the underlying groups. -/
def homologyDerivedGlobalSectionsAddEquiv (F : Sheaf (smallTopology S) AddCommGrpCat.{u + 1})
    (j : ℕ) :
    (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} (j : ℤ)).obj
        ((derivedGlobalSections S).obj F) ≃+
      cohomology S F j :=
  (homologyDerivedGlobalSectionsIsoObj S F j).addCommGroupIsoToAddEquiv

/-- **`H^0(RΓ(Cris(X/S), -)) ≅ Γ(Cris(X/S), -)`.** -/
def homologyZeroDerivedGlobalSectionsIso :
    derivedGlobalSections S ⋙
        DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} ((0 : ℕ) : ℤ) ≅
      globalSections S :=
  homologyDerivedGlobalSectionsIso S 0 ≪≫ cohomologyFunctorZeroIso S

/-- **`RΓ(Cris(X/S), F)` of an injective abelian sheaf is concentrated in degree zero.** -/
theorem isZero_homology_derivedGlobalSections_of_injective
    (F : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) [Injective F] (j : ℤ) (hj : j ≠ 0) :
    IsZero ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} j).obj
      ((derivedGlobalSections S).obj F)) :=
  Functor.isZero_rightDerivedPlus_obj_injective (globalSections S) j hj F

end RGamma

/-! ### Composition with a direct image -/

section Functoriality

/-- **A right adjoint whose left adjoint preserves monomorphisms preserves injective objects.**
In particular the direct image of a morphism of topoi, whose inverse image is left exact, preserves
injectives. -/
theorem preservesInjectiveObjects_of_preservesMonomorphisms_leftAdjoint
    {A B : Type*} [Category* A] [Category* B]
    (inverseImage : B ⥤ A) (directImage : A ⥤ B) (adj : inverseImage ⊣ directImage)
    [inverseImage.PreservesMonomorphisms] :
    directImage.PreservesInjectiveObjects :=
  ⟨fun hI => adj.map_injective _ hI⟩

variable (S S' : GlobalCrystallineSituation.{u})
  [HasDerivedCategory.{w} (Sheaf (smallTopology S) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} (Sheaf (smallTopology S') AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]

/-- **[Stacks, Tag 015M] for crystalline global sections, in its acyclicity form.**  For an
additive functor `g` of abelian sheaves from `Cris(X/S)` to `Cris(Y/S')` carrying injectives to
objects with acyclic global sections, the derived functor of `Γ(Cris(Y/S'), -) ∘ g` is `Rg`
followed by `RΓ(Cris(Y/S'), -)`. -/
def derivedGlobalSectionsCompIso
    (g : Sheaf (smallTopology S) AddCommGrpCat.{u + 1} ⥤
      Sheaf (smallTopology S') AddCommGrpCat.{u + 1}) [g.Additive]
    (hg : ∀ I : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}, Injective I →
      (globalSections S').rightAcyclic (g.obj I)) :
    (g ⋙ globalSections S').rightDerivedFunctorPlus ≅
      g.rightDerivedFunctorPlus ⋙ derivedGlobalSectionsFunctor S' :=
  Stacks.Cohomology.DerivedPushforwardSections.compIso g (globalSections S') hg

/-- **[Stacks, Tag 015M] for crystalline global sections, for a direct image.**  For an additive
functor `g` of abelian sheaves from `Cris(X/S)` to `Cris(Y/S')` preserving injectives, the derived
functor of `Γ(Cris(Y/S'), -) ∘ g` is `Rg` followed by `RΓ(Cris(Y/S'), -)`. -/
def derivedGlobalSectionsPushforwardIso
    (g : Sheaf (smallTopology S) AddCommGrpCat.{u + 1} ⥤
      Sheaf (smallTopology S') AddCommGrpCat.{u + 1}) [g.Additive]
    [g.PreservesInjectiveObjects] :
    (g ⋙ globalSections S').rightDerivedFunctorPlus ≅
      g.rightDerivedFunctorPlus ⋙ derivedGlobalSectionsFunctor S' :=
  Stacks.Cohomology.DerivedPushforwardSections.compIsoOfPreservesInjectives g (globalSections S')

/-- **`RΓ(Cris(X/S), -) ≅ Rg_* ⋙ RΓ(Cris(Y/S'), -)`.**  Given a direct image `g` of abelian
sheaves preserving injectives together with an identification `Γ(Cris(Y/S'), g -) ≅
Γ(Cris(X/S), -)` of underived global sections, derived global sections upstairs factor through
the derived direct image. -/
def derivedGlobalSectionsFunctorIsoPushforward
    (g : Sheaf (smallTopology S) AddCommGrpCat.{u + 1} ⥤
      Sheaf (smallTopology S') AddCommGrpCat.{u + 1}) [g.Additive]
    [g.PreservesInjectiveObjects]
    (e : g ⋙ globalSections S' ≅ globalSections S) :
    derivedGlobalSectionsFunctor S ≅
      g.rightDerivedFunctorPlus ⋙ derivedGlobalSectionsFunctor S' :=
  (Functor.rightDerivedFunctorPlusNatIso e).symm ≪≫
    derivedGlobalSectionsPushforwardIso S S' g

/-- `RΓ(Cris(X/S), F) ≅ RΓ(Cris(Y/S'), Rg_* F)` for a single abelian sheaf `F`, the sheaf-level
form of `derivedGlobalSectionsFunctorIsoPushforward`. -/
def derivedGlobalSectionsIsoPushforward
    (g : Sheaf (smallTopology S) AddCommGrpCat.{u + 1} ⥤
      Sheaf (smallTopology S') AddCommGrpCat.{u + 1}) [g.Additive]
    [g.PreservesInjectiveObjects]
    (e : g ⋙ globalSections S' ≅ globalSections S) :
    derivedGlobalSections S ≅
      DerivedCategory.Plus.singleFunctor (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) 0 ⋙
        g.rightDerivedFunctorPlus ⋙ derivedGlobalSectionsFunctor S' :=
  Functor.isoWhiskerLeft _ (derivedGlobalSectionsFunctorIsoPushforward S S' g e)

end Functoriality

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
