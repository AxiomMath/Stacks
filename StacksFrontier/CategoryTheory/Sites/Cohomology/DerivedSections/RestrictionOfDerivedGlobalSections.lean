module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.DerivedGlobalSectionsOfModules
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.IntoAKInjectiveComplex

/-!
# Restricting derived global sections to an object of the site

Let `(C, O)` be a ringed site and `U` an object of `C`. A global section of a sheaf of
`O`-modules is a compatible family of sections, so it has a section over `U`; this is a natural
transformation `Γ(C, -) ⟶ Γ(U, -)` of the two underived sections functors of
`StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.DerivedGlobalSectionsOfModules`,
and the universal property of the right derived functor turns it into the **restriction
`RΓ(C, -) ⟶ RΓ(U, -)` of derived global sections to derived sections over `U`**.

On a K-injective complex both derived functors are computed by the complexes of sections, and
there the restriction is the one of those complexes: that is the content of
`Stacks.Cohomology.ModuleSections.derivedSectionsRestriction_app_globalSectionsKInjectiveIso`,
and it is what lets the restriction map on hypercohomology be computed.

## Main definitions

* `Stacks.Cohomology.ModuleSections.sectionRestriction`: restriction of a global section to `U`,
  as a natural transformation of the underived sections functors.
* `Stacks.Cohomology.ModuleSections.globalSectionsComplexRestriction`: the induced morphism
  `Γ(C, K^•) ⟶ Γ(U, K^•)` of the section complexes of Stacks 0A8Z and 0A8Y.
* `Stacks.Cohomology.ModuleSections.derivedSectionsRestriction`: the restriction
  `RΓ(C, -) ⟶ RΓ(U, -)`.

## Main results

* `Stacks.Cohomology.ModuleSections.globalSectionsComplexRestriction_naturality`: the restriction
  of section complexes is natural in the complex.
* `Stacks.Cohomology.ModuleSections.derivedSectionsRestriction_app_unit`: the defining property
  of the restriction of derived functors, read at the unit.
* `Stacks.Cohomology.ModuleSections.derivedSectionsRestriction_app_globalSectionsKInjectiveIso`:
  **on a K-injective complex the restriction of derived sections is the restriction of the
  complexes of sections**, through the two comparisons of Stacks 07A5.

## Implementation notes

The restriction of the derived functors is `CategoryTheory.Functor.rightDerivedNatTrans` applied
to the units of the two total right derived functors; the `HasRightDerivedFunctor` hypotheses
come from `Stacks.Cohomology.Localization.hasRightDerivedFunctorOfGrothendieck`, so none are
stated.

The K-injective comparison is proved by unfolding both Stacks 07A5 isomorphisms into the same
four-step composite — the localization comparison, the comparison of
`CategoryTheory.Functor.mapHomotopyCategory` with
`CategoryTheory.Functor.mapHomologicalComplex`, the unit, and the localization comparison again
— and matching the four steps. The middle step is where `rightDerivedNatTrans_app` enters; the
other three are ordinary naturality, except that the components of
`CategoryTheory.Functor.mapHomotopyCategoryFactors` are identities, which is what makes the
second step hold by `rfl`.

*Why the composite comparisons are not rewritten apart.* The source of the inverse component of
`mapHomotopyCategoryFactors` is `(F.mapHomologicalComplex c ⋙ quotient).obj K` rather than
`quotient.obj (F.mapHomologicalComplex c |>.obj K)`; the two are definitionally equal but not
type-correct for each other at `implicit` transparency, so `rw` and `simp only` refuse to
compose across them. The composite is therefore assembled with
`CategoryTheory.Functor.map_comp` as a term and `congrArg`.

## References

* [Stacks Project, Tag 07A5](https://stacks.math.columbia.edu/tag/07A5)
* [Stacks Project, Tag 0A8Z](https://stacks.math.columbia.edu/tag/0A8Z)
* [Stacks Project, Tag 0A8Y](https://stacks.math.columbia.edu/tag/0A8Y)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace Stacks.Cohomology.ModuleSections

universe u

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u}) (U : X.C)

/-- Restriction of a global section to `U`. -/
def sectionRestriction :
    moduleGlobalSections X ⟶ Localization.sectionsOverObject X U where
  app _ := AddCommGrpCat.ofHom
    { toFun := fun s ↦ s.val (op U)
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  naturality _ _ _ := rfl

/-- Restriction of global sections of a complex. -/
def globalSectionsComplexRestriction
    (H : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    RingedSite.globalSectionsComplex X H ⟶ RingedSite.sectionComplex X H U :=
  (NatTrans.mapHomologicalComplex (sectionRestriction X U) (ComplexShape.up ℤ)).app H

/-- The restriction `Γ(C, H) ⟶ Γ(U, H)` of section complexes is natural in the complex `H`. -/
theorem globalSectionsComplexRestriction_naturality
    {H H' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (φ : H ⟶ H') :
    RingedSite.globalSectionsComplexMap X φ ≫ globalSectionsComplexRestriction X U H' =
      globalSectionsComplexRestriction X U H ≫ RingedSite.sectionComplexMap X U φ :=
  (NatTrans.mapHomologicalComplex (sectionRestriction X U) (ComplexShape.up ℤ)).naturality φ

/-- The restriction of derived global sections to derived sections over `U`. -/
def derivedSectionsRestriction :
    derivedModuleGlobalSections X ⟶ Localization.derivedSectionsOverObject X U :=
  Functor.rightDerivedNatTrans _ _ (derivedModuleGlobalSectionsUnit X)
    (derivedSectionsOverObjectUnit X U)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (ComplexShape.up ℤ))
    (Functor.whiskerRight
      (NatTrans.mapHomotopyCategory (sectionRestriction X U) (ComplexShape.up ℤ))
      DerivedCategory.Qh)

/-- Composed with the unit of `RΓ(C, -)` at a complex `H`, the restriction `RΓ(C, -) ⟶ RΓ(U, -)`
is the image of the restriction of sections of `H` followed by the unit of `RΓ(U, -)`. -/
theorem derivedSectionsRestriction_app_unit
    (H : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    (derivedModuleGlobalSectionsUnit X).app
          ((HomotopyCategory.quotient
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
            (ComplexShape.up ℤ)).obj H) ≫
        (derivedSectionsRestriction X U).app
          (DerivedCategory.Qh.obj
            ((HomotopyCategory.quotient
              (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
              (ComplexShape.up ℤ)).obj H)) =
      DerivedCategory.Qh.map
          ((NatTrans.mapHomotopyCategory (sectionRestriction X U) (ComplexShape.up ℤ)).app
            ((HomotopyCategory.quotient
              (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
              (ComplexShape.up ℤ)).obj H)) ≫
        (derivedSectionsOverObjectUnit X U).app
          ((HomotopyCategory.quotient
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
            (ComplexShape.up ℤ)).obj H) :=
  Functor.rightDerivedNatTrans_app _ _ _ _ _ _ _

private theorem factors_comp_mapHomotopyCategory
    (H : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    ((moduleGlobalSections X).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app H ≫
        (NatTrans.mapHomotopyCategory (sectionRestriction X U) (ComplexShape.up ℤ)).app
          ((HomotopyCategory.quotient
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
            (ComplexShape.up ℤ)).obj H) =
      (HomotopyCategory.quotient AddCommGrpCat.{u} (ComplexShape.up ℤ)).map
          (globalSectionsComplexRestriction X U H) ≫
        ((Localization.sectionsOverObject X U).mapHomotopyCategoryFactors
          (ComplexShape.up ℤ)).inv.app H := rfl

private theorem qh_factors_square
    (I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    DerivedCategory.Qh.map
          (((moduleGlobalSections X).mapHomotopyCategoryFactors
            (ComplexShape.up ℤ)).inv.app I) ≫
        DerivedCategory.Qh.map
          ((NatTrans.mapHomotopyCategory (sectionRestriction X U) (ComplexShape.up ℤ)).app
            ((HomotopyCategory.quotient
              (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
              (ComplexShape.up ℤ)).obj I)) =
      DerivedCategory.Qh.map
          ((HomotopyCategory.quotient AddCommGrpCat.{u} (ComplexShape.up ℤ)).map
            (globalSectionsComplexRestriction X U I)) ≫
        DerivedCategory.Qh.map
          (((Localization.sectionsOverObject X U).mapHomotopyCategoryFactors
            (ComplexShape.up ℤ)).inv.app I) :=
  (DerivedCategory.Qh.map_comp _ _).symm.trans
    ((congrArg (fun f => DerivedCategory.Qh.map f)
        (factors_comp_mapHomotopyCategory X U I)).trans
      (DerivedCategory.Qh.map_comp _ _))

private theorem globalSectionsKInjectiveIso_hom
    (I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [I.IsKInjective] :
    (globalSectionsKInjectiveIso X I).hom =
      ((DerivedCategory.quotientCompQhIso AddCommGrpCat.{u}).app
          (RingedSite.globalSectionsComplex X I)).inv ≫
        DerivedCategory.Qh.map
            (((moduleGlobalSections X).mapHomotopyCategoryFactors
              (ComplexShape.up ℤ)).inv.app I) ≫
          (derivedModuleGlobalSectionsUnit X).app
              ((HomotopyCategory.quotient
                (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
                (ComplexShape.up ℤ)).obj I) ≫
            (derivedModuleGlobalSections X).map
              ((DerivedCategory.quotientCompQhIso
                (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).app I).hom := rfl

private theorem sectionsKInjectiveIso_hom
    (I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [I.IsKInjective] :
    (sectionsKInjectiveIso X U I).hom =
      ((DerivedCategory.quotientCompQhIso AddCommGrpCat.{u}).app
          (RingedSite.sectionComplex X I U)).inv ≫
        DerivedCategory.Qh.map
            (((Localization.sectionsOverObject X U).mapHomotopyCategoryFactors
              (ComplexShape.up ℤ)).inv.app I) ≫
          (derivedSectionsOverObjectUnit X U).app
              ((HomotopyCategory.quotient
                (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
                (ComplexShape.up ℤ)).obj I) ≫
            (Localization.derivedSectionsOverObject X U).map
              ((DerivedCategory.quotientCompQhIso
                (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).app I).hom := rfl

/-- **Sections compute derived sections compatibly with restriction.** On a K-injective complex
`I` both Tag 07A5 comparisons are invertible, and the restriction of derived global sections to
derived sections over `U` is, through them, the restriction of the complexes of sections. -/
theorem derivedSectionsRestriction_app_globalSectionsKInjectiveIso
    (I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [I.IsKInjective] :
    (globalSectionsKInjectiveIso X I).hom ≫
        (derivedSectionsRestriction X U).app (DerivedCategory.Q.obj I) =
      DerivedCategory.Q.map (globalSectionsComplexRestriction X U I) ≫
        (sectionsKInjectiveIso X U I).hom := by
  rw [globalSectionsKInjectiveIso_hom, sectionsKInjectiveIso_hom]
  have hnat := (derivedSectionsRestriction X U).naturality
    ((DerivedCategory.quotientCompQhIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).app I).hom
  have hunit := derivedSectionsRestriction_app_unit X U I
  have hq := (DerivedCategory.quotientCompQhIso AddCommGrpCat.{u}).inv.naturality
    (globalSectionsComplexRestriction X U I)
  simp only [Functor.comp_map, ← Iso.app_inv] at hq
  simp only [Functor.comp_obj] at hnat
  simp only [Category.assoc]
  rw [hnat, reassoc_of% hunit, reassoc_of% qh_factors_square, ← reassoc_of% hq]

end Stacks.Cohomology.ModuleSections

end
