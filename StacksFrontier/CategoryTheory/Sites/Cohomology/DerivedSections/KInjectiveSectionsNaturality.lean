module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.DerivedGlobalSectionsOfModules
import StacksCore.Tactic.StacksAttribute

/-! # Naturality of the K-injective comparison for derived global sections

Let `(C, O)` be a ringed site. On a K-injective complex `I` of `O`-modules the complex of global
sections already computes `RΓ(C, I)`; that comparison is
`Stacks.Cohomology.ModuleSections.globalSectionsKInjectiveIso`, an instance of Stacks 07A5 for the
global sections functor; the complete statement of Stacks 07A5 is
`Stacks.Cohomology.UnboundedComplexes.ringedSite_unboundedComplexes`. This file records that the
comparison is **natural**: a morphism of K-injective complexes induces a square with the map on
global sections on one side and the map on derived global sections on the other.

The comparison is a composite of four natural pieces — the identification of the localisation
of the homotopy category with the derived category, twice, the factorisation of
`Functor.mapHomotopyCategory` through `Functor.mapHomologicalComplex`, and the unit of the
derived functor, which is invertible on a K-injective complex — so the naturality is the
chaining of the four corresponding naturality squares.

## Main results

* `Stacks.Cohomology.ModuleSections.globalSectionsKInjectiveIso_naturality`.

## Implementation notes

The morphism of global section complexes is spelled
`((moduleGlobalSections X).mapHomologicalComplex (ComplexShape.up ℤ)).map`, the image of the
morphism under the functor the comparison is built from, which is definitionally
`AlgebraicGeometry.RingedSite.globalSectionsComplexMap` by
`Stacks.Cohomology.ModuleSections.moduleGlobalSections_mapHomologicalComplex`. Only the former
spelling makes the four squares compose without a transport.

No companion statement is given for
`Stacks.Cohomology.ModuleSections.sectionsKInjectiveIso`: nothing in this development needs it,
and the proof would be the same four squares for the sections-over-an-object functor.

## References

* [Stacks Project, Tag 07A5](https://stacks.math.columbia.edu/tag/07A5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace Stacks.Cohomology.ModuleSections

universe u

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})

/-- **The comparison of global sections with derived global sections on a K-injective complex
is natural.** For a morphism `t : I ⟶ J` of K-injective complexes of `O`-modules, the class of
the induced morphism of global section complexes corresponds to the morphism
`RΓ(C, I) ⟶ RΓ(C, J)` induced by the class of `t`. -/
theorem globalSectionsKInjectiveIso_naturality
    {I J : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    [I.IsKInjective] [J.IsKInjective]
    (t : I ⟶ J) :
    DerivedCategory.Q.map
          (((moduleGlobalSections X).mapHomologicalComplex (ComplexShape.up ℤ)).map t) ≫
        (globalSectionsKInjectiveIso X J).hom =
      (globalSectionsKInjectiveIso X I).hom ≫
        (derivedModuleGlobalSections X).map (DerivedCategory.Q.map t) := by
  have h1 : DerivedCategory.Q.map
          (((moduleGlobalSections X).mapHomologicalComplex (ComplexShape.up ℤ)).map t) ≫
        (DerivedCategory.quotientCompQhIso AddCommGrpCat.{u}).inv.app
          (RingedSite.globalSectionsComplex X J) =
      (DerivedCategory.quotientCompQhIso AddCommGrpCat.{u}).inv.app
          (RingedSite.globalSectionsComplex X I) ≫
        DerivedCategory.Qh.map
          ((HomotopyCategory.quotient AddCommGrpCat.{u} (ComplexShape.up ℤ)).map
            (((moduleGlobalSections X).mapHomologicalComplex (ComplexShape.up ℤ)).map t)) :=
    DerivedCategory.quotientCompQhIso_inv_naturality _
  have h2 := ((moduleGlobalSections X).mapHomotopyCategoryFactors
    (ComplexShape.up ℤ)).inv.naturality t
  have h3 := (derivedModuleGlobalSectionsUnit X).naturality
    ((HomotopyCategory.quotient (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (ComplexShape.up ℤ)).map t)
  have h4 := (DerivedCategory.quotientCompQhIso
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).hom.naturality t
  dsimp only [globalSectionsKInjectiveIso, Iso.trans_hom, Iso.symm_hom, asIso_hom,
    CategoryTheory.Functor.mapIso_hom, Iso.app_inv, Iso.app_hom]
  simp only [CategoryTheory.Functor.comp_map] at h2 h3 h4
  simp only [Category.assoc]
  rw [reassoc_of% h1,
    ← CategoryTheory.Functor.map_comp_assoc, h2, CategoryTheory.Functor.map_comp,
    Category.assoc, reassoc_of% h3, ← CategoryTheory.Functor.map_comp, h4,
    CategoryTheory.Functor.map_comp]

end Stacks.Cohomology.ModuleSections

end
