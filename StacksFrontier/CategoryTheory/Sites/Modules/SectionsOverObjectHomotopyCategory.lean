module

public import StacksFrontier.CategoryTheory.Sites.Modules.SectionsOverObjectCorepresentable
public import StacksFrontier.Algebra.Homology.HomotopyCategory.HomComplexFromSingle
public import StacksFrontier.Homology.HomComplex.RHom

/-!
# Cohomology of the sections over an object of a complex of sheaves of modules

Let `(C, O)` be a ringed site, `U` an object of `C` and `M` a cochain complex of `O`-modules.
This file identifies the degree-`n` cohomology of the complex of abelian groups `Γ(U, M^•)`
with the group of morphisms

`(j_{U!} O_U)[0] ⟶ M^•⟦n⟧`

in the homotopy category `K(O)`.

Three identifications are composed. Sections over `U` are corepresented by `j_{U!} O_U`
(Stacks 0G1V, `Stacks.Sites.ExtensionByZero.coyonedaExtensionByZeroUnitIso`), so the complex
`Γ(U, M^•)` is the degreewise `Hom(j_{U!} O_U, -)` of `M^•`; that complex is Mathlib's `Hom`
complex out of `(j_{U!} O_U)[0]`
(`CochainComplex.HomComplex.homComplexSingleIsoCoyonedaComplex`); and the cohomology of a `Hom`
complex is a group of morphisms in the homotopy category (Stacks 0A5X,
`homComplexHomologyAddEquiv`).

## Main definitions

* `Stacks.Sites.ExtensionByZero.sectionsOverObjectHomologyAddEquiv`: the identification
  `Hⁿ(Γ(U, M^•)) ≃+ ((j_{U!} O_U)[0] ⟶ M^•⟦n⟧)` in `K(O)`.

## Implementation notes

Universes are collapsed to a single `u`, so that the hom universe of `SheafOfModules.{u} R`,
in which `CategoryTheory.preadditiveCoyoneda` lands, agrees with the universe of the module
sections, in which `Γ(U, -)` lands.

## References

* [Stacks Project, Tag 0G1V](https://stacks.math.columbia.edu/tag/0G1V)
* [Stacks Project, Tag 0A5X](https://stacks.math.columbia.edu/tag/0A5X)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.Sites.ExtensionByZero

universe u

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
  (R : Sheaf J RingCat.{u}) (U : C)
  [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Sections over `U` of sheaves of modules, read in abelian groups. -/
noncomputable abbrev sectionsOverObjectFunctor :
    SheafOfModules.{u} R ⥤ AddCommGrpCat.{u} :=
  SheafOfModules.evaluation.{u} R (op U) ⋙
    forget₂ (ModuleCat.{u} (R.obj.obj (op U))) AddCommGrpCat.{u}

/-- The sections-over-`U` functor on sheaves of modules is additive. -/
instance additive_sectionsOverObjectFunctor :
    (sectionsOverObjectFunctor J R U).Additive where
  map_add := rfl

/-- The complex of sections over `U` of a complex of sheaves of modules is the degreewise
`Hom(j_{U!} O_U, -)` of that complex: this is Stacks 0G1V, applied degreewise. -/
noncomputable def sectionsOverObjectComplexIsoCoyonedaComplex
    (M : CochainComplex (SheafOfModules.{u} R) ℤ) :
    ((sectionsOverObjectFunctor J R U).mapHomologicalComplex (ComplexShape.up ℤ)).obj M ≅
      CochainComplex.HomComplex.coyonedaComplex (extensionByZeroUnitObj J R U) M :=
  ((NatIso.mapHomologicalComplex (coyonedaExtensionByZeroUnitIso J R U)
    (ComplexShape.up ℤ)).app M).symm

/-- **The cohomology of the sections over `U` of a complex of sheaves of modules.** The
degree-`n` cohomology of `Γ(U, M^•)` is the group of morphisms `(j_{U!} O_U)[0] ⟶ M^•⟦n⟧` in
the homotopy category of `O`-modules.

Sections over `U` are corepresented by `j_{U!} O_U` (Stacks 0G1V), the degreewise `Hom` out of
an object is the `Hom` complex out of that object placed in degree zero, and the cohomology of
a `Hom` complex is a group of morphisms in the homotopy category (Stacks 0A5X). -/
noncomputable def sectionsOverObjectHomologyAddEquiv
    (M : CochainComplex (SheafOfModules.{u} R) ℤ) (n : ℤ) :
    (((sectionsOverObjectFunctor J R U).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj M).homology n ≃+
      ((HomotopyCategory.quotient (SheafOfModules.{u} R) (ComplexShape.up ℤ)).obj
          ((CochainComplex.singleFunctor (SheafOfModules.{u} R) 0).obj
            (extensionByZeroUnitObj J R U)) ⟶
        (HomotopyCategory.quotient (SheafOfModules.{u} R) (ComplexShape.up ℤ)).obj (M⟦n⟧)) :=
  (((HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℤ) n).mapIso
      (sectionsOverObjectComplexIsoCoyonedaComplex J R U M ≪≫
        CochainComplex.HomComplex.coyonedaComplexIsoHomComplexSingle
          (extensionByZeroUnitObj J R U) M)).addCommGroupIsoToAddEquiv).trans
    (homComplexHomologyAddEquiv
      ((CochainComplex.singleFunctor (SheafOfModules.{u} R) 0).obj
        (extensionByZeroUnitObj J R U)) M n)

end Stacks.Sites.ExtensionByZero

end
