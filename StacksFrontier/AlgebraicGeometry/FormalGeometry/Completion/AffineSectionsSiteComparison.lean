module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHomFilteredColimit
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusComparisons
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.FormalFunctionsPseudoCoherent
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.LocalCalculation

/-!
# The two models of `RΓ(U, -)` over an open of a scheme agree

Derived sections over an open set `U` of a scheme appear in this library in two unrelated
spellings, both total right derived functors of `ℱ ↦ Γ(U, ℱ)` with values in
`D(Γ(X, U))`:

* `Stacks.Cohomology.HypercohomologyEdge.derivedSections (structureSheafRing X.toRingedSpace) U`,
  the right derived functor of `SheafOfModules.evaluation` at `U`, which is the `RΓ(U, -)` of the
  hypercohomology edge morphism; and
* `AlgebraicGeometry.RingedSite.derivedSectionsOverObject (opensRingedSite X.sheaf) U`, the right
  derived functor of `AlgebraicGeometry.RingedSite.moduleSectionsOver` along the identity of
  `Γ(X, U)`, which is the `RΓ(U, -)` of [Stacks, Tag 0CQI].

This file constructs a natural isomorphism between them.

## Main definitions

* `Stacks.Algebraization.siteSectionsOver` and `Stacks.Algebraization.siteDerivedSectionsOver`:
  the ringed-site sections and derived sections over `U`, ascribed as functors out of `X.Modules`
  and `D(𝒪_X)`.
* `Stacks.Algebraization.schemeDerivedSectionsOver`: the hypercohomology-edge `RΓ(U, -)`, likewise
  ascribed.
* `Stacks.Algebraization.sectionsOverSiteIso`: **`Γ(U, -) ≅ Γ(U, -)`**, the underived comparison.
* `Stacks.Algebraization.derivedSectionsOverSiteIso`: **`RΓ(U, -) ≅ RΓ(U, -)`**, the derived
  comparison.

## Implementation notes

The underived comparison is restriction of scalars along the identity ring map,
`ModuleCat.restrictScalarsId`: the two functors are `evaluation ⋙ restrictScalars (id)` and
`evaluation`. The derived comparison is then the uniqueness of total right derived functors,
`CategoryTheory.Functor.rightDerivedNatIso`.

Both functors are ascribed into the scheme's spelling of the category of `𝒪_X`-modules before
anything is said about them. `X.Modules`, `SheafOfModules (structureSheafRing X.toRingedSpace)` and
`SheafOfModules ((Stacks.SheafOfModules.Tensor.ringSheaf (opensRingedSite X.sheaf).O))` are the
same category, the three spellings of the sheaf of rings being definitionally equal, but instance
search does not see through the difference; ascribing once keeps every statement below in one
spelling, and `Stacks.Algebraization.schemeDerivedSectionsOver_eq` and
`Stacks.Algebraization.siteDerivedSectionsOver_eq` are the `rfl`s that let a consumer pass between
the ascription and the original.

## References

* [Stacks Project, Tag 0CQI](https://stacks.math.columbia.edu/tag/0CQI)
* [Stacks Project, Tag 0D6F](https://stacks.math.columbia.edu/tag/0D6F)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.SheafOfModules (opensRingedSite)
open Stacks.Cohomology.HypercohomologyEdge (derivedSections homotopySections)

universe u

namespace Stacks.Algebraization

attribute [local instance 100000] HasDerivedCategory.standard

variable {X : Scheme.{u}} (U : X.Opens)

/-- **The sections over `U` of the ringed site of `X`**, ascribed as a functor out of
`X.Modules`: `Γ(U, -)` read as a module over `Γ(X, U)` by restriction of scalars along the
identity. -/
def siteSectionsOver : X.Modules ⥤ ModuleCat.{u} Γ(X, U) :=
  AlgebraicGeometry.RingedSite.moduleSectionsOver (opensRingedSite X.sheaf) U
    (RingHom.id Γ(X, U))

/-- `Stacks.Algebraization.siteSectionsOver` is an additive functor. -/
instance siteSectionsOver_additive : (siteSectionsOver U).Additive :=
  AlgebraicGeometry.RingedSite.moduleSectionsOver_additive (opensRingedSite X.sheaf) U
    (RingHom.id Γ(X, U))

/-- **`RΓ(U, -)` of the ringed site of `X`**, ascribed as a functor out of `D(𝒪_X)`. This is the
`RΓ(U, -)` of [Stacks, Tag 0CQI]. -/
def siteDerivedSectionsOver :
    DerivedCategory X.Modules ⥤ DerivedCategory (ModuleCat.{u} Γ(X, U)) :=
  AlgebraicGeometry.RingedSite.derivedSectionsOverObject (opensRingedSite X.sheaf) U

/-- The comparison exhibiting `Stacks.Algebraization.siteDerivedSectionsOver` as the total right
derived functor of `Stacks.Algebraization.siteSectionsOver`. -/
def siteDerivedSectionsOverUnit :
    (siteSectionsOver U).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ siteDerivedSectionsOver U :=
  AlgebraicGeometry.RingedSite.derivedSectionsOverUnit (opensRingedSite X.sheaf) U
    (RingHom.id Γ(X, U))

/-- `Stacks.Algebraization.siteDerivedSectionsOver`, with the unit
`Stacks.Algebraization.siteDerivedSectionsOverUnit`, is a right derived functor of
`Stacks.Algebraization.siteSectionsOver` with respect to the quasi-isomorphisms. -/
instance siteDerivedSectionsOver_isRightDerivedFunctor :
    (siteDerivedSectionsOver U).IsRightDerivedFunctor (siteDerivedSectionsOverUnit U)
      (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)) :=
  AlgebraicGeometry.RingedSite.derivedSectionsOver_isRightDerivedFunctor
    (opensRingedSite X.sheaf) U (RingHom.id Γ(X, U))

/-- **Sections over `U`**, as the hypercohomology edge morphism reads them: evaluation of a sheaf
of modules at `U`. -/
def schemeSectionsOver : X.Modules ⥤ ModuleCat.{u} Γ(X, U) :=
  _root_.SheafOfModules.evaluation (structureSheafRing X.toRingedSpace) (op U)

/-- `Stacks.Algebraization.schemeSectionsOver` is an additive functor. -/
instance schemeSectionsOver_additive : (schemeSectionsOver U).Additive :=
  inferInstanceAs (_root_.SheafOfModules.forget (structureSheafRing X.toRingedSpace) ⋙
    PresheafOfModules.evaluation _ (op U)).Additive

/-- **`RΓ(U, -)` as the hypercohomology edge morphism reads it**, ascribed as a functor out of
`D(𝒪_X)`. -/
def schemeDerivedSectionsOver :
    DerivedCategory X.Modules ⥤ DerivedCategory (ModuleCat.{u} Γ(X, U)) :=
  derivedSections (structureSheafRing X.toRingedSpace) U

/-- The comparison exhibiting `Stacks.Algebraization.schemeDerivedSectionsOver` as the total right
derived functor of `Stacks.Algebraization.schemeSectionsOver`. -/
def schemeDerivedSectionsOverUnit :
    (schemeSectionsOver U).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ schemeDerivedSectionsOver U :=
  (homotopySections (structureSheafRing X.toRingedSpace) U).totalRightDerivedUnit
    DerivedCategory.Qh
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
      (ComplexShape.up ℤ))

/-- `Stacks.Algebraization.schemeDerivedSectionsOver`, with the unit
`Stacks.Algebraization.schemeDerivedSectionsOverUnit`, is a right derived functor of
`Stacks.Algebraization.schemeSectionsOver` with respect to the quasi-isomorphisms. -/
instance schemeDerivedSectionsOver_isRightDerivedFunctor :
    (schemeDerivedSectionsOver U).IsRightDerivedFunctor (schemeDerivedSectionsOverUnit U)
      (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)) :=
  (inferInstance :
    ((homotopySections (structureSheafRing X.toRingedSpace) U).totalRightDerived
        DerivedCategory.Qh
        (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
          (ComplexShape.up ℤ))).IsRightDerivedFunctor
      ((homotopySections (structureSheafRing X.toRingedSpace) U).totalRightDerivedUnit
        DerivedCategory.Qh
        (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
          (ComplexShape.up ℤ)))
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
        (ComplexShape.up ℤ)))

/-- **The two models of `Γ(U, -)` agree.** One is evaluation at `U`, the other evaluation
followed by restriction of scalars along the identity of `Γ(X, U)`. -/
def sectionsOverSiteIso : siteSectionsOver U ≅ schemeSectionsOver U :=
  Functor.isoWhiskerLeft
      (_root_.SheafOfModules.evaluation (structureSheafRing X.toRingedSpace) (op U))
      (ModuleCat.restrictScalarsId Γ(X, U)) ≪≫
    Functor.rightUnitor _

/-- **The two models of `RΓ(U, -)` agree**: the ringed-site derived sections over `U` of
[Stacks, Tag 0CQI] and the derived sections of the hypercohomology edge morphism are isomorphic
as functors `D(𝒪_X) ⥤ D(Γ(X, U))`.

Both are total right derived functors along `DerivedCategory.Qh` of the two isomorphic functors
`K(Mod 𝒪_X) ⥤ D(Γ(X, U))` induced by `Stacks.Algebraization.sectionsOverSiteIso`, so they are
identified by the uniqueness of right derived functors. -/
def derivedSectionsOverSiteIso : siteDerivedSectionsOver U ≅ schemeDerivedSectionsOver U :=
  Functor.rightDerivedNatIso _ _ (siteDerivedSectionsOverUnit U)
    (schemeDerivedSectionsOverUnit U)
    (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ))
    (Functor.isoWhiskerRight
      (Functor.mapHomotopyCategoryNatIso (sectionsOverSiteIso U) (ComplexShape.up ℤ))
      DerivedCategory.Qh)

/-- `Stacks.Algebraization.schemeDerivedSectionsOver` is the hypercohomology-edge `RΓ(U, -)` it
ascribes. -/
theorem schemeDerivedSectionsOver_eq :
    schemeDerivedSectionsOver U = derivedSections (structureSheafRing X.toRingedSpace) U :=
  rfl

/-- `Stacks.Algebraization.siteDerivedSectionsOver` is the ringed-site `RΓ(U, -)` it ascribes. -/
theorem siteDerivedSectionsOver_eq :
    siteDerivedSectionsOver U =
      AlgebraicGeometry.RingedSite.derivedSectionsOverObject (opensRingedSite X.sheaf) U :=
  rfl

end Stacks.Algebraization

end
