module

public import StacksFrontier.AlgebraicGeometry.Spaces.AddCommGrpCatTransported
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleTensor
public import StacksFrontier.CategoryTheory.Monoidal.FunctorCategoryConst
public import StacksFrontier.Topology.Sheaves.Cohomology.Leray.AbelianSheafSpectralSequence

/-!
# The tensor product of abelian sheaves on a topological space

The tensor product of two sheaves of abelian groups on a topological space `X` is the
sheafification of their objectwise tensor product over `ℤ`. This gives a monoidal structure on
`Stacks.Cohomology.Leray.AbelianSheaf X`, obtained from Mathlib's
`CategoryTheory.Sheaf.monoidalCategory` applied to the braided closed monoidal structure
`AddCommGrpCat.monoidalCategory`, `AddCommGrpCat.braidedCategory`, `AddCommGrpCat.monoidalClosed`
on abelian groups. Mathlib's only monoidal structure on `AddCommGrpCat` is the cartesian one.

Mathlib's `CategoryTheory.constantSheaf` is `Functor.const (Opens X)ᵒᵖ` followed by
sheafification, and `CategoryTheory.constantSheafAdj` exhibits it as the left adjoint of
evaluation at a terminal object of the site. The terminal object of `Opens X` is `⊤`, so that
right adjoint is `Stacks.Cohomology.Leray.sectionsFunctor X ⊤`. Both factors of the constant sheaf
functor are monoidal, so the constant sheaf functor is monoidal and its right adjoint is lax
monoidal: this gives the multiplication `Γ(X, F) ⊗ Γ(X, G) ⟶ Γ(X, F ⊗ G)` on sections, from which
the cup product of Cohomology, Section 0FKU is formed.

## Main definitions

* `Stacks.Cohomology.Leray.abelianSheafMonoidalCategory`: **the tensor product of abelian sheaves
  on a topological space.**
* `Stacks.Cohomology.Leray.abelianSheafBraidedCategory`: it is braided.
* `Stacks.Cohomology.Leray.presheafToSheafMonoidal`: sheafification is a monoidal functor for it.
* `Stacks.Cohomology.Leray.constantSheafMonoidal`: **the constant sheaf functor is monoidal** for
  it.
* `Stacks.Cohomology.Leray.sectionsTopLaxMonoidal`: **sections over the whole space are lax
  monoidal**, so there are canonical maps `Γ(X, F) ⊗ Γ(X, G) ⟶ Γ(X, F ⊗ G)`, natural in both
  variables and compatible with the associators and the units.

## Implementation notes

`abelianSheafMonoidalCategory` and `abelianSheafBraidedCategory` are `@[instance_reducible]`
definitions rather than instances, following `AddCommGrpCat.monoidalCategory` and Mathlib's
`CategoryTheory.Sheaf.monoidalCategory`: a global monoidal instance on a category that also has
finite products conflicts with the cartesian one. They are enabled with
`attribute [local instance]`, after the `AddCommGrpCat` structures their types mention.

## References

* [Stacks Project, Tag 0722](https://stacks.math.columbia.edu/tag/0722)
* [Stacks Project, Section 0FKU](https://stacks.math.columbia.edu/tag/0FKU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open CategoryTheory.Enriched.FunctorCategory
open scoped CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed

universe u v

namespace Stacks.Cohomology.Leray

attribute [local instance] AddCommGrpCat.monoidalCategory
  AddCommGrpCat.uliftIntEquivalenceInverseMonoidal
  AddCommGrpCat.uliftIntEquivalenceFunctorMonoidal AddCommGrpCat.braidedCategory
  AddCommGrpCat.monoidalClosed MonoidalClosed.enrichedOrdinaryCategorySelf

/-- **The tensor product of abelian sheaves on a topological space.** -/
@[instance_reducible] def abelianSheafMonoidalCategory (X : TopCat.{u}) :
    MonoidalCategory (AbelianSheaf X) :=
  Sheaf.monoidalCategory _ _

attribute [local instance] abelianSheafMonoidalCategory

/-- The tensor product of abelian sheaves is braided. -/
@[instance_reducible] def abelianSheafBraidedCategory (X : TopCat.{u}) :
    BraidedCategory (AbelianSheaf X) :=
  Sheaf.braidedCategory _ _

/-- Sheafification is a monoidal functor for this tensor product. -/
instance presheafToSheafMonoidal (X : TopCat.{u}) :
    (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).Monoidal :=
  inferInstance

/-- **The constant sheaf functor is monoidal** for the tensor product of abelian sheaves. -/
instance constantSheafMonoidal (X : TopCat.{u}) :
    (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).Monoidal :=
  inferInstanceAs ((Functor.const (Opens X)ᵒᵖ ⋙
    presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).Monoidal)

/-- **Sections of an abelian sheaf over the whole space are lax monoidal**: there are canonical
maps `Γ(X, F) ⊗ Γ(X, G) ⟶ Γ(X, F ⊗ G)`, natural in both variables and compatible with the
associators and the units. -/
instance sectionsTopLaxMonoidal (X : TopCat.{u}) :
    (sectionsFunctor X ⊤).LaxMonoidal :=
  (constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u}
    (T := (⊤ : Opens X)) isTerminalTop).rightAdjointLaxMonoidal

end Stacks.Cohomology.Leray

end
