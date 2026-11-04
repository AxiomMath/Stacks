module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.CompositeRightDerivedFunctors
import StacksCore.Tactic.StacksAttribute

/-!
# Cohomology of an abelian sheaf over an object, from an injective resolution

Let `(C, J)` be a site, `U` an object of `C` and `F` an abelian sheaf on `C`. The category of
abelian sheaves on `C` has enough injectives, so `F` has an injective resolution
`F[0] → I^•`. The `i`-th cohomology group of `F` over `U` is
`H^i(U, F) = H^i(Γ(U, I^•))`; in other words, `H^i(U, -)` is the `i`-th right derived functor
of the sections functor `Γ(U, -) : F ↦ F(U)`.

In this library `Γ(U, -)` is `Stacks.Cohomology.CompositeRightDerived.sections J U` and its
`i`-th right derived functor is `Stacks.Cohomology.CompositeRightDerived.cohomology J U i`.
This file records the displayed equation: for *any* injective resolution `I` of `F`, the
group `H^i(U, F)` is canonically the `i`-th cohomology of the complex of sections
`Γ(U, I^•)`. The identification is natural in the sheaf and in a compatible map of
resolutions, which is what makes it independent of the resolution chosen.

## Main results

* `Stacks.Cohomology.SectionCohomology.cohomologyIso`: `H^i(U, F) ≅ H^i(Γ(U, I^•))`.
* `Stacks.Cohomology.SectionCohomology.cohomologyIso_hom_naturality`: its naturality.

## Implementation notes

The source works with sheaves of abelian groups on a site, with no ring of coefficients; the
sheaf-of-modules version over a ringed site, where `H^i(U, F)` is an `O(U)`-module, is a
different statement and is not treated here. The site is a small category and the abelian
groups live in the same universe, which is the setting in which the category of abelian
sheaves is a Grothendieck abelian category and so has enough injectives.

## References

* [Stacks Project, Tag 071C](https://stacks.math.columbia.edu/tag/071C)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace Stacks.Cohomology.SectionCohomology

open Stacks.Cohomology.CompositeRightDerived

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)

/-- **Stacks Project, Tag 071C.** The source's displayed equation: the `i`-th cohomology group
`H^i(U, F)` of an abelian sheaf `F` over an object `U` of the site, the `i`-th right derived
functor of the sections functor `Γ(U, -)` evaluated at `F`, is canonically the `i`-th
cohomology of the complex of sections `Γ(U, I^•)` of any injective resolution `I` of `F`. -/
@[stacks 071C "H^i(U, F) = H^i(Γ(U, I^•)) for any injective resolution F[0] → I^•"]
def cohomologyIso (U : C) (F : Sheaf J Ab.{u}) (I : InjectiveResolution F) (i : ℕ) :
    (cohomology J U i).obj F ≅
      (((sections J U).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).homology i :=
  I.isoRightDerivedObj (sections J U) i

/-- The identification of `cohomologyIso` is natural in the sheaf and in a compatible map of
injective resolutions. -/
@[reassoc]
theorem cohomologyIso_hom_naturality (U : C) {F G : Sheaf J Ab.{u}} (f : F ⟶ G)
    (I : InjectiveResolution F) (K : InjectiveResolution G)
    (φ : I.cocomplex ⟶ K.cocomplex) (comm : I.ι.f 0 ≫ φ.f 0 = f ≫ K.ι.f 0) (i : ℕ) :
    (cohomology J U i).map f ≫ (cohomologyIso J U G K i).hom =
      (cohomologyIso J U F I i).hom ≫
        ((sections J U).mapHomologicalComplex (ComplexShape.up ℕ) ⋙
          HomologicalComplex.homologyFunctor _ _ i).map φ :=
  InjectiveResolution.isoRightDerivedObj_hom_naturality f I K φ comm (sections J U) i

end Stacks.Cohomology.SectionCohomology
