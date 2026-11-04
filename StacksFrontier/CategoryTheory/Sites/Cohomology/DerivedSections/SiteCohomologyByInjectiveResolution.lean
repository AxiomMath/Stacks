module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.CompositeRightDerivedFunctors
import StacksCore.Tactic.StacksAttribute

/-!
# Cohomology of an abelian sheaf on a site, from an injective resolution

Let `(C, J)` be a site and `F` an abelian sheaf on it.
`Stacks.Cohomology.CompositeRightDerived.siteSections J` is the global sections functor
`Γ(C, -)` of the source, the limit over `Cᵒᵖ` of the underlying presheaf, which is
`Mor_{PSh(C)}(e, -)` for `e` the terminal presheaf; and
`Stacks.Cohomology.CompositeRightDerived.siteCohomology J i` is its `i`-th right derived
functor, the `i`-th cohomology group `H^i(C, -)` of the source.

This file records the displayed equation defining that group: for any injective resolution
`F[0] → I^•` of `F`, `H^i(C, F)` is canonically the `i`-th cohomology of the complex of global
sections `Γ(C, I^•)`. The identification is natural in the sheaf and in a compatible map of
resolutions, which is what makes it independent of the resolution chosen.

## Main results

* `Stacks.Cohomology.SiteSections.siteCohomologyIso`: `H^i(C, F) ≅ H^i(Γ(C, I^•))`.
* `Stacks.Cohomology.SiteSections.siteCohomologyIso_hom_naturality`: its naturality.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Cohomology.SiteSections

open Stacks.Cohomology.CompositeRightDerived

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)

/-- **Stacks Project, Tag 071E.** The source's displayed equation: the `i`-th cohomology group
of an abelian sheaf `F` on the site `C` is canonically the `i`-th cohomology of the complex of
global sections of any injective resolution of `F`. -/
@[stacks 071E]
def siteCohomologyIso (F : Sheaf J Ab.{u}) (I : InjectiveResolution F) (i : ℕ) :
    (siteCohomology J i).obj F ≅
      (((siteSections J).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).homology i :=
  I.isoRightDerivedObj (siteSections J) i

/-- The identification of `siteCohomologyIso` is natural in the sheaf and in a compatible map
of injective resolutions. -/
@[reassoc]
theorem siteCohomologyIso_hom_naturality {F G : Sheaf J Ab.{u}} (f : F ⟶ G)
    (I : InjectiveResolution F) (K : InjectiveResolution G)
    (φ : I.cocomplex ⟶ K.cocomplex) (comm : I.ι.f 0 ≫ φ.f 0 = f ≫ K.ι.f 0) (i : ℕ) :
    (siteCohomology J i).map f ≫ (siteCohomologyIso J G K i).hom =
      (siteCohomologyIso J F I i).hom ≫
        ((siteSections J).mapHomologicalComplex (ComplexShape.up ℕ) ⋙
          HomologicalComplex.homologyFunctor _ _ i).map φ :=
  InjectiveResolution.isoRightDerivedObj_hom_naturality f I K φ comm (siteSections J) i

end Stacks.Cohomology.SiteSections
