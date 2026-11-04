module

public import StacksFrontier.Homology.DerivedCategory.ModelComparisonTransport
public import StacksFrontier.RingTheory.Dualizing.CoextendRestrictComparison.Constructed

/-!
# `RHom_A(B, -)` read at the two models of `D(Mod A)`

The repository runs two models of the derived category of modules side by side: the locally small
one of [Stacks, Tag 079Q], `ModuleCat.hasDerivedCategory`, activated file-locally, with
morphisms in `Type u`, and `CategoryTheory.HasDerivedCategory.standard`, installed file-locally,
with morphisms in `Type (u + 1)`. Derived Hom along a ring homomorphism is available at both:
`Dualizing.derivedHom` of `…/RingTheory/Dualizing/TrivialDuality.lean` is pinned to the standard
model, and `Dualizing.AnyModel.derivedHom` of `…/RingTheory/Dualizing/DerivedHomAnyModel.lean`
takes the two models as parameters — and at the standard model the two are the *same* functor, by
`Dualizing.AnyModel.derivedHom_eq_standard`.

This file compares the two readings. The need for it is concrete: [Stacks, Tag 0A9F] at the
twisted inverse image (`AlgebraicGeometry.twistedInverseImage_spec_isoDerivedHom`) is stated
against the locally small reading, because the adjunction of [Stacks, Tag 0A9E] it rests on comes
from Brown representability, which needs local smallness; while the normalization convention of
[Stacks, Tag 0A7M] that evaluates `RHom_A(κ, ω_A^•)` — `Dualizing.IsNormalizedDualizingComplex` —
is stated against the standard model, `Dualizing.derivedHom` having that model baked into its
type.

## Main definitions

* `Dualizing.AnyModel.derivedHomModelIso` — `RHom_A(B, -)` taken at the standard model and
  `RHom_A(B, -)` taken at the locally small model agree up to the comparison equivalences on
  source and target.

## Main results

* `Dualizing.AnyModel.nonempty_derivedHom_locallySmall_iso_of_standard_iso` — an isomorphism
  `RHom_A(B, K) ≅ L` at the standard model gives one at the locally small model. The objects need
  no transport: by `StacksDraft.DerivedModel.derivedCategory_eq_standard` the two models have the
  same objects, and the comparison equivalence is the identity on them.

## How the transport is obtained

`Dualizing.AnyModel.derivedHom` is, at *every* pair of models, the total right derived functor of
one and the same functor out of the homotopy category, `Dualizing.coextendScalarsToDerivedCategory`
followed by localization; its universal property for its own total-derived unit
`Dualizing.AnyModel.derivedHomUnit` is the instance
`Dualizing.AnyModel.derivedHom_isRightDerivedFunctor`. So
`StacksDraft.DerivedModel.rightDerivedModelIso` — a total right derived functor transported across
a comparison of models of its source and of its target — applies with no new duality input, and
the two comparisons it asks for are `StacksDraft.DerivedModel.shrinkComparisonQhIso` at
`ModuleCat A` and at `ModuleCat B`. This is `StacksDraft.DerivedModel.derivedPushforwardModelIso`
with `Rf_*` replaced by `RHom_A(B, -)`, and it is written in the same shape.

## Implementation notes

*Where this belongs.* The transport itself is generic and would sit beside
`StacksDraft.DerivedModel.derivedPushforwardModelIso` in
`…/Homology/DerivedCategory/ModelComparisonTransport.lean`; it lives here because that file
mentions no ring and importing `…/RingTheory/Dualizing/` into it would reverse the dependency.
Nothing below is specific to the dualizing application.

*Universes.* Both rings are taken in a single universe `u` and the modules in `Type u`, which is
the only setting in which the two models can be compared at all: the locally small model of
`ModuleCat.{max v u} A` has morphisms in `max v u` and the comparison equivalence
`Stacks.Injectives.grothendieckModelEquiv` is stated for a category locally small in its own
Grothendieck universe. This is also the setting [Stacks, Tag 0A9F] pins, its universes being
literally `u` throughout.

*Models are named, never searched.* Importing
`…/Homology/DerivedCategory/ModelComparisonTransport.lean` brings the global locally small
instances into scope, so every `HasDerivedCategory` argument below is spelled out — as
`CategoryTheory.HasDerivedCategory.standard` or as
`Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian` — and none is left to instance
search. This is the discipline that file's implementation notes ask of its consumers.

*No `@[stacks]` attribute.* The source has nothing to say here: a comparison of two Lean choices
of localization is an artefact of formalizing the derived category, not a statement about two
mathematical objects. The tags in the chain are carried where they belong — [Stacks, Tag 079Q] by
`Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian` and [Stacks, Tag 0A70] by
`Dualizing.AnyModel.restrictScalarsDerived_adj_derivedHom`.

## References

* [Stacks Project, Tag 079Q](https://stacks.math.columbia.edu/tag/079Q)
* [Stacks Project, Tag 0A70](https://stacks.math.columbia.edu/tag/0A70)
* [Stacks Project, Tag 0A7M](https://stacks.math.columbia.edu/tag/0A7M)
* [Stacks Project, Tag 0A9F](https://stacks.math.columbia.edu/tag/0A9F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor

universe u

namespace Dualizing.AnyModel

variable {A B : Type u} [CommRing A] [CommRing B]

/-- **`RHom_A(B, -)` read at the two models of the derived category.** Derived coextension of
scalars taken at `CategoryTheory.HasDerivedCategory.standard` and taken at the locally small model
of [Stacks, Tag 079Q] agree up to the comparison equivalences on source and target. Both are total
right derived functors of `Dualizing.coextendScalarsToDerivedCategory`, and a total right derived
functor is unique up to a canonical isomorphism.

This is `StacksDraft.DerivedModel.derivedPushforwardModelIso` with `Rf_*` replaced by
`RHom_A(B, -)`. -/
def derivedHomModelIso (f : A →+* B) :
    @derivedHom.{u, u, u, u + 1, u + 1} A B _ _
          (HasDerivedCategory.standard (ModuleCat.{u} A))
          (HasDerivedCategory.standard (ModuleCat.{u} B)) f ⋙
        (Stacks.Injectives.grothendieckModelEquiv.{u} (ModuleCat.{u} B)).functor ≅
      (Stacks.Injectives.grothendieckModelEquiv.{u} (ModuleCat.{u} A)).functor ⋙
        @derivedHom.{u, u, u, u, u} A B _ _
          (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} (ModuleCat.{u} A))
          (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} (ModuleCat.{u} B))
          f :=
  StacksDraft.DerivedModel.rightDerivedModelIso
    (HomotopyCategory.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ))
    (@derivedHomUnit.{u, u, u + 1, u + 1} A B _ _
      (HasDerivedCategory.standard (ModuleCat.{u} A))
      (HasDerivedCategory.standard (ModuleCat.{u} B)) f)
    (@derivedHomUnit.{u, u, u, u} A B _ _
      (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} (ModuleCat.{u} A))
      (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} (ModuleCat.{u} B)) f)
    (StacksDraft.DerivedModel.shrinkComparisonQhIso (ModuleCat.{u} A)).symm
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _
        (StacksDraft.DerivedModel.shrinkComparisonQhIso (ModuleCat.{u} B)).symm)

/-- **An isomorphism `RHom_A(B, K) ≅ L` at the standard model gives one at the locally small
model.** The two models have the same objects, by
`StacksDraft.DerivedModel.derivedCategory_eq_standard`, and the comparison equivalence is the
identity on them (`Stacks.Injectives.grothendieckModelEquiv_functor_obj`), so `K` and `L` are
read unchanged on the other side; only the morphisms are transported, which is
`Dualizing.AnyModel.derivedHomModelIso`.

This is the step that lets the normalization convention of [Stacks, Tag 0A7M], stated at the
standard model, be consumed by [Stacks, Tag 0A9F], stated at the locally small one. -/
theorem nonempty_derivedHom_locallySmall_iso_of_standard_iso (f : A →+* B)
    (K : @DerivedCategory (ModuleCat.{u} A) _ _ (HasDerivedCategory.standard (ModuleCat.{u} A)))
    (L : @DerivedCategory (ModuleCat.{u} B) _ _ (HasDerivedCategory.standard (ModuleCat.{u} B)))
    (e : (@derivedHom.{u, u, u, u + 1, u + 1} A B _ _
        (HasDerivedCategory.standard (ModuleCat.{u} A))
        (HasDerivedCategory.standard (ModuleCat.{u} B)) f).obj K ≅ L) :
    Nonempty ((@derivedHom.{u, u, u, u, u} A B _ _
        (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} (ModuleCat.{u} A))
        (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} (ModuleCat.{u} B))
        f).obj K ≅ L) :=
  ⟨((derivedHomModelIso f).app K).symm ≪≫
    (Stacks.Injectives.grothendieckModelEquiv.{u} (ModuleCat.{u} B)).functor.mapIso e⟩

end Dualizing.AnyModel

end
