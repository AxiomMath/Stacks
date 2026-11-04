module

public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering

/-!
# Postcomposition of sheaves preserves monomorphisms

`CategoryTheory.sheafCompose J F` postcomposes a sheaf with a functor `F` between the
coefficient categories. This file records that it *preserves* monomorphisms as soon as `F`
does.

Mathlib has the two halves separately but not the composite statement: `sheafCompose J F` is
faithful when `F` is (`CategoryTheory.instFaithfulSheafCompose`), hence *reflects*
monomorphisms, and `Mathlib/CategoryTheory/Limits/FunctorCategory/EpiMono.lean` has that
whiskering on the right by a monomorphism-preserving functor preserves monomorphisms of
*presheaves*. Reflecting is the direction full faithfulness gives; preserving does not follow
from it, and the point of this file is that it does not need a description of the
monomorphisms of either sheaf category either.

## Main results

* `CategoryTheory.sheafCompose_preservesMonomorphisms`: if `F` preserves monomorphisms then
  so does `CategoryTheory.sheafCompose J F`.

## Implementation notes

The proof is the composite of three facts, none of which inspects what a monomorphism of
sheaves is. `CategoryTheory.sheafToPresheaf` creates limits of any shape the coefficient
category has (`CategoryTheory.sheafToPresheaf.createsLimitsOfShape`), so for the shape
`WalkingCospan` it both preserves and reflects fibre squares; a morphism is a monomorphism
exactly when its fibre square with itself has equal projections; so `sheafToPresheaf`
preserves and reflects monomorphisms. On presheaves `sheafCompose J F` is whiskering on the
right by `F`, which preserves monomorphisms objectwise. Hence the hypothesis is
`HasLimitsOfShape WalkingCospan A` on the source coefficient category and nothing on the
target: fibre squares are only ever needed on the side the monomorphism starts on.

`Mono` is reflected rather than transported by hand because
`CategoryTheory.Sheaf.Hom.mono_of_presheaf_mono` is exactly the fully-faithful reflection
and is already in Mathlib.
-/

@[expose] public section

open CategoryTheory.Functor CategoryTheory.Limits

namespace CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {A : Type*} [Category A] {B : Type*} [Category B] (F : A ⥤ B)
  [J.HasSheafCompose F] [HasLimitsOfShape WalkingCospan A] [F.PreservesMonomorphisms]

/-- Postcomposing sheaves with a functor that preserves monomorphisms preserves
monomorphisms. On underlying presheaves `CategoryTheory.sheafCompose` is whiskering on the
right by `F`, which preserves monomorphisms objectwise, and
`CategoryTheory.sheafToPresheaf` both preserves monomorphisms (it creates fibre squares) and
reflects them (it is fully faithful). -/
instance sheafCompose_preservesMonomorphisms :
    (sheafCompose J F).PreservesMonomorphisms where
  preserves {_ _} φ _ := (sheafToPresheaf J B).mono_of_mono_map
    (inferInstanceAs (Mono (whiskerRight ((sheafToPresheaf J A).map φ) F)))

end CategoryTheory

end
