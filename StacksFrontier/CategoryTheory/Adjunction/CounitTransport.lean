module

public import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# The counit of an adjunction at an object presented through an isomorphism

Let `L ⊣ R` be an adjunction.  Its counit is a natural transformation, so its component at an
object `Y` is determined by its component at any object isomorphic to `Y`: conjugating by an
isomorphism `e : Y ≅ Y'` turns `adj.counit.app Y'` into `adj.counit.app Y`.

This is the step a consumer needs whenever the counit is *valued* only at objects of a particular
shape.  Derived adjunctions are the typical case: the counit of
`CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction` is computed by
`…_counit_app_eq` only at an object presented as `DerivedCategory.Q.obj X`, while the occurrences
a composite actually contains are at objects built by other functors, which are merely
*isomorphic* to such a presentation.

## Main results

* `Stacks.Adjunction.counit_app_of_iso`: the component of the counit at `Y`, written with the
  component at `Y'` for any isomorphism `e : Y ≅ Y'`.

## Implementation notes

The statement is naturality of the counit along `e.hom`, solved for the component at the source.
It is stated in the direction a rewrite wants — the component at `Y`, which is the occurrence to
be eliminated, stands alone on the left-hand side.

`CategoryTheory.Adjunction.counit_app_eq_of_iso`, in
`StacksFrontier.Homology.Tor.DerivedChangeOfRingsResolution`, is the same transport under the name
the derived change-of-rings consumers use; it is proved from this one.  What this file adds is a
position in the import graph — `Mathlib.CategoryTheory.Adjunction.Basic` alone — so that the
transport is available below the K-flat resolution, which is where the two derived scalar
equivalences of [stacks 0A63] and [stacks 0E1W] need it.  That file also has the unit
counterpart `CategoryTheory.Adjunction.unit_app_eq_of_iso`, and applies both to [stacks 0GMT] at
a completely arbitrary object:
`CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction_unit_app_eq_of_model`
and `…_counit_app_eq_of_model`.  A consumer wanting the unit or the counit of [stacks 0GMT] away
from a class should reach for those rather than transport by hand.
-/

@[expose] public section

open CategoryTheory

namespace Stacks.Adjunction

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {L : C ⥤ D} {R : D ⥤ C}

/-- **Transport of a counit along an isomorphism of its argument.**  For an adjunction
`adj : L ⊣ R` and an isomorphism `e : Y ≅ Y'`, the component of the counit at `Y` is the component
at `Y'` conjugated by `e`.

So a formula for the counit at objects of one shape determines it at every object isomorphic to
one of that shape. -/
theorem counit_app_of_iso (adj : L ⊣ R) {Y Y' : D} (e : Y ≅ Y') :
    adj.counit.app Y = L.map (R.map e.hom) ≫ adj.counit.app Y' ≫ e.inv := by
  rw [← Category.assoc, ← Functor.comp_map, adj.counit.naturality e.hom, Category.assoc,
    show (𝟭 D).map e.hom ≫ e.inv = 𝟙 Y from e.hom_inv_id]
  exact (Category.comp_id (adj.counit.app Y)).symm

end Stacks.Adjunction
