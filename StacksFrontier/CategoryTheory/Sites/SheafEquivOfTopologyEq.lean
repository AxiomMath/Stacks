module

public import Mathlib.CategoryTheory.Sites.Sheaf

/-!
# Sheaves for equal Grothendieck topologies

Two Grothendieck topologies on a category which are equal but not definitionally equal have the
same sheaves. This file records the equivalence of sheaf categories, built so that it does not
change the underlying presheaf of a sheaf, which a transport along the equality by `Eq.mp` or by
`cases` would only do propositionally.

## Main definitions

* `CategoryTheory.sheafEquivOfTopologyEq`: the equivalence `Sheaf J A ≌ Sheaf K A` for `J = K`.

## Implementation notes

Both functors are the inclusions `ObjectProperty.ιOfLE` of full subcategories of presheaves, so
`((sheafEquivOfTopologyEq h A).functor.obj F).obj = F.obj` holds by `rfl`, and so do the unit
and the counit.
-/

@[expose] public section

namespace CategoryTheory

/-- Sheaves for two equal Grothendieck topologies are the same: the equivalence leaves the
underlying presheaf of every sheaf unchanged. -/
def sheafEquivOfTopologyEq {C : Type*} [Category C] {J K : GrothendieckTopology C} (h : J = K)
    (A : Type*) [Category A] : Sheaf J A ≌ Sheaf K A where
  functor := ObjectProperty.ιOfLE fun _ hF ↦ h ▸ hF
  inverse := ObjectProperty.ιOfLE fun _ hF ↦ h ▸ hF
  unitIso := Iso.refl _
  counitIso := Iso.refl _

end CategoryTheory
