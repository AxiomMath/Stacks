module

public import Mathlib.CategoryTheory.Limits.HasLimits
public import StacksCore.Tactic.StacksAttribute

/-!
# Limits and colimits are unique up to unique isomorphism

Stacks Definition 4.14.1 (Tag 002E) defines the limit of a diagram `F : J ⥤ C` and remarks
that limits are unique up to unique isomorphism; Definition 4.14.2 (Tag 002F) does the same
for colimits. Mathlib's `IsLimit.uniqueUpToIso` gives an isomorphism between two limit cones;
here we record that it is the only one, and dually for colimit cocones.

## Main results

* `CategoryTheory.Limits.IsLimit.nonempty_unique_iso`: between two limit cones over the same
  diagram there is exactly one isomorphism of cones.
* `CategoryTheory.Limits.IsColimit.nonempty_unique_iso`: between two colimit cocones under the
  same diagram there is exactly one isomorphism of cocones.
-/

@[expose] public section

namespace CategoryTheory.Limits

variable {J C : Type*} [Category* J] [Category* C] {F : J ⥤ C}

/-- Two limit cones over the same diagram are isomorphic by exactly one isomorphism of cones:
the isomorphism `IsLimit.uniqueUpToIso hs ht`, and any other is equal to it. -/
@[stacks 002E "limits are unique up to unique isomorphism"]
theorem IsLimit.nonempty_unique_iso {s t : Cone F} (hs : IsLimit s) (ht : IsLimit t) :
    Nonempty (Unique (s ≅ t)) :=
  ⟨{ default := hs.uniqueUpToIso ht
     uniq := fun _ ↦ Iso.ext ht.uniq_cone_morphism }⟩

/-- Two colimit cocones under the same diagram are isomorphic by exactly one isomorphism of
cocones: the isomorphism `IsColimit.uniqueUpToIso hs ht`, and any other is equal to it. -/
@[stacks 002F "colimits are unique up to unique isomorphism"]
theorem IsColimit.nonempty_unique_iso {s t : Cocone F} (hs : IsColimit s) (ht : IsColimit t) :
    Nonempty (Unique (s ≅ t)) :=
  ⟨{ default := hs.uniqueUpToIso ht
     uniq := fun _ ↦ Iso.ext hs.uniq_cocone_morphism }⟩

end CategoryTheory.Limits
