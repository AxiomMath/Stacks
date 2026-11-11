module

public import Mathlib.CategoryTheory.Sites.ConcreteSheafification
public import StacksCore.Tactic.StacksAttribute

/-! # The universal property of `F^# = F^{++}`

Stacks tag 00WH: for a presheaf `F` and a sheaf `Q`, every map `η : F ⟶ Q` factors uniquely
through the canonical map `F ⟶ F^#` as `F ⟶ F^# ⟶ Q`. Here `F^#` is the concrete construction
`F^{++}` of tag 00WG, Mathlib's `CategoryTheory.GrothendieckTopology.sheafify` (`plusObj` applied
twice) with the canonical map `CategoryTheory.GrothendieckTopology.toSheafify`.

`existsUnique_toSheafify_comp` states the whole tag as one declaration, from Mathlib's
`CategoryTheory.GrothendieckTopology.sheafifyLift` (the map `γ`),
`CategoryTheory.GrothendieckTopology.toSheafify_sheafifyLift` (the factorization) and
`CategoryTheory.GrothendieckTopology.sheafifyLift_unique` (its uniqueness), which are registered
here for the same tag.

## Implementation notes

`StacksCore/CategoryTheory/Sites/Sheafification/SheafificationAdjoint.lean` also registers 00WH, for
Mathlib's abstract sheafification `CategoryTheory.sheafifyLift`,
`CategoryTheory.toSheafify_sheafifyLift` and `CategoryTheory.sheafifyLift_unique`, whose `F^#`
is not the `F^{++}` of 00WG. Those lines are in the promoted library, which this draft module may
not change, so they stay as they are; the registrations below are the ones that match 00WG.

## References

* [Stacks Project, Tag 00WG](https://stacks.math.columbia.edu/tag/00WG)
* [Stacks Project, Tag 00WH](https://stacks.math.columbia.edu/tag/00WH)
-/

@[expose] public section

add_to_stacks 00WH "the lift `γ : F^{++} ⟶ Q` of a map `η : F ⟶ Q` into a sheaf"
  CategoryTheory.GrothendieckTopology.sheafifyLift
add_to_stacks 00WH "the lift factors `η` through the canonical map `F ⟶ F^{++}`"
  CategoryTheory.GrothendieckTopology.toSheafify_sheafifyLift
add_to_stacks 00WH "the lift is the unique such factorization"
  CategoryTheory.GrothendieckTopology.sheafifyLift_unique

namespace CategoryTheory.GrothendieckTopology

universe w' w v u

open Limits

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable {D : Type w} [Category.{w'} D]
variable [∀ (P : Cᵒᵖ ⥤ D) (X : C) (S : J.Cover X), HasMultiequalizer (S.index P)]
  [∀ X : C, HasColimitsOfShape (J.Cover X)ᵒᵖ D]

/-- Every map `η : P ⟶ Q` from a presheaf to a sheaf factors uniquely through the canonical map
`P ⟶ P^{++}` (`J.toSheafify P`). -/
@[stacks 00WH]
theorem existsUnique_toSheafify_comp {P Q : Cᵒᵖ ⥤ D} (hQ : Presheaf.IsSheaf J Q) (η : P ⟶ Q) :
    ∃! γ : J.sheafify P ⟶ Q, J.toSheafify P ≫ γ = η :=
  ⟨J.sheafifyLift η hQ, J.toSheafify_sheafifyLift η hQ,
    fun γ h => J.sheafifyLift_unique η hQ γ h⟩

end CategoryTheory.GrothendieckTopology
