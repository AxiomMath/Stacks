module

public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack.Defs

/-!
# Full subcategories and isomorphism over the identity

A subcategory of `𝒳` is modelled by an `ObjectProperty` `P` on `𝒳`; the associated full
subcategory is `P.FullSubcategory`, and the restricted structure functor is `P.ι ⋙ p`.

An object `y` of `𝒳` can be isomorphic to an object with property `P` in two senses:

* plainly, `P.isoClosure y`: some isomorphism `y ≅ y'` of `𝒳` with `P y'`;
* over the identity, `CategoryTheory.Functor.IsoOverId`: such an isomorphism lying over
  `𝟙 (p.obj y)`, i.e. an isomorphism of the fibre of `p` over `p.obj y`.

The second implies the first, and asking that the isomorphism lie over *some* isomorphism of the
base gives the first again. The two agree when `P` is closed under isomorphisms.

## Main definitions

* `CategoryTheory.Functor.restrict`, the restriction of `p` to the full subcategory cut out by `P`;
* `CategoryTheory.Functor.IsoOverId`: `y` is isomorphic over the identity to an object with
  property `P`.

## Main results

* `CategoryTheory.Functor.isoClosure_iff_exists_isHomLift`: an isomorphism to an object with
  property `P` can always be taken to lie over an isomorphism of the base.
* `CategoryTheory.Functor.isoOverId_iff_isoClosure`: the two senses agree when `P` is closed
  under isomorphisms.
-/

@[expose] public section

namespace CategoryTheory

open Limits Opposite

universe v₁ v₂ u₁ u₂

namespace Functor

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒳 : Type u₂} [Category.{v₂} 𝒳]

/-- The restriction of `p : 𝒳 ⥤ 𝒮` to the full subcategory of `𝒳` cut out by `P`. -/
abbrev restrict (p : 𝒳 ⥤ 𝒮) (P : ObjectProperty 𝒳) : P.FullSubcategory ⥤ 𝒮 := P.ι ⋙ p

/-- `y` is isomorphic over the identity to an object with property `P`, i.e. isomorphic to one in
the fibre of `p` over `p.obj y`. -/
def IsoOverId (p : 𝒳 ⥤ 𝒮) (P : ObjectProperty 𝒳) (y : 𝒳) : Prop :=
  ∃ y' : 𝒳, P y' ∧ ∃ e : y ≅ y', p.IsHomLift (𝟙 (p.obj y)) e.hom

/-- An object with property `P` is isomorphic over the identity to an object with property `P`,
namely to itself. -/
lemma isoOverId_of_prop {p : 𝒳 ⥤ 𝒮} {P : ObjectProperty 𝒳} {y : 𝒳} (hy : P y) :
    IsoOverId p P y :=
  ⟨y, hy, Iso.refl y, IsHomLift.id rfl⟩

/-- An object isomorphic over the identity to an object with property `P` is isomorphic to an
object with property `P`. -/
lemma isoClosure_of_isoOverId {p : 𝒳 ⥤ 𝒮} {P : ObjectProperty 𝒳} {y : 𝒳}
    (h : IsoOverId p P y) : P.isoClosure y :=
  have ⟨y', hy', e, _⟩ := h
  ⟨y', hy', ⟨e⟩⟩

/-- `y` is isomorphic to an object with property `P` if and only if it is so by an isomorphism
lying over some isomorphism of the base. -/
lemma isoClosure_iff_exists_isHomLift (p : 𝒳 ⥤ 𝒮) (P : ObjectProperty 𝒳) (y : 𝒳) :
    P.isoClosure y ↔
      ∃ (y' : 𝒳) (_ : P y') (e : y ≅ y') (α : p.obj y ≅ p.obj y'), p.IsHomLift α.hom e.hom :=
  ⟨fun ⟨y', hy', ⟨e⟩⟩ =>
      ⟨y', hy', e, p.mapIso e, inferInstanceAs (p.IsHomLift (p.map e.hom) e.hom)⟩,
    fun ⟨y', hy', e, _, _⟩ => ⟨y', hy', ⟨e⟩⟩⟩

/-- For a subcategory closed under isomorphism, being isomorphic over the identity to an object of
the subcategory is being an object of the subcategory. -/
lemma isoOverId_iff_prop (p : 𝒳 ⥤ 𝒮) (P : ObjectProperty 𝒳) [P.IsClosedUnderIsomorphisms]
    (y : 𝒳) : IsoOverId p P y ↔ P y :=
  ⟨fun ⟨_, hy', e, _⟩ => P.prop_of_iso e.symm hy', isoOverId_of_prop⟩

/-- For `P` closed under isomorphisms, `y` is isomorphic over the identity to an object with
property `P` if and only if it is isomorphic to one. -/
lemma isoOverId_iff_isoClosure (p : 𝒳 ⥤ 𝒮) (P : ObjectProperty 𝒳)
    [P.IsClosedUnderIsomorphisms] (y : 𝒳) : IsoOverId p P y ↔ P.isoClosure y :=
  ⟨isoClosure_of_isoOverId, fun ⟨_, hy', ⟨e⟩⟩ => isoOverId_of_prop (P.prop_of_iso e.symm hy')⟩

end Functor

end CategoryTheory
