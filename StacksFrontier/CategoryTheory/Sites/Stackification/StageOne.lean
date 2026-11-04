module

public import StacksFrontier.CategoryTheory.Sites.Stackification.MorQuotientSeparated

/-! # What the first stage of the stackification delivers

This file collects, in the shape the two later stages will consume them, the statements about
`CategoryTheory.Functor.toMorQuotient` that correspond to the two clauses of Stacks 02ZN.

At this stage both clauses hold in a degenerate but useful form.

* Clause (2) — every object of the stackification is *locally* in the essential image — holds
  with the trivial covering: the quotient functor is the identity on objects, so every object
  of `MorQuotient p J` is *globally* in the essential image, by an isomorphism lying over an
  identity. See `CategoryTheory.Functor.exists_isHomLift_id_iso_toMorQuotient_obj`.

* Clause (1) — the map on morphism presheaves exhibits the target as the sheafification of the
  source — does **not** hold yet, and cannot: this stage constructs the *separated quotient* of
  the morphism presheaves, not their sheafification. What does hold is the exact pair of
  statements that identify a separated quotient: the map on morphism sets is surjective
  (`CategoryTheory.Functor.toMorQuotient_map_surjective`), it identifies precisely the locally
  equal morphisms (`CategoryTheory.Quotient.functor_map_eq_iff`), and the result is
  separated (`CategoryTheory.Functor.locallyEqual_morQuotientProj_iff`). Turning a separated
  presheaf into a sheaf is what the second stage — adjoining locally defined morphisms — is
  for, and it is not done here.

## Obligations that remain before Stacks 02ZN

The following are **not** proved anywhere in this directory, and no declaration here should be
read as claiming them.

1. Stage two: the category with the same objects as `𝒳` and locally defined morphisms as
   morphisms, its composition, the check that it is a category over the base, that the
   functor to it preserves strongly cartesian morphisms and that it is fibred, and the
   identification of its morphism presheaves with the sheafifications of the separated
   morphism presheaves produced by stage one.
2. Stage three: the category of pairs (covering sieve, descent datum), its morphisms, the
   eight verifications the source lists and omits, and in particular that the result is a
   stack in the sense of `CategoryTheory.Functor.IsStack`.
3. The composite 1-morphism `G : 𝒮 ⥤ 𝒮'` and clauses (1) and (2) of 02ZN for it.
4. Uniqueness of the stackification up to unique 2-isomorphism.
5. Stacks 0435 (the universal property), 02ZP, 0436, 04W9, 04Y1, 04Y2.
-/

@[expose] public section

universe v₁ u₁ v₂ u₂

namespace CategoryTheory.Functor

open CategoryTheory Category

variable {𝒮 : Type u₁} {𝒳 : Type u₂} [Category.{v₁} 𝒮] [Category.{v₂} 𝒳]

variable {p : 𝒳 ⥤ 𝒮} {J : GrothendieckTopology 𝒮}

/-- The quotient functor is essentially surjective, being the identity on objects. -/
instance essSurj_toMorQuotient : (p.toMorQuotient J).EssSurj :=
  CategoryTheory.Quotient.essSurj_functor _

/-- **Clause (2) of Stacks 02ZN for the first stage, with the trivial covering.** Every object
of the quotient category is in the essential image of the quotient functor, by an isomorphism
lying over an identity of the base — indeed the quotient functor is the identity on objects,
so no covering is needed at all.

This is stated in the shape required by
`CategoryTheory.Functor.IsFibredOneMorphism.of_fullyFaithful`. -/
theorem exists_isHomLift_id_iso_toMorQuotient_obj (A : p.MorQuotient J) :
    ∃ (x : 𝒳) (e : (p.toMorQuotient J).obj x ≅ A),
      (p.morQuotientProj J).IsHomLift (𝟙 ((p.morQuotientProj J).obj A)) e.hom :=
  ⟨A.as, Iso.refl _, IsHomLift.id rfl⟩

/-- **The morphism map of the first stage is surjective.** Together with
`CategoryTheory.Quotient.functor_map_eq_iff` this says that the morphism sets of the
quotient are exactly the quotients of those of `𝒳` by local equality; and together with
`CategoryTheory.Functor.locallyEqual_morQuotientProj_iff` that they are separated.

This is *not* clause (1) of Stacks 02ZN: a separated quotient is not a sheafification. -/
theorem toMorQuotient_map_surjective {x y : 𝒳}
    (F : (p.toMorQuotient J).obj x ⟶ (p.toMorQuotient J).obj y) :
    ∃ a : x ⟶ y, (p.toMorQuotient J).map a = F :=
  exists_eq_toMorQuotient_map F

end CategoryTheory.Functor
