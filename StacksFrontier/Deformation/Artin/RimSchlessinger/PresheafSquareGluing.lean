module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Yoneda

/-!
# Gluing sections of a presheaf at a square

A presheaf of types *glues* at a commutative square of its base when a pair of sections over the
two middle corners of the square which agree over the initial corner comes from exactly one
section over the terminal corner. This file names that property and records the three ways it
transports, which are what a consumer holding the property for one presheaf and wanting it for
another needs:

* along a natural family of bijections, hence along an isomorphism of presheaves, and hence along
  an isomorphism of presheaves after universe lifts — the shape in which condition (2) of
  [Stacks Project, Tag 045G] delivers an algebraic space isomorphic to an isomorphism sheaf;
* along an isomorphism of the functor whose image the square is taken to be — the shape in which
  a square of a slice category is compared with its image under
  `CategoryTheory.Over.iteratedSliceForward` followed by
  `CategoryTheory.Over.iteratedSliceBackward`.

## Main definitions

* `Deformation.Artin.PresheafGluesAt` — the gluing property.

## Main results

* `Deformation.Artin.PresheafGluesAt.of_equiv` — transport along a natural family of bijections.
* `Deformation.Artin.PresheafGluesAt.of_natIso` — transport along an isomorphism of presheaves.
* `Deformation.Artin.presheafGluesAt_uliftFunctor_iff` — the property is insensitive to a universe
  lift of the values.
* `Deformation.Artin.PresheafGluesAt.of_uliftIso` — transport along an isomorphism of presheaves
  that holds only after universe lifts.
* `Deformation.Artin.presheafGluesAt_comp_op` — the property for a presheaf precomposed with a
  functor is the property for the presheaf at the image square.
* `Deformation.Artin.PresheafGluesAt.of_natIsoFunctor` — transport along an isomorphism of the
  functor taking the square.

## Implementation notes

The property is stated as an `ExistsUnique` rather than as an `IsPullback` of types because that
is the shape both of its producer,
`AlgebraicGeometry.Space.existsUnique_section_of_isThickening_of_isAffineHom`, and of its
consumers, which read the uniqueness half as faithfulness and the existence half as fullness of a
comparison functor.

The source and target presheaves of `Deformation.Artin.PresheafGluesAt.of_equiv` take values in
independent universes, so that the lemma also serves the universe-lift transport; `Equiv` is
already cross-universe.

`Deformation.Artin.presheafGluesAt_comp_op` is `Iff.rfl`: the two sides are the same proposition,
because `(E.op ⋙ P).obj (Opposite.op X)` is `P.obj (Opposite.op (E.obj X))` and
`E.op.map i.op` is `(E.map i).op`. It is recorded so that a consumer can move between the two
spellings by rewriting rather than by relying on that.
-/

@[expose] public section

open CategoryTheory Opposite

universe v₁ u₁ w₁ w₂ v₂ u₂

namespace Deformation.Artin

variable {C : Type u₁} [Category.{v₁} C]

/-- A presheaf of types *glues at* the commutative square with sides `i`, `f`, `a`, `b` when a
section over `X'` and a section over `Y` with the same restriction to `X` are the two restrictions
of exactly one section over `Y'`. -/
public def PresheafGluesAt (P : Cᵒᵖ ⥤ Type w₁) {X X' Y Y' : C}
    (i : X ⟶ X') (f : X ⟶ Y) (a : X' ⟶ Y') (b : Y ⟶ Y') : Prop :=
  ∀ (sX' : P.obj (op X')) (sY : P.obj (op Y)),
    P.map i.op sX' = P.map f.op sY →
      ∃! s : P.obj (op Y'), P.map a.op s = sX' ∧ P.map b.op s = sY

/-- **Gluing at a square transports along a natural family of bijections of sections.** -/
public theorem PresheafGluesAt.of_equiv {P : Cᵒᵖ ⥤ Type w₁} {Q : Cᵒᵖ ⥤ Type w₂}
    (e : ∀ T, P.obj T ≃ Q.obj T)
    (he : ∀ {T T' : Cᵒᵖ} (h : T ⟶ T') (s : P.obj T), Q.map h (e T s) = e T' (P.map h s))
    {X X' Y Y' : C} {i : X ⟶ X'} {f : X ⟶ Y} {a : X' ⟶ Y'} {b : Y ⟶ Y'}
    (hP : PresheafGluesAt P i f a b) : PresheafGluesAt Q i f a b := by
  intro tX' tY ht
  obtain ⟨x, rfl⟩ := (e _).surjective tX'
  obtain ⟨y, rfl⟩ := (e _).surjective tY
  simp only [he, (e _).apply_eq_iff_eq] at ht
  exact ((e _).existsUnique_congr fun s => by simp only [he, (e _).apply_eq_iff_eq]).1
    (hP x y ht)

/-- **Gluing at a square transports along an isomorphism of presheaves.** -/
public theorem PresheafGluesAt.of_natIso {P Q : Cᵒᵖ ⥤ Type w₁} (α : P ≅ Q)
    {X X' Y Y' : C} {i : X ⟶ X'} {f : X ⟶ Y} {a : X' ⟶ Y'} {b : Y ⟶ Y'}
    (hP : PresheafGluesAt P i f a b) : PresheafGluesAt Q i f a b :=
  hP.of_equiv (fun T => (α.app T).toEquiv)
    (fun h s => (ConcreteCategory.congr_hom (α.hom.naturality h) s).symm)

/-- **Gluing at a square is insensitive to a universe lift of the values of the presheaf.** -/
public theorem presheafGluesAt_uliftFunctor_iff (P : Cᵒᵖ ⥤ Type w₁)
    {X X' Y Y' : C} (i : X ⟶ X') (f : X ⟶ Y) (a : X' ⟶ Y') (b : Y ⟶ Y') :
    PresheafGluesAt (P ⋙ uliftFunctor.{w₂, w₁}) i f a b ↔ PresheafGluesAt P i f a b :=
  ⟨fun h => h.of_equiv (fun _ => Equiv.ulift) (fun _ _ => rfl),
    fun h => h.of_equiv (fun _ => Equiv.ulift.symm) (fun _ _ => rfl)⟩

/-- **Gluing at a square transports along an isomorphism of presheaves valid after universe
lifts.** -/
public theorem PresheafGluesAt.of_uliftIso {P : Cᵒᵖ ⥤ Type w₁} {Q : Cᵒᵖ ⥤ Type w₂}
    (α : P ⋙ uliftFunctor.{w₂, w₁} ≅ Q ⋙ uliftFunctor.{w₁, w₂})
    {X X' Y Y' : C} {i : X ⟶ X'} {f : X ⟶ Y} {a : X' ⟶ Y'} {b : Y ⟶ Y'}
    (hP : PresheafGluesAt P i f a b) : PresheafGluesAt Q i f a b :=
  (presheafGluesAt_uliftFunctor_iff Q i f a b).1
    (((presheafGluesAt_uliftFunctor_iff P i f a b).2 hP).of_natIso α)

/-- Gluing of a presheaf precomposed with a functor at a square is gluing of the presheaf at the
image square. -/
public theorem presheafGluesAt_comp_op {D : Type u₂} [Category.{v₂} D] (E : D ⥤ C)
    (P : Cᵒᵖ ⥤ Type w₁) {X X' Y Y' : D}
    (i : X ⟶ X') (f : X ⟶ Y) (a : X' ⟶ Y') (b : Y ⟶ Y') :
    PresheafGluesAt (E.op ⋙ P) i f a b ↔
      PresheafGluesAt P (E.map i) (E.map f) (E.map a) (E.map b) :=
  Iff.rfl

/-- **Gluing at the image of a square transports along an isomorphism of the functor taking the
square.** -/
public theorem PresheafGluesAt.of_natIsoFunctor {D : Type u₂} [Category.{v₂} D] {E E' : D ⥤ C}
    (η : E ≅ E') (P : Cᵒᵖ ⥤ Type w₁) {X X' Y Y' : D}
    {i : X ⟶ X'} {f : X ⟶ Y} {a : X' ⟶ Y'} {b : Y ⟶ Y'}
    (hP : PresheafGluesAt P (E.map i) (E.map f) (E.map a) (E.map b)) :
    PresheafGluesAt P (E'.map i) (E'.map f) (E'.map a) (E'.map b) :=
  (presheafGluesAt_comp_op E' P i f a b).1
    (((presheafGluesAt_comp_op E P i f a b).2 hP).of_natIso
      (Functor.isoWhiskerRight (NatIso.op η) P).symm)

end Deformation.Artin

end
