module

public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Types.Basic

/-!
# Presheaves of subsingletons are determined by their support

A presheaf of types on a category `𝒯` all of whose values are subsingletons is a subobject of the
final presheaf: the only information it carries is, for each object `a` of `𝒯`, whether its value
over `a` is empty. Two such presheaves which are nonempty over the same objects are isomorphic.
The two presheaves may take values in different universes; they are compared after both are
lifted to a common universe.

## Main results

* `CategoryTheory.presheafIsoOfSubsingleton`: two presheaves of subsingletons with the same
  support are isomorphic after a universe lift.
* `CategoryTheory.nonempty_iso_comp_uliftFunctor_of_subsingleton`: the same as a mere existence
  statement.
* `CategoryTheory.equivOfIsoCompUliftFunctor`,
  `CategoryTheory.subsingleton_of_iso_comp_uliftFunctor` and
  `CategoryTheory.nonempty_iff_of_iso_comp_uliftFunctor`: the converse direction. An isomorphism
  of the two lifted presheaves gives a bijection of the values over each object, hence transports
  both subsingletonness and the support from one presheaf to the other.

## Implementation notes

The components of `CategoryTheory.presheafIsoOfSubsingleton` are given by
`CategoryTheory.pickUlift`, a term of a plain function type: a lambda written directly in the
`app` field, whose type is a morphism of `Type`, is elaborated with no expected type for its
argument.
-/

@[expose] public section

universe v u t t'

namespace CategoryTheory

variable {𝒯 : Type u} [Category.{v} 𝒯]

/-- The unique map from a universe-lifted subsingleton to a universe-lifted type that is nonempty
whenever the source is: it sends everything to a chosen element. -/
noncomputable def pickUlift {α : Type t} {β : Type t'} (h : Nonempty α ↔ Nonempty β) :
    ULift.{t', t} α → ULift.{t, t'} β :=
  fun x => ULift.up (h.1 ⟨x.down⟩).some

/-- **Two presheaves of subsingletons with the same support are isomorphic.** The values are
compared after both presheaves are lifted to the universe `max t t'`, so the two may take values
in different universes. -/
noncomputable def presheafIsoOfSubsingleton {P : 𝒯ᵒᵖ ⥤ Type t} {Q : 𝒯ᵒᵖ ⥤ Type t'}
    (hP : ∀ a, Subsingleton (P.obj a)) (hQ : ∀ a, Subsingleton (Q.obj a))
    (h : ∀ a, Nonempty (P.obj a) ↔ Nonempty (Q.obj a)) :
    P ⋙ uliftFunctor.{t', t} ≅ Q ⋙ uliftFunctor.{t, t'} where
  hom :=
    { app := fun a => ↾(pickUlift (h a))
      naturality := fun _ b _ => by
        have := hQ b
        ext _
        exact Subsingleton.elim (α := ULift.{t, t'} (Q.obj b)) _ _ }
  inv :=
    { app := fun a => ↾(pickUlift (h a).symm)
      naturality := fun _ b _ => by
        have := hP b
        ext _
        exact Subsingleton.elim (α := ULift.{t', t} (P.obj b)) _ _ }
  hom_inv_id := by
    ext a _
    have := hP a
    exact Subsingleton.elim (α := ULift.{t', t} (P.obj a)) _ _
  inv_hom_id := by
    ext a _
    have := hQ a
    exact Subsingleton.elim (α := ULift.{t, t'} (Q.obj a)) _ _

/-- **The bijection of values underlying an isomorphism of two lifted presheaves.** An
isomorphism `P ⋙ uliftFunctor ≅ Q ⋙ uliftFunctor` has, over each object, an isomorphism of types
between the two lifted values; stripping the lifts gives a bijection `P.obj a ≃ Q.obj a`. -/
noncomputable def equivOfIsoCompUliftFunctor {P : 𝒯ᵒᵖ ⥤ Type t} {Q : 𝒯ᵒᵖ ⥤ Type t'}
    (e : P ⋙ uliftFunctor.{t', t} ≅ Q ⋙ uliftFunctor.{t, t'}) (a : 𝒯ᵒᵖ) :
    P.obj a ≃ Q.obj a :=
  Equiv.ulift.symm.trans ((e.app a).toEquiv.trans Equiv.ulift)

/-- A presheaf isomorphic, after the universe lifts, to a presheaf of subsingletons is itself a
presheaf of subsingletons. -/
lemma subsingleton_of_iso_comp_uliftFunctor {P : 𝒯ᵒᵖ ⥤ Type t} {Q : 𝒯ᵒᵖ ⥤ Type t'}
    (e : P ⋙ uliftFunctor.{t', t} ≅ Q ⋙ uliftFunctor.{t, t'})
    (hP : ∀ a, Subsingleton (P.obj a)) (a : 𝒯ᵒᵖ) : Subsingleton (Q.obj a) :=
  have := hP a
  (equivOfIsoCompUliftFunctor e a).symm.injective.subsingleton

/-- Two presheaves isomorphic after the universe lifts have the same support. -/
lemma nonempty_iff_of_iso_comp_uliftFunctor {P : 𝒯ᵒᵖ ⥤ Type t} {Q : 𝒯ᵒᵖ ⥤ Type t'}
    (e : P ⋙ uliftFunctor.{t', t} ≅ Q ⋙ uliftFunctor.{t, t'}) (a : 𝒯ᵒᵖ) :
    Nonempty (P.obj a) ↔ Nonempty (Q.obj a) :=
  (equivOfIsoCompUliftFunctor e a).nonempty_congr

/-- The existence form of `CategoryTheory.presheafIsoOfSubsingleton`. -/
lemma nonempty_iso_comp_uliftFunctor_of_subsingleton {P : 𝒯ᵒᵖ ⥤ Type t} {Q : 𝒯ᵒᵖ ⥤ Type t'}
    (hP : ∀ a, Subsingleton (P.obj a)) (hQ : ∀ a, Subsingleton (Q.obj a))
    (h : ∀ a, Nonempty (P.obj a) ↔ Nonempty (Q.obj a)) :
    Nonempty (P ⋙ uliftFunctor.{t', t} ≅ Q ⋙ uliftFunctor.{t, t'}) :=
  ⟨presheafIsoOfSubsingleton hP hQ h⟩

end CategoryTheory

end
