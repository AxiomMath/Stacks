module

public import StacksFrontier.CategoryTheory.Monoidal.Reseat

/-!
# The tensorator of the re-seating identity functor

`CategoryTheory.MonoidalCategory.reseatMonoidal` makes the identity functor monoidal from the
re-seated structure `CategoryTheory.MonoidalCategory.reseat` to the given one.  Its tensorator is
`CategoryTheory.MonoidalCategory.reseatIso`, the isomorphism `X ⊗ Y ≅ (T.obj X).obj Y` along
which the structure was re-seated; this file records that identification, which is what makes the
re-seated structure's constraints computable.  The constraints themselves are computed in
`StacksFrontier/CategoryTheory/Monoidal/ReseatConstraints.lean`; in particular the re-seated
braiding is `CategoryTheory.MonoidalCategory.reseat_braiding` there.

## Main results

* `CategoryTheory.MonoidalCategory.Functor.id_preimage`: the identity functor's
  `CategoryTheory.Functor.preimage` is the morphism itself.
* `CategoryTheory.MonoidalCategory.reseatMonoidal_μ`: the tensorator of the identity functor
  from the re-seated structure to the given one is `reseatIso`.
-/

@[expose] public section

universe v u

namespace CategoryTheory.MonoidalCategory

open Category

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] {T : C ⥤ C ⥤ C} {U : C}

omit [MonoidalCategory C] in
/-- The identity functor's `Functor.preimage` is the identity. -/
lemma Functor.id_preimage {X Y : C} (f : (𝟭 C).obj X ⟶ (𝟭 C).obj Y) :
    (𝟭 C).preimage f = f :=
  CategoryTheory.Functor.map_preimage (𝟭 C) f

/-- The tensorator of the identity functor from the re-seated structure to the given one is
`reseatIso`. -/
lemma reseatMonoidal_μ (e : curriedTensor C ≅ T) (ε : 𝟙_ C ≅ U) (X Y : C) :
    @Functor.LaxMonoidal.μ C _ (reseat e ε) C _ _ (𝟭 C)
        (@Functor.Monoidal.toLaxMonoidal C _ (reseat e ε) C _ _ (𝟭 C) (reseatMonoidal e ε))
        X Y =
      (reseatIso e X Y).hom :=
  rfl

end CategoryTheory.MonoidalCategory
