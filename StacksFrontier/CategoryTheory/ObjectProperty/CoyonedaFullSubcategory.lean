module

public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic

/-!
# Compactness of an object of a full subcategory

Let `C` be a preadditive category and let `P : ObjectProperty C` be a property of its objects.
An object `K` of the full subcategory `P.FullSubcategory` corepresents the additive functor
`preadditiveCoyoneda.obj (op K)`, and the underlying object `K.obj` corepresents
`preadditiveCoyoneda.obj (op K.obj)` on `C`. The inclusion `P.ι` is fully faithful and additive,
so the first functor is the restriction of the second along `P.ι`
(`ObjectProperty.preadditiveCoyonedaObjιIso`).

The isomorphism transfers *compactness*, in the form
`PreservesColimitsOfShape (Discrete α) (preadditiveCoyoneda.obj (op K))` used for Brown
representability ([Stacks, Tag 0A8G]). If `P` is closed under the coproducts of shape
`Discrete α` that `C` has, then `P.ι` creates — hence preserves — them, so the composite
`P.ι ⋙ preadditiveCoyoneda.obj (op K.obj)` preserves them as soon as `K.obj` is compact in `C`.
Transporting along the isomorphism gives compactness of `K` inside `P.FullSubcategory`. In
particular, objects of a localizing subcategory that are compact in the ambient category are
compact in the subcategory.

## Main definitions

* `CategoryTheory.ObjectProperty.preadditiveCoyonedaObjιIso`: the additive functor corepresented
  by `K` is the restriction along `P.ι` of the one corepresented by `K.obj`.

## Main results

* `CategoryTheory.ObjectProperty.preservesColimitsOfShape_discrete_preadditiveCoyoneda_op`: if
  `P` is closed under coproducts of shape `Discrete α` and `K.obj` is compact for them in `C`,
  then `K` is compact for them in `P.FullSubcategory`.

## References

* [Stacks Project, Tag 0A8G](https://stacks.math.columbia.edu/tag/0A8G)
-/

@[expose] public section

universe w v u

namespace CategoryTheory.ObjectProperty

open Category Limits Opposite

variable {C : Type u} [Category.{v} C] [Preadditive C] (P : ObjectProperty C)

/-- The additive functor corepresented by an object `K` of `P.FullSubcategory` is the
restriction along the inclusion `P.ι` of the additive functor corepresented by the underlying
object `K.obj` of `C`: the inclusion is fully faithful, hence bijective on morphism groups, and
additive, hence that bijection is an isomorphism of abelian groups. -/
noncomputable def preadditiveCoyonedaObjιIso (K : P.FullSubcategory) :
    preadditiveCoyoneda.obj (op K) ≅ P.ι ⋙ preadditiveCoyoneda.obj (op K.obj) :=
  NatIso.ofComponents
    (fun M ↦ (AddEquiv.ofBijective (P.ι.mapAddHom (X := K) (Y := M))
      ⟨P.ι.map_injective, P.ι.map_surjective⟩).toAddCommGrpIso)
    (fun f ↦ by ext g; exact P.ι.map_comp g f)

/-- **Compactness passes to a full subcategory closed under the relevant coproducts.** If `P` is
closed under the coproducts of shape `Discrete α` existing in `C`, then the inclusion `P.ι`
creates, hence preserves, those coproducts; so if the underlying object of `K` corepresents a
functor on `C` preserving them, then `K` corepresents a functor on `P.FullSubcategory`
preserving them. -/
lemma preservesColimitsOfShape_discrete_preadditiveCoyoneda_op (K : P.FullSubcategory)
    (α : Type w) [HasColimitsOfShape (Discrete α) C]
    [P.IsClosedUnderColimitsOfShape (Discrete α)]
    [PreservesColimitsOfShape (Discrete α) (preadditiveCoyoneda.obj (op K.obj))] :
    PreservesColimitsOfShape (Discrete α) (preadditiveCoyoneda.obj (op K)) :=
  have : PreservesColimitsOfShape (Discrete α) P.ι := inferInstance
  preservesColimitsOfShape_of_natIso (P.preadditiveCoyonedaObjιIso K).symm

end CategoryTheory.ObjectProperty

end
