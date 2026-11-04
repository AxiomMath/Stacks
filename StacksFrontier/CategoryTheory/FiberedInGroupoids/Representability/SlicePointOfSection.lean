module

public import StacksFrontier.CategoryTheory.FiberedCategory.PresheafElements
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.SlicePoint

/-!
# A point of a representable category fibred in groupoids, from a section of the presheaf

Let `𝒞` be a category, `X` an object of `𝒞` and `q : 𝒟 ⥤ 𝒞/X` a category fibred in groupoids over
the slice at `X` which is equivalent, over that slice, to the category of elements of a presheaf
of sets `P` (`CategoryTheory.PresheafOfCategories.discreteProjection`). A morphism of presheaves
`b : h_T ⟶ P` out of a representable one — equivalently, by the Yoneda lemma, a section of `P`
over `T` — then determines a 1-morphism

```text
𝒞/T.left ⥤ 𝒟   over   CategoryTheory.Over.map T.hom,
```

together with a vertical identification of its value at the tautological object with the object
of `𝒟` that the section names.

## Main definitions

* `StacksRepresentableCFG.objOfSection`: the object of `𝒟` named by a section of the
  representing presheaf.

## Main results

* `StacksRepresentableCFG.obj_objOfSection`: it lies over the object the section is taken at.
* `StacksRepresentableCFG.exists_pointOverMap_of_section`: the 1-morphism `𝒞/T.left ⥤ 𝒟` over
  `Over.map T.hom` determined by a section, with the vertical identification at the tautological
  object.

## Implementation notes

The object of the category of elements attached to a section `s` of `P` over `T` is written out
as `⟨T, Discrete.mk s⟩`, which is the inverse of
`CategoryTheory.PresheafOfCategories.discreteFiberEquiv`; that it lies over `T` is `rfl`, so the
only content of `StacksRepresentableCFG.obj_objOfSection` is that the inverse 1-morphism of the
equivalence is strictly over the base.

A morphism `b : yoneda.obj T ⟶ P` is converted to a section by evaluating at `𝟙 T`, rather than
through `CategoryTheory.yonedaEquiv`, so that no universe lift intervenes.
-/

@[expose] public section

open CategoryTheory Opposite

namespace StacksRepresentableCFG

universe v₁ v₂ u₁ u₂

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒟 : Type u₂} [Category.{v₂} 𝒟]

section

variable {q : 𝒟 ⥤ 𝒞} {P : 𝒞ᵒᵖ ⥤ Type v₁}
  (e : EquivalenceOver q (PresheafOfCategories.discreteProjection P)) (T : 𝒞)
  (s : P.obj (op T))

/-- The object of `𝒟` named by a section `s` of the representing presheaf `P` over `T`: carry the
corresponding object `(T, s)` of the category of elements of `P` back along the equivalence. -/
def objOfSection : 𝒟 :=
  e.inv.functor.obj ⟨T, Discrete.mk s⟩

/-- The object named by a section of `P` over `T` lies over `T`. -/
theorem obj_objOfSection : q.obj (objOfSection e T s) = T :=
  Functor.congr_obj e.inv.w _

end

/-- **A scheme-valued point from a section of the representing presheaf.** Let `q : 𝒟 ⥤ 𝒞/X` be
a category fibred in groupoids over the slice of `𝒞` at `X`, equivalent over that slice to the
category of elements of a presheaf of sets `P`, and let `b : h_T ⟶ P` be a morphism from a
representable presheaf. Then there is a 1-morphism `y : 𝒞/T.left ⥤ 𝒟` strictly over
`CategoryTheory.Over.map T.hom`, together with a vertical isomorphism of its value at the
tautological object of `𝒞/T.left` with the object of `𝒟` named by the section `b(𝟙 T)`. -/
theorem exists_pointOverMap_of_section {X : 𝒞} (q : 𝒟 ⥤ Over X) (hq : q.IsFiberedInGroupoids)
    {P : (Over X)ᵒᵖ ⥤ Type v₁}
    (e : EquivalenceOver q (PresheafOfCategories.discreteProjection P))
    (T : Over X) (b : yoneda.obj T ⟶ P) :
    ∃ (y : Over T.left ⥤ 𝒟) (_ : y ⋙ q = Over.map T.hom)
      (ξ : y.obj (Over.mk (𝟙 T.left)) ≅ objOfSection e T (b.app (op T) (𝟙 T))),
      q.IsHomLift (𝟙 T) ξ.hom :=
  exists_pointOverMap_of_obj q hq T _ (obj_objOfSection e T (b.app (op T) (𝟙 T)))

end StacksRepresentableCFG

end
