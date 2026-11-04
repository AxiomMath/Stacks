module

public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.FibreFunctors

/-!
# A point of a category fibred in groupoids over a slice, from an object over the base

Let `𝒞` be a category, let `X` be an object of `𝒞` and let `q : 𝒴 ⥤ 𝒞/X` be a category fibred in
groupoids over the slice at `X`. For an object `W` of `𝒞/X`, the 2-Yoneda lemma
`Stacks.RepresentableMorphism.ClassifyingFunctor.exists_classifying_functor` turns an object `y₀`
of `𝒴` lying over `W` into a 1-morphism `(𝒞/X)/W ⥤ 𝒴` over `𝒞/X`. Precomposing it with
`CategoryTheory.Over.iteratedSliceBackward` gives a 1-morphism out of `𝒞/W.left`, the slice of `𝒞`
at the *underlying* object of `W`, lying strictly over `CategoryTheory.Over.map W.hom`:

```text
y₀ an object of 𝒴 over W   ⟼   a 1-morphism  𝒞/W.left ⥤ 𝒴  over  Over.map W.hom.
```

## Main definitions

* `StacksRepresentableCFG.iteratedSliceBackwardIdIso`: the tautological object of `(𝒞/X)/W` is
  the image of the tautological object of `𝒞/W.left` under
  `CategoryTheory.Over.iteratedSliceBackward`.

## Main results

* `StacksRepresentableCFG.exists_pointOverMap_of_obj`: an object of `𝒴` lying over `W` is the
  value at the tautological object of a 1-morphism `𝒞/W.left ⥤ 𝒴` strictly over
  `Over.map W.hom`, the identification being vertical.

## Implementation notes

The vertical identification is stated at `CategoryTheory.Over.mk (𝟙 W.left)` rather than at
`CategoryTheory.Over.mk (𝟙 W)`, because that is the tautological object of the slice the 1-morphism
is defined on. The two are matched by `StacksRepresentableCFG.iteratedSliceBackwardIdIso`, which is
not an identity: the image of `Over.mk (𝟙 W.left)` under `Over.iteratedSliceBackward` has
underlying object `Over.mk (𝟙 W.left ≫ W.hom)`, equal to `W` only after
`CategoryTheory.Category.id_comp`. Its components are identities on the underlying objects of `𝒞`,
which is what makes the identification vertical.

## References

* [Stacks Project, Tag 02Y4](https://stacks.math.columbia.edu/tag/02Y4)
* [Stacks Project, Tag 04SS](https://stacks.math.columbia.edu/tag/04SS)
* [Stacks Project, Tag 02ZW](https://stacks.math.columbia.edu/tag/02ZW)
-/

@[expose] public section

open CategoryTheory

namespace StacksRepresentableCFG

universe v₁ v₂ u₁ u₂

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒴 : Type u₂} [Category.{v₂} 𝒴]

/-- The tautological object of `(𝒞/X)/W` is the image of the tautological object of `𝒞/W.left`
under `CategoryTheory.Over.iteratedSliceBackward`. Both components of the isomorphism are
identities on the underlying object `W.left` of `𝒞`. -/
def iteratedSliceBackwardIdIso {X : 𝒞} (W : Over X) :
    W.iteratedSliceBackward.obj (Over.mk (𝟙 W.left)) ≅ Over.mk (𝟙 W) :=
  Over.isoMk (Over.isoMk (Iso.refl W.left))

/-- The component of `StacksRepresentableCFG.iteratedSliceBackwardIdIso W` on the underlying
object of `𝒞` is the identity of `W.left`. -/
@[simp] theorem iteratedSliceBackwardIdIso_hom_left_left {X : 𝒞} (W : Over X) :
    (iteratedSliceBackwardIdIso W).hom.left.left = 𝟙 W.left :=
  rfl

/-- The underlying object of the image of the tautological object of `𝒞/W.left` under
`CategoryTheory.Over.iteratedSliceBackward` is `W` itself: it is `W.left` equipped with
`𝟙 W.left ≫ W.hom`. -/
theorem forget_obj_iteratedSliceBackward_id {X : 𝒞} (W : Over X) :
    (Over.forget W).obj (W.iteratedSliceBackward.obj (Over.mk (𝟙 W.left))) = W :=
  congrArg Over.mk (Category.id_comp W.hom)

/-- `StacksRepresentableCFG.iteratedSliceBackwardIdIso` is a vertical isomorphism of `(𝒞/X)/W`:
it lies over the identity of `W`. -/
theorem isHomLift_iteratedSliceBackwardIdIso {X : 𝒞} (W : Over X) :
    (Over.forget W).IsHomLift (𝟙 W) (iteratedSliceBackwardIdIso W).hom := by
  refine IsHomLift.of_fac' _ (𝟙 W) _ (forget_obj_iteratedSliceBackward_id W) rfl
    (Over.OverMorphism.ext ?_)
  aesop_cat

/-- Let `q : 𝒴 ⥤ 𝒞/X` be a category fibred in groupoids over the slice of `𝒞` at `X`, let `W` be
an object of `𝒞/X` and let `y₀` be an object of `𝒴` lying over `W`. Then there is a 1-morphism
`y : 𝒞/W.left ⥤ 𝒴` strictly over `CategoryTheory.Over.map W.hom`, together with a vertical
isomorphism of its value at the tautological object of `𝒞/W.left` with `y₀`. -/
theorem exists_pointOverMap_of_obj {X : 𝒞} (q : 𝒴 ⥤ Over X) (hq : q.IsFiberedInGroupoids)
    (W : Over X) (y₀ : 𝒴) (hy₀ : q.obj y₀ = W) :
    ∃ (y : Over W.left ⥤ 𝒴) (_ : y ⋙ q = Over.map W.hom)
      (ξ : y.obj (Over.mk (𝟙 W.left)) ≅ y₀), q.IsHomLift (𝟙 W) ξ.hom := by
  obtain ⟨G, hGq, ξ₀, hξ₀⟩ :=
    Stacks.RepresentableMorphism.ClassifyingFunctor.exists_classifying_functor q hq W y₀ hy₀
  have hθ : (Over.forget W).IsHomLift (𝟙 W) (iteratedSliceBackwardIdIso W).hom :=
    isHomLift_iteratedSliceBackwardIdIso W
  have hGθ : q.IsHomLift (𝟙 W) (G.map (iteratedSliceBackwardIdIso W).hom) :=
    Functor.isHomLift_map_of_comp_eq hGq (𝟙 W) (iteratedSliceBackwardIdIso W).hom
  refine ⟨W.iteratedSliceBackward ⋙ G, ?_, G.mapIso (iteratedSliceBackwardIdIso W) ≪≫ ξ₀, ?_⟩
  · rw [Functor.assoc, hGq, Over.iteratedSliceBackward_forget]
  · simpa using IsHomLift.comp q (𝟙 W) (𝟙 W)
      (G.map (iteratedSliceBackwardIdIso W).hom) ξ₀.hom

end StacksRepresentableCFG

end
