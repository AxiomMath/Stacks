module

public import StacksFrontier.CategoryTheory.Sites.Stack.SlicePointIsomPresheaf

/-!
# Every object of a fibre is the value of a point of the slice

Let `p : 𝒵 ⥤ 𝒟/X` be fibred and let `U` be an object of `𝒟/X`. A *point of `p` with values in
`U`* is a functor `W : 𝒟/U.left ⥤ 𝒵` with `W ⋙ p = Over.map U.hom`, and its value at the
terminal object `1_{U.left}` lies in the fibre of `p` over `U`
(`CategoryTheory.Functor.sliceValue`). This file goes the other way: an object `y` of `𝒵` lying
over `U` *is* the value of such a point, up to a vertical morphism.

This is the essential-surjectivity half of the 2-Yoneda lemma (Stacks 004B) in the shape the data
of Stacks 06CK asks for. The point is the chosen-pullback point
`CategoryTheory.Functor.pullbackSliceFunctor` of `y`, read through the iterated-slice
identification of `𝒟/U.left` with `(𝒟/X)/U`, and the comparison morphism is the chosen cartesian
lift at the terminal object.

## Main definitions

* `CategoryTheory.Functor.slicePointOfObject`: the point attached to an object of the fibre.
* `CategoryTheory.Functor.slicePointUnit`: the comparison morphism of its value at the terminal
  object with the given object.

## Main results

* `CategoryTheory.Functor.slicePointOfObject_comp`: the point is a section over `𝒟/U.left`.
* `CategoryTheory.Functor.isHomLift_slicePointUnit`: the comparison morphism is vertical.
* `CategoryTheory.Functor.exists_slicePoint`: the three preceding statements packaged as an
  existence statement, which is the form a consumer assembling data for Stacks 06CK uses.

## Implementation notes

The statement is about points on `𝒟/U.left`, not on the slice `(𝒟/X)/U` of
`CategoryTheory.Functor.TwoYoneda.exists_basedFunctor_unitHom`: the two are identified only by
`CategoryTheory.Over.iteratedSliceEquiv`, and inserting that identification into a `Over.map
U.hom`-shaped statement costs more than composing with it here — the same trade-off recorded in
`StacksFrontier.CategoryTheory.Sites.Stack.SlicePointComparison`.

That the comparison morphism is vertical is the only computation. The chosen cartesian lift at the
terminal object lies over `CategoryTheory.Functor.structHom U (Over.mk (𝟙 U.left))`, which is the
`eqToHom` of `CategoryTheory.Functor.overMap_obj_mkId`, so the base morphism is an identity after
that identification.

## References

* [Stacks Project, Tag 004B](https://stacks.math.columbia.edu/tag/004B)
* [Stacks Project, Tag 06CK](https://stacks.math.columbia.edu/tag/06CK)
-/

@[expose] public section

open CategoryTheory

universe v₁ u₁ v₂ u₂

namespace CategoryTheory.Functor

variable {D : Type u₁} [Category.{v₁} D] {X : D} {Z : Type u₂} [Category.{v₂} Z]

/-- The structure morphism of the terminal object of `𝒟/U.left`, read in `𝒟/X`, is the
identification of `CategoryTheory.Functor.overMap_obj_mkId`. -/
theorem structHom_mkId (U : Over X) :
    structHom U (Over.mk (𝟙 U.left)) = eqToHom (overMap_obj_mkId U) := by
  apply Over.OverMorphism.ext
  simp

variable (p : Z ⥤ Over X) [p.IsFibered] (U : Over X) (y : Z) (hy : p.obj y = U)

/-- The point of `p` with values in `U` attached to an object `y` of `𝒵` lying over `U`: the
chosen pullbacks of `y` along the structure morphisms of the objects of `𝒟/U.left`. -/
noncomputable def slicePointOfObject : Over U.left ⥤ Z :=
  Over.iteratedSliceBackward U ⋙ pullbackSliceFunctor p ⟨y, hy⟩

/-- The point attached to an object of the fibre is a section: composing it with `p` gives the
structure functor of `𝒟/U.left` over `𝒟/X`. -/
theorem slicePointOfObject_comp : slicePointOfObject p U y hy ⋙ p = Over.map U.hom :=
  backward_pullbackSliceFunctor_comp p U ⟨y, hy⟩

/-- The comparison morphism of the value of `CategoryTheory.Functor.slicePointOfObject` at the
terminal object of `𝒟/U.left` with the object it was built from: the chosen cartesian lift
there. -/
noncomputable def slicePointUnit :
    (slicePointOfObject p U y hy).obj (Over.mk (𝟙 U.left)) ⟶ y :=
  IsPreFibered.pullbackMap hy (structHom U (Over.mk (𝟙 U.left)))

/-- The comparison morphism of `CategoryTheory.Functor.slicePointUnit` is vertical over `U`. -/
theorem isHomLift_slicePointUnit : p.IsHomLift (𝟙 U) (slicePointUnit p U y hy) := by
  have h : p.IsHomLift (structHom U (Over.mk (𝟙 U.left))) (slicePointUnit p U y hy) :=
    inferInstanceAs
      (p.IsHomLift (structHom U (Over.mk (𝟙 U.left)))
        (IsPreFibered.pullbackMap hy (structHom U (Over.mk (𝟙 U.left)))))
  rw [structHom_mkId U] at h
  have h' : p.IsHomLift (eqToHom (overMap_obj_mkId U) ≫ 𝟙 U) (slicePointUnit p U y hy) := by
    rwa [Category.comp_id]
  exact (IsHomLift.lift_eqToHom_comp_iff p (𝟙 U) (slicePointUnit p U y hy)
    (overMap_obj_mkId U)).mp h'

include hy in
/-- **Every object of a fibre is the value at the terminal object of a point of the slice**, up to
a vertical morphism. This is the essential surjectivity of the 2-Yoneda lemma for points on
`𝒟/U.left`, with the comparison morphism named: a consumer assembling the data of Stacks 06CK
needs the underlying morphism of `𝒵` and not just the isomorphism of fibres. -/
theorem exists_slicePoint :
    ∃ (W : Over U.left ⥤ Z) (_ : W ⋙ p = Over.map U.hom)
      (c : W.obj (Over.mk (𝟙 U.left)) ⟶ y), p.IsHomLift (𝟙 U) c :=
  ⟨slicePointOfObject p U y hy, slicePointOfObject_comp p U y hy,
    slicePointUnit p U y hy, isHomLift_slicePointUnit p U y hy⟩

end CategoryTheory.Functor

end
