module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ChangeOfRingsExactness
public import StacksFrontier.CategoryTheory.Abelian.InverseSystem

/-!
# Image subobjects travel along restriction of scalars

Restriction of scalars along a morphism `α : R ⟶ R'` of sheaves of rings is exact
(`Stacks.SheafOfModules.ChangeOfRings.exactFunctor_restrictScalars`), hence preserves the limits
and colimits out of which images are built. So the image of a morphism `f` of sheaves of
`R'`-modules, read as a subobject of the restriction of its target, *is* the image of the
restricted morphism: no comparison has to be chosen, and a filtration by image subobjects is
carried step by step onto the corresponding filtration over the smaller ring sheaf.

This is `CategoryTheory.map_imageSubobject_eq` of
`StacksFrontier.CategoryTheory.Abelian.InverseSystem`, instantiated at restriction of scalars.

## Main results

* `Stacks.SheafOfModules.ChangeOfRings.imageSubobject_map_restrictScalars`: the image of a
  restricted morphism is the restriction of its image.

## References

* [The Stacks Project, Tag 03CU](https://stacks.math.columbia.edu/tag/03CU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v' u' u

namespace Stacks.SheafOfModules.ChangeOfRings

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {R R' : Sheaf J RingCat.{u}} (α : R ⟶ R')

/-- For a morphism `f : M ⟶ N` of sheaves of `R'`-modules, the image subobject of the restriction
of scalars of `f` along `α` is the image under restriction of scalars of the image subobject of
`f`. -/
theorem imageSubobject_map_restrictScalars {M N : _root_.SheafOfModules.{u} R'} (f : M ⟶ N) :
    imageSubobject ((_root_.SheafOfModules.restrictScalars.{u} α).map f) =
      (mapSubobjects (_root_.SheafOfModules.restrictScalars.{u} α) N).obj (imageSubobject f) :=
  (map_imageSubobject_eq (_root_.SheafOfModules.restrictScalars.{u} α) f).symm

end Stacks.SheafOfModules.ChangeOfRings

end

end
