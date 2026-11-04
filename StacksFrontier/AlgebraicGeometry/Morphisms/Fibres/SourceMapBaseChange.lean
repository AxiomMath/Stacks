module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.SourceMap
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Properties of the comparison morphism of fibres inherited from the source

For `i : Z ⟶ X` and `f : X ⟶ Y` the comparison morphism
`AlgebraicGeometry.Scheme.Hom.fiberMap f i y : (i ≫ f).fiber y ⟶ f.fiber y` is the base change
of `i` along the fibre inclusion `f.fiberι y`. So every property of `i` stable under base change
is a property of the comparison morphism, and in particular the fibres of `i ≫ f` map to the
fibres of `f` by flat morphisms, locally of finite type, of the same relative dimension as `i`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.flat_fiberMap` and
  `AlgebraicGeometry.Scheme.Hom.locallyOfFiniteType_fiberMap`: flatness and local finite type of
  the comparison morphism.
* `AlgebraicGeometry.Scheme.Hom.surjective_fiberMap_of_forall_exists`: a family of morphisms
  jointly surjective onto `X` induces a family of comparison morphisms jointly surjective onto
  each fibre of `f`.
* `AlgebraicGeometry.Scheme.Hom.relativeDimension_fiberMap`: the comparison morphism has the
  relative dimension of `i`.

## References

* [Stacks Project, Tag 02NK](https://stacks.math.columbia.edu/tag/02NK)
* [Stacks Project, Tag 053R](https://stacks.math.columbia.edu/tag/053R)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {X Y Z : Scheme.{u}}

/-- The comparison morphism of fibres is flat as soon as the morphism of sources is, being its
base change along the fibre inclusion. -/
@[sga "3 VIB 3.11" "fiber-flatness"]
instance Scheme.Hom.flat_fiberMap (f : X ⟶ Y) (i : Z ⟶ X) [Flat i] (y : Y) :
    Flat (f.fiberMap i y) :=
  MorphismProperty.of_isPullback (f.isPullback_fiberMap i y).flip inferInstance

/-- The comparison morphism of fibres is locally of finite type as soon as the morphism of
sources is, being its base change along the fibre inclusion. -/
instance Scheme.Hom.locallyOfFiniteType_fiberMap (f : X ⟶ Y) (i : Z ⟶ X)
    [LocallyOfFiniteType i] (y : Y) : LocallyOfFiniteType (f.fiberMap i y) :=
  MorphismProperty.of_isPullback (f.isPullback_fiberMap i y).flip inferInstance

/-- **Stacks Project, Tag 02NK.** The comparison morphism of fibres has the relative dimension
of the morphism of sources, relative dimension being stable under base change. -/
theorem Scheme.Hom.relativeDimension_fiberMap (f : X ⟶ Y) (i : Z ⟶ X) [LocallyOfFiniteType i]
    (y : Y) (d : ℕ) (hi : RelativeDimension i d) : RelativeDimension (f.fiberMap i y) d :=
  RelativeDimension.of_isPullback (f.isPullback_fiberMap i y).flip hi

/-- A point of a fibre of `f` lying over the image of `i` is the image of a point of the
corresponding fibre of `i ≫ f`. -/
theorem Scheme.Hom.exists_fiberMap_eq (f : X ⟶ Y) (i : Z ⟶ X) (y : Y) (w : f.fiber y) (z : Z)
    (hz : i.base z = f.fiberι y w) :
    ∃ v : (i ≫ f).fiber y, (f.fiberMap i y).base v = w :=
  (f.range_fiberMap i y).ge ⟨z, hz⟩

/-- A family of morphisms to `X` that is jointly surjective induces, on each fibre of
`f : X ⟶ Y`, a jointly surjective family of comparison morphisms. -/
theorem Scheme.Hom.surjective_fiberMap_of_forall_exists (f : X ⟶ Y) {Idx : Type*}
    {W : Idx → Scheme.{u}} (i : ∀ j, W j ⟶ X)
    (hsurj : ∀ x : X, ∃ j, ∃ z : W j, (i j).base z = x) (y : Y) (w : f.fiber y) :
    ∃ j, ∃ v : (i j ≫ f).fiber y, (f.fiberMap (i j) y).base v = w := by
  obtain ⟨j, z, hz⟩ := hsurj (f.fiberι y w)
  exact ⟨j, f.exists_fiberMap_eq (i j) y w z hz⟩

end AlgebraicGeometry

end
