module

public import StacksFrontier.AlgebraicGeometry.Stacks.UniversalFamilyNormalisation

/-!
# The chosen arrows out of the 2-Yoneda universal family of an object

Let `𝒯` be a category over the big fppf site of a scheme `S` which is fibred in groupoids and
let `X` be an object of `𝒯`. The scheme-valued point
`AlgebraicGeometry.Stack.objUniversalFamily` attached to `X` by the 2-Yoneda lemma is assembled
from chosen strongly cartesian lifts of the structure morphisms of the slice over the base of
`X`. This file names those lifts and records their four properties: each is strongly cartesian
over the structure morphism of its test object, hence lies over it; they are compatible with the
transition morphisms of the family; and the base object of a member of the family is the image of
its test object.

Everything here is about an arbitrary target `𝒯`, so it is available to any fibre computation
performed over a universal family, and in particular to both Stacks 05YH and Stacks 05YJ.

## Main definitions

* `AlgebraicGeometry.Stack.objUniversalArrow`: the chosen strongly cartesian morphism from the
  member of the universal family at a test object to the object the family is attached to.

## Main results

* `AlgebraicGeometry.Stack.objUniversalArrow_isStronglyCartesian`: it is strongly cartesian over
  the structure morphism of the test object.
* `AlgebraicGeometry.Stack.objUniversalArrow_over`: hence it lies over that morphism.
* `AlgebraicGeometry.Stack.objUniversalArrow_naturality`: the chosen morphisms are compatible
  with the transition morphisms of the family.
* `AlgebraicGeometry.Stack.objUniversalFamily_base_obj`: the base object of a member of the
  family is the image of the test object.
* `AlgebraicGeometry.Stack.objUniversalArrow_base`: the morphism of the site underlying the
  chosen morphism is the structure morphism of the test object.

## What is and is not proved

Proved, in full, with no carried hypothesis. No tag is claimed: the file states no result of the
Stacks project, it names the data out of which the 2-Yoneda point of an object is built.

## Implementation notes

The chosen lift itself is `CategoryTheory.Functor.TwoYoneda.chosenLift`, read at the fibre object
`CategoryTheory.Functor.Fiber.mk rfl` out of which `AlgebraicGeometry.Stack.objUniversalFamily`
is assembled; every statement about it is made
through `AlgebraicGeometry.Stack.objUniversalArrow`, which is the chosen arrow itself.

`AlgebraicGeometry.Stack.objUniversalFamily` is semireducible, so it is made
`implicit_reducible` locally: the type of the chosen arrow is spelled with the composite that it
unfolds to.

## References

* [Stacks Project, Tag 004B](https://stacks.math.columbia.edu/tag/004B)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v₂ u₂

namespace AlgebraicGeometry.Stack

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒯 : BasedCategory.{v₂, u₂} (BigFppfOver B S hS)}

attribute [local implicit_reducible] objUniversalFamily CategoryTheory.Over.iteratedSliceBackward
  CategoryTheory.Over.homMk

/-- The chosen strongly cartesian lift of the structure morphism of a test object out of which
the 2-Yoneda point of an object of `𝒯` is assembled. -/
noncomputable abbrev objUniversalLift (h𝒯 : 𝒯.p.IsFiberedInGroupoids) (X : 𝒯.obj)
    (T : Over (𝒯.p.obj X).left) :=
  Functor.TwoYoneda.chosenLift 𝒯.p h𝒯 (𝒯.p.obj X) (Functor.Fiber.mk (a := X) rfl)
    ((Over.iteratedSliceBackward (𝒯.p.obj X)).obj T)

/-- The chosen strongly cartesian morphism from the member of the 2-Yoneda universal family of
an object at a test object to that object. -/
noncomputable def objUniversalArrow (h𝒯 : 𝒯.p.IsFiberedInGroupoids) (X : 𝒯.obj)
    (T : Over (𝒯.p.obj X).left) : (objUniversalFamily h𝒯 X).obj T ⟶ X :=
  (objUniversalLift h𝒯 X T).φ

/-- The chosen morphism out of a member of the 2-Yoneda universal family is strongly cartesian
over the structure morphism of the test object. -/
theorem objUniversalArrow_isStronglyCartesian (h𝒯 : 𝒯.p.IsFiberedInGroupoids) (X : 𝒯.obj)
    (T : Over (𝒯.p.obj X).left) :
    𝒯.p.IsStronglyCartesian ((Over.iteratedSliceBackward (𝒯.p.obj X)).obj T).hom
      (objUniversalArrow h𝒯 X T) :=
  (objUniversalLift h𝒯 X T).isStronglyCartesian

/-- The chosen morphism out of a member of the 2-Yoneda universal family lies over the structure
morphism of the test object. -/
theorem objUniversalArrow_over (h𝒯 : 𝒯.p.IsFiberedInGroupoids) (X : 𝒯.obj)
    (T : Over (𝒯.p.obj X).left) :
    𝒯.p.IsHomLift ((Over.iteratedSliceBackward (𝒯.p.obj X)).obj T).hom
      (objUniversalArrow h𝒯 X T) :=
  (objUniversalArrow_isStronglyCartesian h𝒯 X T).toIsHomLift

/-- The chosen morphisms out of the 2-Yoneda universal family are compatible with its transition
morphisms. -/
theorem objUniversalArrow_naturality (h𝒯 : 𝒯.p.IsFiberedInGroupoids) (X : 𝒯.obj)
    {T T' : Over (𝒯.p.obj X).left} (f : T ⟶ T') :
    (objUniversalFamily h𝒯 X).map f ≫ objUniversalArrow h𝒯 X T' = objUniversalArrow h𝒯 X T :=
  have _h := objUniversalArrow_isStronglyCartesian h𝒯 X T'
  have _h' := objUniversalArrow_over h𝒯 X T
  Functor.IsStronglyCartesian.fac 𝒯.p
    ((Over.iteratedSliceBackward (𝒯.p.obj X)).obj T').hom (objUniversalArrow h𝒯 X T')
    (Over.w ((Over.iteratedSliceBackward (𝒯.p.obj X)).map f)).symm (objUniversalArrow h𝒯 X T)

/-- The base object of a member of the 2-Yoneda universal family is the image of the test
object. -/
theorem objUniversalFamily_base_obj (h𝒯 : 𝒯.p.IsFiberedInGroupoids) (X : 𝒯.obj)
    (T : Over (𝒯.p.obj X).left) :
    𝒯.p.obj ((objUniversalFamily h𝒯 X).obj T) = (Over.map (𝒯.p.obj X).hom).obj T :=
  congrArg (fun K => K.obj T) (objUniversalFamily_comp h𝒯 X)

/-- The morphism of the site underlying the chosen morphism out of a member of the 2-Yoneda
universal family is the structure morphism of the test object. -/
theorem objUniversalArrow_base (h𝒯 : 𝒯.p.IsFiberedInGroupoids) (X : 𝒯.obj)
    (T : Over (𝒯.p.obj X).left) :
    𝒯.p.map (objUniversalArrow h𝒯 X T) =
      eqToHom (objUniversalFamily_base_obj h𝒯 X T) ≫
        ((Over.iteratedSliceBackward (𝒯.p.obj X)).obj T).hom := by
  have h := objUniversalArrow_over h𝒯 X T
  have hf := IsHomLift.fac' 𝒯.p ((Over.iteratedSliceBackward (𝒯.p.obj X)).obj T).hom
    (objUniversalArrow h𝒯 X T)
  rw [hf]
  simp only [eqToHom_refl, Category.comp_id]

end AlgebraicGeometry.Stack

end
