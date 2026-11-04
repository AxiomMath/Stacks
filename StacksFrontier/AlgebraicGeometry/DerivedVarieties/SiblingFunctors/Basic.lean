module

public import StacksFrontier.Algebra.Homology.DerivedCategory.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Sibling functors from a bounded derived category

Two exact functors out of the bounded derived category of an abelian category `A` are *siblings*
when their restrictions to `A` are naturally isomorphic and their values at every object of the
bounded derived category are isomorphic. This file records the inclusion of `A` into its bounded
derived category and the sibling relation itself.

## Main definitions

* `AlgebraicGeometry.boundedSingleFunctor`: the inclusion of an abelian category into its bounded
  derived category, with objects placed in degree zero.
* `AlgebraicGeometry.AreSiblings`: the relation of being sibling exact functors.

## Implementation notes

The inclusion into the bounded derived category is the lift of `DerivedCategory.singleFunctor A 0`
to the full subcategory of bounded objects. Its comparison with the usual degree-zero functor is
`AlgebraicGeometry.boundedSingleFunctorCompιIso`.

An isomorphism is data, whereas being siblings is a proposition. Accordingly, both the natural
isomorphism between the restrictions and the objectwise isomorphisms are wrapped in `Nonempty`.
Exactness is expressed by the `CategoryTheory.Functor.CommShift` and
`CategoryTheory.Functor.IsTriangulated` instances on the two functors.

## References

* [Stacks Project, Tag 0FZT](https://stacks.math.columbia.edu/tag/0FZT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v v' u u'

namespace AlgebraicGeometry

/-- The canonical inclusion of an abelian category into its bounded derived category, sending
an object to the complex concentrated in degree zero. -/
@[implicit_reducible]
public noncomputable def boundedSingleFunctor (A : Type u) [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] : A ⥤ DerivedCategory.Bounded A :=
  (DerivedCategory.TStructure.t (C := A)).bounded.lift
    (DerivedCategory.singleFunctor A 0) (fun _ ↦ ⟨⟨0, inferInstance⟩, ⟨0, inferInstance⟩⟩)

/-- Composing the inclusion into the bounded derived category with its fully faithful inclusion
into the derived category gives the usual degree-zero single-object functor. -/
public noncomputable def boundedSingleFunctorCompιIso (A : Type u) [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] :
    boundedSingleFunctor A ⋙ DerivedCategory.Bounded.ι ≅ DerivedCategory.singleFunctor A 0 :=
  Iso.refl _

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
  {D : Type u'} [Category.{v'} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [IsTriangulated D]

/-- **Stacks Project, Tag 0FZT.** Two exact functors from the bounded derived category of an
abelian category are **siblings** if their restrictions to the abelian category are naturally
isomorphic and their values at each object of the bounded derived category are isomorphic. -/
@[stacks 0FZT]
public structure AreSiblings (F F' : DerivedCategory.Bounded A ⥤ D) [IsTriangulated D]
    [F.CommShift ℤ] [F.IsTriangulated] [F'.CommShift ℤ] [F'.IsTriangulated] : Prop where
  /-- The restrictions of the two functors to the abelian category are naturally isomorphic. -/
  restrictionIso : Nonempty (boundedSingleFunctor A ⋙ F ≅ boundedSingleFunctor A ⋙ F')
  /-- The values of the two functors at every bounded-derived object are isomorphic. -/
  objIso : ∀ K, Nonempty (F.obj K ≅ F'.obj K)

end AlgebraicGeometry

end
