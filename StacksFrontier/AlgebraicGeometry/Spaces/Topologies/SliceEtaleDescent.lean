module

public import Mathlib.CategoryTheory.Sites.IsSheafFor
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.EtalePhCoverings

/-!
# Étale descent and fibre products on the slice over an algebraic space

Let `B` be a big fppf site, `S` a scheme of `B` and `X` an algebraic space over `S`. This file
records, for a presheaf of sets on the bare slice category `Over X` of algebraic spaces over `X`
(no chosen big site of algebraic spaces), the étale descent condition, and the fibre products of
that slice category.

## Main definitions

* `AlgebraicGeometry.Space.IsEtaleSheafOnSlice` — étale descent for a presheaf on `Over X`.
* `AlgebraicGeometry.Space.sliceFiberProduct`, with its projections
  `AlgebraicGeometry.Space.sliceFiberProductFst` and
  `AlgebraicGeometry.Space.sliceFiberProductSnd` — the fibre product of two morphisms of
  `Over X`, built from the fibre product of algebraic spaces.

## Main results

* `AlgebraicGeometry.Space.sliceFiberProduct_isPullback` — that square is a pullback.

## Implementation notes

These are variants of the declarations `IsEtaleSheafOver`, `slicePullback`, `slicePullbackFst`,
`slicePullbackSnd` and `slicePullback_isPullback` of
`StacksFrontier/AlgebraicGeometry/Spaces/Topologies/PhSheafCriterion.lean`. The base declarations
are stated over a chosen big ph site of algebraic spaces `T`, for the slice `BigPHSpaceOver T X`;
the ones here are stated over the bare slice `Over X` of the algebraic spaces of `B`, which is
what a presheaf coming from a big étale site needs. The base statements are left untouched, so
these carry their own names; at `B = T.fppfSite` they are definitionally the base ones.

## References

* [Stacks Project, Tag 0DFM](https://stacks.math.columbia.edu/tag/0DFM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)
  (F : (Over X)ᵒᵖ ⥤ Type w)

/-- Étale descent for a presheaf on the slice category of algebraic spaces over `X`: the sheaf
condition holds for every family in the slice at `X` whose underlying family of morphisms of
algebraic spaces is an étale covering in the sense of Stacks 041E. -/
def IsEtaleSheafOnSlice : Prop :=
  ∀ (U : Over X) (E : PreZeroHypercover.{u + 2} U),
    IsEtaleCovering B S hS
      (fun i ↦ (E.X i).left.1) (fun i ↦ (E.f i).left.hom) →
    Presieve.IsSheafFor F E.presieve₀

/-- The fibre product of two morphisms of the slice category of algebraic spaces over `X`: the
fibre product of algebraic spaces, viewed over `X` through the first projection. -/
noncomputable def sliceFiberProduct {U V W : Over X} (f : V ⟶ U) (g : W ⟶ U) :
    Over X :=
  Over.mk ((ObjectProperty.homMk (pullback.fst f.left.hom g.left.hom) :
    AlgebraicSpaces.fiberProduct B S hS f.left g.left ⟶ V.left) ≫ V.hom)

/-- The first projection of `AlgebraicGeometry.Space.sliceFiberProduct`. -/
noncomputable def sliceFiberProductFst {U V W : Over X} (f : V ⟶ U) (g : W ⟶ U) :
    sliceFiberProduct B S hS X f g ⟶ V :=
  Over.homMk (ObjectProperty.homMk (pullback.fst f.left.hom g.left.hom)) rfl

/-- The second projection of `AlgebraicGeometry.Space.sliceFiberProduct`. -/
noncomputable def sliceFiberProductSnd {U V W : Over X} (f : V ⟶ U) (g : W ⟶ U) :
    sliceFiberProduct B S hS X f g ⟶ W :=
  Over.homMk (ObjectProperty.homMk (pullback.snd f.left.hom g.left.hom)) (by
    change (ObjectProperty.homMk (pullback.snd f.left.hom g.left.hom) :
        AlgebraicSpaces.fiberProduct B S hS f.left g.left ⟶ W.left) ≫ W.hom =
      (ObjectProperty.homMk (pullback.fst f.left.hom g.left.hom) :
        AlgebraicSpaces.fiberProduct B S hS f.left g.left ⟶ V.left) ≫ V.hom
    rw [← g.w, ← f.w, ← Category.assoc, ← Category.assoc,
      (AlgebraicSpaces.isPullback_fiberProduct B S hS f.left g.left).w])

/-- `AlgebraicGeometry.Space.sliceFiberProduct` is a fibre product in the slice over `X`: the
forgetful functor to algebraic spaces is faithful and reflects fibre products, and the image of
the square is the fibre product of algebraic spaces. -/
theorem sliceFiberProduct_isPullback {U V W : Over X} (f : V ⟶ U) (g : W ⟶ U) :
    IsPullback (sliceFiberProductFst B S hS X f g) (sliceFiberProductSnd B S hS X f g) f g :=
  IsPullback.of_map_of_faithful (Over.forget X)
    (AlgebraicSpaces.isPullback_fiberProduct B S hS f.left g.left)

end AlgebraicGeometry.Space

end
