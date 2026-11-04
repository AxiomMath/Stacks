module

public import StacksFrontier.AlgebraicGeometry.Picard.HilbertAbelMap
public import StacksFrontier.AlgebraicGeometry.PicardScheme.PicardFunctor

/-!
# The Abel morphism of functors of points, from the Hilbert functor to the Picard functor

Let `f : X ⟶ S` be a morphism of a big fppf site which is smooth of relative dimension one, so
that `X ⟶ S` is a smooth relative curve, and let `d` be a natural number. A degree-`d` Hilbert
family in `X` over a test scheme `T` of the site is a relative effective Cartier divisor on
`X_T` (Tag 0B9C), and the class of its invertible sheaf is an element of `Pic(X_T)`, the value at
`T` of the presheaf whose fppf sheafification is the Picard functor. This file assembles those
classes into a morphism of functors of points

`γ_d : Hilb^d_{X/S} ⟶ Pic_{X/S}`,

the *Abel morphism* in degree `d`, and composes it with the unit of the sheafification to land in
the Picard functor itself.

No representability of either functor is used: this is the Abel morphism at the level of functors
of points, where it is the naturality of `Stacks.Hilbert.abelClass` under base change and nothing
else.

## Main definitions

* `Stacks.Hilbert.ambientOverBase` — the morphism `f` of the site read as an object of the slice
  category of all schemes over `S`.
* `Stacks.Hilbert.hilbertFunctorOnBigFppfSite` — the degree-`d` Hilbert functor restricted to the
  test schemes of the big fppf site, with its values lifted to the universe the Picard presheaf
  lives in.
* `Stacks.Hilbert.abelTransformation` — the Abel morphism `γ_d` into the presheaf `T ↦ Pic(X_T)`.
* `Stacks.Hilbert.abelTransformationToPicardFunctor` — the same composed with the unit of the
  fppf sheafification, so landing in the Picard functor `Pic_{X/S}`.

## Main results

* `Stacks.Hilbert.baseChange_eq_pullback_ambientOverBase` and
  `Stacks.Hilbert.familyBaseChangeMap_ambientOverBase` — the base change of `X` used by the
  Picard presheaf and the one used by the Hilbert functor are the same scheme and the same
  comparison morphism.

## Implementation notes

*Why the two functors need reconciling at all.* The Hilbert functor of
`StacksFrontier/AlgebraicGeometry/Picard/HilbertFunctorFpqcSheaf.lean` is indexed by the slice
category `Over S` of all schemes over `S` and takes values in `Type u`; the Picard presheaf of
`StacksFrontier/AlgebraicGeometry/PicardScheme/PicardFunctor.lean` is indexed by the test schemes
`BigFppfOver B S hS` of a chosen big fppf site and takes values in `Type (u + 1)`, a Picard group
being a type of isomorphism classes of modules. Two adjustments bring them together: restriction
along `Over.post B.inclusion`, the functor sending a test scheme of the site to its underlying
`S`-scheme, and `CategoryTheory.uliftFunctor` on the values. Neither changes the mathematics —
the restriction is a change of index category and the lift is injective on each value — and
nothing about the Hilbert functor is redefined.

*The two base changes agree on the nose.* `Stacks.PicardFunctor.baseChange` is the fibre product
`X ×_S T` formed from the morphisms of the site, and the Hilbert functor's ambient scheme is the
fibre product formed in `Over S`; after the restriction these are the same `pullback` of the same
two morphisms, so `Stacks.Hilbert.baseChange_eq_pullback_ambientOverBase` and
`Stacks.Hilbert.familyBaseChangeMap_ambientOverBase` hold by `rfl` and no transport along an
equality of schemes appears anywhere below.

## References

* [Stacks Project, Tag 0B94](https://stacks.math.columbia.edu/tag/0B94)
* [Stacks Project, Tag 0B9C](https://stacks.math.columbia.edu/tag/0B9C)
* [Stacks Project, Tag 0B9L](https://stacks.math.columbia.edu/tag/0B9L)
* [Stacks Project, Tag 021S](https://stacks.math.columbia.edu/tag/021S)
-/


@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Hilbert

variable (B : BigFppfSite.{u}) {X S : Scheme.{u}} (hX : B.Contains X) (hS : B.Contains S)
  (f : B.obj hX ⟶ B.obj hS)

/-- The morphism `f : X ⟶ S` of a big fppf site read as an object of the slice category of all
schemes over `S`. -/
abbrev ambientOverBase : Over S := Over.mk (B.inclusion.map f)

/-- The base change `X ×_S T` used by the Picard presheaf is the ambient scheme of the Hilbert
families over the test scheme `T`: both are the fibre product of `X ⟶ S` with `T ⟶ S`. -/
theorem baseChange_eq_pullback_ambientOverBase (T : BigFppfOver B S hS) :
    ((Over.pullback ((Over.post B.inclusion).obj T).hom).obj (ambientOverBase B hX hS f)).left =
      Stacks.PicardFunctor.baseChange B hX hS f T :=
  rfl

/-- The comparison morphism `X_T ⟶ X_U` of the Hilbert functor and the one of the Picard
presheaf are the same morphism of schemes. -/
theorem familyBaseChangeMap_ambientOverBase {T U : BigFppfOver B S hS} (g : T ⟶ U) :
    familyBaseChangeMap (ambientOverBase B hX hS f) ((Over.post B.inclusion).map g) =
      Stacks.PicardFunctor.baseChangeMap B hX hS f g :=
  rfl

/-- The degree-`d` Hilbert functor of `X ⟶ S` restricted to the test schemes of the big fppf
site, with its values lifted to the universe of the Picard presheaf. Its value at `T` is the set
of degree-`d` Hilbert families in `X` over `T`, and its action on a morphism of test schemes is
base change of families. -/
abbrev hilbertFunctorOnBigFppfSite (d : ℕ) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1) :=
  (Over.post B.inclusion).op ⋙ hilbertFunctorOfRank (ambientOverBase B hX hS f) d ⋙
    uliftFunctor.{u + 1, u}

variable [SmoothOfRelativeDimension 1 (ambientOverBase B hX hS f).hom] (d : ℕ)

/-- **The Abel morphism `γ_d : Hilb^d_{X/S} ⟶ Pic_{X/S}` at the level of functors of points**,
into the presheaf `T ↦ Pic(X_T)` whose fppf sheafification is the Picard functor. It sends a
degree-`d` Hilbert family in `X` over a test scheme `T` — a relative effective Cartier divisor on
`X_T` by Tag 0B9C — to the class of its invertible sheaf in `Pic(X_T)`.

Naturality is `Stacks.Hilbert.abelClass_baseChange`: the class of the base-changed family is the
pullback of the class of the family. No representability of either functor enters. -/
def abelTransformation :
    hilbertFunctorOnBigFppfSite B hX hS f d ⟶ Stacks.PicardFunctor.picardPresheaf B hX hS f where
  app _ := TypeCat.ofHom fun Z ↦ abelClass Z.down
  naturality _ _ g := ConcreteCategory.hom_ext _ _ fun Z ↦
    (abelClass_baseChange ((Over.post B.inclusion).map g.unop) Z.down).symm

/-- The Abel morphism sends a degree-`d` Hilbert family to the class of its invertible sheaf. -/
theorem abelTransformation_app_apply (T : (BigFppfOver B S hS)ᵒᵖ)
    (Z : (hilbertFunctorOnBigFppfSite B hX hS f d).obj T) :
    (abelTransformation B hX hS f d).app T Z = abelClass Z.down :=
  rfl

/-- **The Abel morphism into the Picard functor** `Pic_{X/S}` itself: the Abel morphism into the
presheaf `T ↦ Pic(X_T)` followed by the unit of the fppf sheafification. -/
def abelTransformationToPicardFunctor :
    hilbertFunctorOnBigFppfSite B hX hS f d ⟶ Stacks.PicardFunctor.picardFunctor B hX hS f :=
  abelTransformation B hX hS f d ≫ Stacks.PicardFunctor.toPicardFunctor B hX hS f

end Stacks.Hilbert

end
