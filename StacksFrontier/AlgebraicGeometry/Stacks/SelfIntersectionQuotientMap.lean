module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStack
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStackIsStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersectionCanonicalMap
public import StacksFrontier.CategoryTheory.Sites.Stack.Transport.UliftStack
public import StacksFrontier.CategoryTheory.Sites.Stackification.UniversalPropertyGroupoid

/-!
# The canonical morphism from the quotient stack of the self-intersection groupoid

Let `S` be a scheme contained in a big fppf site, let `𝒰` and `𝒳` be categories fibred in groupoids
over the big fppf site of `S`, and let `f : 𝒰 ⟶ 𝒳` be a 1-morphism. Suppose that `𝒰` and its
self-intersection are represented by algebraic spaces through chosen equivalences `eU` and `eR`
and that `𝒰` is fibred in setoids, so that the groupoid in algebraic spaces
`AlgebraicGeometry.Stack.SelfIntersection.selfIntersectionGroupoid` is defined, together with the
1-morphism `AlgebraicGeometry.Stack.SelfIntersection.toStackOfPointwiseGroupoid` from its pointwise
groupoid fibration to `𝒳`.

The quotient stack `[U/R]` is the stackification of the pointwise groupoid fibration
(`AlgebraicGeometry.Stack.quotientStack`), so the universal property of the stackification
(`CategoryTheory.Functor.Stackification.extendGroupoid`) extends this 1-morphism to a 1-morphism
from `[U/R]` to `𝒳`, unique up to a vertical 2-isomorphism. Since the quotient stack lives at
morphism universe `u + 1`, the extension is formed with values in the universe lift of `𝒳` and
then brought back to `𝒳` by `CategoryTheory.BasedCategory.uliftDown`.

## Main definitions

* `AlgebraicGeometry.Stack.SelfIntersection.toStackUliftOfPointwise`: the 1-morphism from the
  presentation of the quotient stack to the universe lift of `𝒳`.
* `AlgebraicGeometry.Stack.SelfIntersection.canonicalMapUlift`: its extension to the quotient
  stack.
* `AlgebraicGeometry.Stack.SelfIntersection.canonicalMapToStack`: the canonical morphism from the
  quotient stack to `𝒳`.
* `AlgebraicGeometry.Stack.SelfIntersection.unitCanonicalMapUlift`: the vertical 2-isomorphism
  filling the triangle.

## Main results

* `AlgebraicGeometry.Stack.SelfIntersection.isStack_stackUlift`: the universe lift of an
  algebraic stack is a stack over the big fppf site.

## References

* [Stacks Project, Tag 04T4](https://stacks.math.columbia.edu/tag/04T4)
* [Stacks Project, Tag 0436](https://stacks.math.columbia.edu/tag/0436)
-/


@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack.SelfIntersection

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {𝒰 𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
variable {f : 𝒰.val ⥤ᵇ 𝒳.val}
variable {U R : AlgebraicSpaces B S hS}
variable
  (eU : StacksRepresentableCFG.EquivalenceOver
    𝒰.val.p (presheafOfCategories (U.obj ⋙ typeToCat)).p)
  (eR : StacksRepresentableCFG.EquivalenceOver
    (relation B S hS 𝒰 𝒳 f).val.p
    (presheafOfCategories (R.obj ⋙ typeToCat)).p)

/-- The universe lift of `𝒳`, with objects and morphisms in `Type (u + 1)`. -/
noncomputable abbrev stackUlift (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1}
    (BigFppfOver B S hS)) : BasedCategory.{u + 1, u + 1} (BigFppfOver B S hS) :=
  (𝒳.val).ulift.{u, u + 1, u, u + 1, u + 1, u + 1}

/-- The universe lift of an algebraic stack is a stack over the big fppf site. -/
theorem isStack_stackUlift (h𝒳 : IsAlgebraicStack B S hS 𝒳.val) :
    (stackUlift 𝒳).p.IsStack (BigFppfOver.topology B S hS) :=
  BasedCategory.isStack_ulift 𝒳.val (BigFppfOver.topology B S hS)
    (isStack_of_isAlgebraicStack B S hS h𝒳)

/-- The 1-morphism from the presentation of the quotient stack to the universe lift of `𝒳`: the
inverse of `AlgebraicGeometry.Stack.quotientPrestackEquivalence`, followed by
`AlgebraicGeometry.Stack.SelfIntersection.toStackOfPointwiseGroupoid` and by the universe lift of
`𝒳`. -/
noncomputable def toStackUliftOfPointwise (hsetU : 𝒰.val.p.IsFiberedInSetoids) :
    (Stack.quotientPrestack (selfIntersectionGroupoid eU eR hsetU)).obj ⥤ (stackUlift 𝒳).obj :=
  (Stack.quotientPrestackEquivalence (selfIntersectionGroupoid eU eR hsetU)).inverse ⋙
    (toStackOfPointwiseGroupoid eU eR hsetU).toFunctor ⋙ BasedCategory.uliftUp 𝒳.val

/-- `toStackUliftOfPointwise` commutes on the nose with the structure functors to the big fppf
site. -/
theorem toStackUliftOfPointwise_comp (hsetU : 𝒰.val.p.IsFiberedInSetoids) :
    toStackUliftOfPointwise eU eR hsetU ⋙ (stackUlift 𝒳).p =
      (Stack.quotientPrestack (selfIntersectionGroupoid eU eR hsetU)).p := by
  show _ ⋙ (toStackOfPointwiseGroupoid eU eR hsetU).toFunctor ⋙
    (BasedCategory.uliftUp 𝒳.val ⋙ (stackUlift 𝒳).p) = _
  rw [BasedCategory.uliftUp_comp 𝒳.val, (toStackOfPointwiseGroupoid eU eR hsetU).w]
  rfl

/-- The extension of `toStackUliftOfPointwise` along the stackification
`AlgebraicGeometry.Stack.toQuotientStack` of the presentation of the quotient stack. -/
noncomputable def canonicalMapUlift (hsetU : 𝒰.val.p.IsFiberedInSetoids)
    (h𝒳 : IsAlgebraicStack B S hS 𝒳.val) :
    (Stack.quotientStack (selfIntersectionGroupoid eU eR hsetU)).obj ⥤ (stackUlift 𝒳).obj :=
  Functor.Stackification.extendGroupoid
    (Stack.isFiberedInGroupoids_quotientPrestack (selfIntersectionGroupoid eU eR hsetU))
    (Stack.isFiberedInGroupoids_quotientStack (selfIntersectionGroupoid eU eR hsetU))
    (Stack.isStack_quotientStack (selfIntersectionGroupoid eU eR hsetU))
    (BasedCategory.isFiberedInGroupoids_ulift 𝒳.val 𝒳.isFiberedInGroupoids)
    (isStack_stackUlift h𝒳)
    (Stack.isFibredOneMorphism_toQuotientStack (selfIntersectionGroupoid eU eR hsetU)).comp_eq
    (toStackUliftOfPointwise_comp eU eR hsetU)
    (Stack.isLocallyBijective_toQuotientStack (selfIntersectionGroupoid eU eR hsetU))
    (Stack.essImage_toQuotientStack (selfIntersectionGroupoid eU eR hsetU))

/-- `canonicalMapUlift` commutes on the nose with the structure functors to the big fppf site. -/
theorem canonicalMapUlift_comp_eq (hsetU : 𝒰.val.p.IsFiberedInSetoids)
    (h𝒳 : IsAlgebraicStack B S hS 𝒳.val) :
    canonicalMapUlift eU eR hsetU h𝒳 ⋙ (stackUlift 𝒳).p =
      (Stack.quotientStack (selfIntersectionGroupoid eU eR hsetU)).p :=
  Functor.Stackification.extendGroupoid_comp_eq _ _ _ _ _ _ _ _ _

/-- The canonical morphism from the quotient stack of the groupoid of the self-intersection to
the algebraic stack `𝒳`, as a 1-morphism over the big fppf site: the extension
`canonicalMapUlift` followed by `CategoryTheory.BasedCategory.uliftDown`. -/
noncomputable def canonicalMapToStack (hsetU : 𝒰.val.p.IsFiberedInSetoids)
    (h𝒳 : IsAlgebraicStack B S hS 𝒳.val) :
    (Stack.quotientStack (selfIntersectionGroupoid eU eR hsetU)) ⥤ᵇ 𝒳.val where
  toFunctor := canonicalMapUlift eU eR hsetU h𝒳 ⋙ BasedCategory.uliftDown 𝒳.val
  w := by
    rw [Functor.assoc, BasedCategory.uliftDown_comp 𝒳.val, canonicalMapUlift_comp_eq]

/-- The 2-isomorphism filling the triangle: the composite of the canonical morphism to the
quotient stack with the extension `canonicalMapUlift` is isomorphic to the 1-morphism
`toStackUliftOfPointwise` it extends. -/
noncomputable def unitCanonicalMapUlift (hsetU : 𝒰.val.p.IsFiberedInSetoids)
    (h𝒳 : IsAlgebraicStack B S hS 𝒳.val) :
    Stack.toQuotientStack (selfIntersectionGroupoid eU eR hsetU) ⋙
        canonicalMapUlift eU eR hsetU h𝒳 ≅ toStackUliftOfPointwise eU eR hsetU :=
  Functor.Stackification.unitGroupoid _ _ _ _ _ _ _ _ _

/-- Every component of `unitCanonicalMapUlift` is vertical over the big fppf site. -/
lemma isHomLift_unitCanonicalMapUlift_app (hsetU : 𝒰.val.p.IsFiberedInSetoids)
    (h𝒳 : IsAlgebraicStack B S hS 𝒳.val)
    (A : (Stack.quotientPrestack (selfIntersectionGroupoid eU eR hsetU)).obj) :
    (stackUlift 𝒳).p.IsHomLift
      (𝟙 ((Stack.quotientPrestack (selfIntersectionGroupoid eU eR hsetU)).p.obj A))
      ((unitCanonicalMapUlift eU eR hsetU h𝒳).hom.app A) :=
  Functor.Stackification.isHomLift_unitGroupoid_app _ _ _ _ _ _ _ _ _ A

end AlgebraicGeometry.Stack.SelfIntersection

end
