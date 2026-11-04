module

public import Mathlib.CategoryTheory.Groupoid.Discrete
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamiliesFibered
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesNodal
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesOpenSubstackFromBaseLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.NodalOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeAsSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedPermanence
public import StacksFrontier.AlgebraicGeometry.Stacks.Algebraic.RepresentableBySpace.Characterization
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableMorphismAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.Substack
public import StacksFrontier.CategoryTheory.FiberedCategory.FiberedInSetoids
public import StacksFrontier.CategoryTheory.FiberedCategory.FiberedInSetoidsSupplement
public import StacksFrontier.CategoryTheory.FiberedCategory.OfPresheaf
public import StacksFrontier.CategoryTheory.FiberedCategory.PresheafElementsEquivalence
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.Criterion
public import StacksFrontier.CategoryTheory.Sites.Localization.Relocalize
import all StacksFrontier.AlgebraicGeometry.Quot.CurvesNodal

/-!
# CurvesNodalUnconditional

The generalizations made by this development of declarations of
`StacksFrontier.AlgebraicGeometry.Quot.CurvesNodal`. That module keeps its statements as they are;
each declaration here restating one of them carries its name with the suffix `_unconditional` (or
`Unconditional` for a definition), and the declarations that depend on those restatements follow
them.
-/

@[expose] public noncomputable section

attribute [local implicit_reducible] AlgebraicGeometry.curvesProjectionOver

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

namespace AlgebraicGeometry

attribute [local instance] Space.pointTopology

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-! ### The point set of the maximal at-worst-nodal open subspace -/

/-! ### The locus in the base of a family -/

/-- The property of a family of curves of being at-worst-nodal of relative dimension one, read as
a property of the objects of the category of families of curves. -/
def isNodalCurveFamily : ObjectProperty (CurveFamily B hZ) := fun F =>
  Space.IsAtWorstNodalOfRelativeDimensionOne B integerBase hZ F.toBase.hom

/-- A family of curves mapping to an at-worst-nodal family of relative dimension one is itself
at-worst-nodal of relative dimension one. -/
@[stacks 0DSY "the open substack Curves^nodal, base-change clause: the at-worst-nodal condition \
is inherited along every morphism of families of curves, and a morphism of families is a \
cartesian square, so the subcategory is closed under base change. Unconditional: no \
presentation of Curves as an algebraic stack (Tag 0D5A) and no part of Tag 04S6 is assumed"]
theorem isNodalCurveFamily_of_hom {F G : CurveFamily B hZ} (a : F ⟶ G)
    (hG : isNodalCurveFamily B hZ G) : isNodalCurveFamily B hZ F :=
  nodal_of_curveFamily_hom B hZ a hG

/-- **Stacks 0DSY.** The nodal condition cuts a *strictly* full subcategory out of the category
of families of curves: it is invariant under isomorphism. -/
@[stacks 0DSY "the open substack Curves^nodal, strict-fullness clause: the at-worst-nodal \
condition is invariant under isomorphism of families of curves, so it cuts a strictly full \
subcategory out of Curves. Unconditional: no presentation of Curves as an algebraic stack \
(Tag 0D5A) and no part of Tag 04S6 is assumed"]
theorem isClosedUnderIsomorphisms_isNodalCurveFamily :
    (isNodalCurveFamily B hZ).IsClosedUnderIsomorphisms :=
  isClosedUnderIsomorphisms_of_curveFamily_hom B hZ (isNodalCurveFamily B hZ)
    (isNodalCurveFamily_of_hom B hZ)

/-! ### Stacks 0DSY, part (1) -/

/-- **Stacks 0DSY, part (1).** The open substack `Curves^{nodal}` of families of curves which are
at-worst-nodal of relative dimension one, together with the characterisation of its objects: an
object of the stack belongs to it exactly when the family of curves it classifies is
at-worst-nodal of relative dimension one.

This is `AlgebraicGeometry.curvesOpenSubstackOfBaseLocus`, the method of Section 109.6, at the
locus `AlgebraicGeometry.exists_nodal_baseOpen`.

The algebraic stack of curves is a hypothesis: `𝒳` is any algebraic stack over the big fppf site
of the integers whose objects are identified with families of curves by an equivalence `E` over
that site. Nothing else is assumed; in particular no part of Stacks 04S6 is, the algebraic-stack
field of the substack coming from the unconditional Stacks 05UM.

Part (2) of the source, the characterisation for a proper scheme over a field, is not asserted
here.

The definition carries `@[no_expose]`: its body names the private helpers that build the
substack, so it may not be exposed. Nothing downstream needs to unfold it — the
characterisation of its objects is the second component of the subtype. -/
@[stacks 0DSY "the open substack and part (1): the characterisation on every family of curves, \
given a presentation of the algebraic stack of curves. Part (2), the characterisation for a \
proper scheme over a field, is registered separately on \
`AlgebraicGeometry.lifts_nodalCurves_curveFamilyOfProperOverField_iff`",
  no_expose]
def nodalCurvesOpenSubstackUnconditional
    (𝒳 : Stack.AlgebraicStacks.{u, w} B integerBase hZ)
    (E : CurveFamily B hZ ≌ 𝒳.val.val.obj)
    (hE : E.functor ⋙ 𝒳.val.val.p = curvesProjectionOver B hZ) :
    {U : Stack.OpenSubstack 𝒳 //
      ∀ F : CurveFamily B hZ,
        U.property (E.functor.obj F) ↔
          Space.IsAtWorstNodalOfRelativeDimensionOne B integerBase hZ F.toBase.hom} :=
  curvesOpenSubstackOfBaseLocus B hZ (isNodalCurveFamily B hZ)
    (fun a hG => isNodalCurveFamily_of_hom B hZ a hG) (exists_nodal_baseOpen B hZ) 𝒳 E hE

/-- **Stacks 0DSY, part (1).** The classifying object of a family of curves lifts through the
inclusion of the nodal open substack exactly when the family is at-worst-nodal of relative
dimension one.

As for `AlgebraicGeometry.nodalCurvesOpenSubstackUnconditional`, the algebraic stack of curves
and its identification with families of curves are hypotheses, and nothing else is assumed. -/
@[stacks 0DSY "part (1): the classifying morphism of a family factors through the nodal open \
substack iff the family is at-worst-nodal of relative dimension one, given a presentation of \
the algebraic stack of curves. Part (2), the characterisation for a proper scheme over a \
field, is registered separately on \
`AlgebraicGeometry.lifts_nodalCurves_curveFamilyOfProperOverField_iff`"]
theorem classifying_factors_nodalCurvesOpenSubstack_iff_unconditional
    (𝒳 : Stack.AlgebraicStacks.{u, w} B integerBase hZ)
    (E : CurveFamily B hZ ≌ 𝒳.val.val.obj)
    (hE : E.functor ⋙ 𝒳.val.val.p = curvesProjectionOver B hZ)
    (F : CurveFamily B hZ) :
    (∃ Y : (nodalCurvesOpenSubstackUnconditional B hZ 𝒳 E hE).1.property.FullSubcategory,
      Y.obj = E.functor.obj F) ↔
      Space.IsAtWorstNodalOfRelativeDimensionOne B integerBase hZ F.toBase.hom := by
  have hchar := (nodalCurvesOpenSubstackUnconditional B hZ 𝒳 E hE).2 F
  constructor
  · rintro ⟨Y, hY⟩
    exact hchar.mp (hY ▸ Y.property)
  · intro hN
    exact ⟨⟨E.functor.obj F, hchar.mpr hN⟩, rfl⟩

/-! ### Stacks 0DSY over the category of curves itself -/

/-- **Stacks 0DSY.** The category `Curves^{nodal}` of families of curves which are at-worst-nodal
of relative dimension one, as an object of the 2-category of categories fibred in groupoids over
the big fppf site of `Spec(ℤ)`. -/
@[stacks 0DSY "the open substack Curves^nodal itself, as the strictly full subcategory of \
Curves spanned by the families which are at-worst-nodal of relative dimension one, read as an \
object of the 2-category of categories fibred in groupoids over the big fppf site of Spec(Z). \
Unconditional: no presentation of Curves as an algebraic stack (Tag 0D5A) and no part of \
Tag 04S6 is assumed"]
def nodalCurvesFiberedCategory :
    CatFiberedInGroupoids.{u, u + 1, u + 1, u + 1} (BigFppfOver B integerBase hZ) :=
  curvesFullSubcategoryFibered B hZ (isNodalCurveFamily B hZ)
    (fun a h => isNodalCurveFamily_of_hom B hZ a h)

/-- **Stacks 0DSY.** The inclusion `Curves^{nodal} ⊂ Curves`, as a 1-morphism of categories
fibred in groupoids over the big fppf site of `Spec(ℤ)`. -/
@[stacks 0DSY "the inclusion Curves^nodal ⊂ Curves of the open substack, as a 1-morphism of \
categories fibred in groupoids over the big fppf site of Spec(Z). Unconditional: no \
presentation of Curves as an algebraic stack (Tag 0D5A) and no part of Tag 04S6 is assumed"]
def nodalCurvesInclusion :
    nodalCurvesFiberedCategory B hZ ⟶ curvesFiberedCategory B hZ :=
  curvesFullSubcategoryInclusion B hZ (isNodalCurveFamily B hZ)
    (fun a h => isNodalCurveFamily_of_hom B hZ a h)

/-- **Stacks 0DSY.** The inclusion `Curves^{nodal} ⊂ Curves` is representable by algebraic
spaces. -/
@[stacks 0DSY "the open substack Curves^nodal, representability clause: the inclusion \
Curves^nodal ⊂ Curves is representable by algebraic spaces. Unconditional: no presentation of \
Curves as an algebraic stack (Tag 0D5A) and no part of Tag 04S6 is assumed"]
theorem isRepresentableByAlgebraicSpaces_nodalCurvesInclusion :
    Stack.IsRepresentableByAlgebraicSpaces B integerBase hZ (nodalCurvesInclusion B hZ).hom :=
  isRepresentableByAlgebraicSpaces_curvesFullSubcategoryInclusion B hZ (isNodalCurveFamily B hZ)
    (isNodalCurveFamily_of_hom B hZ) (exists_nodal_baseOpen B hZ)

/-- **Stacks 0DSY.** The inclusion `Curves^{nodal} ⊂ Curves` is an open immersion: every
algebraic space representing one of its base changes along a scheme-valued point of `Curves` has
open immersion structural morphism. -/
@[stacks 0DSY "the open substack Curves^nodal, open-immersion clause: the inclusion \
Curves^nodal ⊂ Curves is an open immersion in the sense of Tag 04XB. Unconditional: no \
presentation of Curves as an algebraic stack (Tag 0D5A) and no part of Tag 04S6 is assumed"]
theorem isOpenImmersion_nodalCurvesInclusion :
    Stack.IsOpenImmersion B integerBase hZ (nodalCurvesInclusion B hZ) :=
  isOpenImmersion_curvesFullSubcategoryInclusion B hZ (isNodalCurveFamily B hZ)
    (isNodalCurveFamily_of_hom B hZ) (exists_nodal_baseOpen B hZ)

/-- **Stacks 0DSY, part (1).** A family of curves lifts through the inclusion
`Curves^{nodal} ⊂ Curves` exactly when it is at-worst-nodal of relative dimension one. -/
@[stacks 0DSY "part (1): the classifying morphism of a family of curves factors through \
Curves^nodal -- that is, the family lifts through the inclusion of the strictly full \
subcategory -- if and only if the family is at-worst-nodal of relative dimension one. \
Unconditional: no presentation of Curves as an algebraic stack (Tag 0D5A) and no part of \
Tag 04S6 is assumed"]
theorem lifts_nodalCurves_iff (F : CurveFamily B hZ) :
    (∃ Y : (isNodalCurveFamily B hZ).FullSubcategory, Y.obj = F) ↔
      Space.IsAtWorstNodalOfRelativeDimensionOne B integerBase hZ F.toBase.hom :=
  lifts_curvesFullSubcategory_iff B hZ (isNodalCurveFamily B hZ) F

/-- **Stacks 0DSY, part (1).** The classifying morphism of a family of curves factors through
`Curves^{nodal}` exactly when the family is at-worst-nodal of relative dimension one, where
factoring through `Curves^{nodal}` is being in the image on objects of the 1-morphism
`AlgebraicGeometry.nodalCurvesInclusion` itself.

This is `AlgebraicGeometry.lifts_nodalCurves_iff` read through that 1-morphism, so that part (1)
is asserted about the very object whose inclusion is proved representable by algebraic spaces
and an open immersion in
`AlgebraicGeometry.isRepresentableByAlgebraicSpaces_nodalCurvesInclusion` and
`AlgebraicGeometry.isOpenImmersion_nodalCurvesInclusion`.

The declaration carries no hypothesis beyond the site and its containing `Spec(ℤ)`: there is no
algebraic stack `𝒳` and no equivalence identifying it with the category of families of
curves. -/
@[stacks 0DSY "part (1), stated through the inclusion 1-morphism \
AlgebraicGeometry.nodalCurvesInclusion of the open substack: a family of curves is in the image \
on objects of Curves^nodal ⟶ Curves if and only if it is at-worst-nodal of relative dimension \
one. Unconditional: no presentation of Curves as an algebraic stack (Tag 0D5A) and no part of \
Tag 04S6 is assumed"]
theorem lifts_nodalCurvesInclusion_iff (F : CurveFamily B hZ) :
    (∃ Y : (nodalCurvesFiberedCategory B hZ).based.obj,
        (CatFiberedInGroupoids.homFunctor (nodalCurvesInclusion B hZ)).obj Y = F) ↔
      Space.IsAtWorstNodalOfRelativeDimensionOne B integerBase hZ F.toBase.hom :=
  lifts_curvesFullSubcategoryInclusion_iff B hZ (isNodalCurveFamily B hZ)
    (isNodalCurveFamily_of_hom B hZ) F

end AlgebraicGeometry

end
