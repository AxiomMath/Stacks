module

import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.Unconditional
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStackIsStack
public import StacksFrontier.AlgebraicGeometry.Stacks.FibreEssentialSmallness
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatPresentationRepresentableDiagonal
import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableStackInSetoids

/-!
# An algebraic stack in setoids is representable by an algebraic space (Stacks 04SZ)

Let `S` be a scheme contained in a big fppf site `B` and let `𝒳` be a category fibred in
groupoids over the big fppf site of `S`. Stacks 04SZ says that, for `𝒳` an algebraic stack, the
following are equivalent: (1) `𝒳` is a stack in setoids; (2) the canonical 1-morphism
`I_𝒳 ⟶ 𝒳` from the inertia is an equivalence; (3) `𝒳` is representable by an algebraic space.

`StacksFrontier.AlgebraicGeometry.Stacks.RepresentableStackInSetoids` proves the implication
(3) ⟹ (1), and `StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStackIsStack` the equivalence
(1) ⟺ (2). This file proves the implication (1) ⟹ (3), the one that points the other way, and
assembles the three into the equivalence of Stacks 04SZ.

The proof of (1) ⟹ (3) is the source's. A stack in setoids is the category of elements of a
sheaf, namely of the `Type u` model of its presheaf of isomorphism classes (Stacks 02ZX and
Stacks 0432), so by
`AlgebraicGeometry.isRepresentableByAlgebraicSpace_iff_isAlgebraicSpace_isoClassPresheafModel`
the conclusion is exactly that this sheaf is an algebraic space. A presentation
`f : 𝒰 ⟶ 𝒳` by a category representable by an algebraic space, representable by algebraic
spaces, surjective, flat and locally of finite presentation becomes, under Stacks 04SY and
Stacks 04TC, a morphism of sheaves with those same properties whose source is an algebraic
space. The bootstrap theorem Stacks 04S6 part (3),
`AlgebraicGeometry.Space.isBootstrapAlgebraicSpaceAlongFlatSurjection`, then makes the target an
algebraic space.

## Main results

* `Stack.small_isoClassPresheaf_of_isThin_fiber`: the presheaf of isomorphism classes of a
  fibred category with thin, essentially small fibres is `u`-small, which is what makes its
  `Type u` model available.
* `Stack.isRepresentableByAlgebraicSpace_of_isStackInSetoids_of_flatPresentation`: a stack in
  setoids with a flat presentation is representable by an algebraic space.
* `Stack.isRepresentableByAlgebraicSpace_of_isStackInSetoids`: the implication (1) ⟹ (3) of
  Stacks 04SZ.
* `Stack.isStackInSetoids_tfae`: **Stacks 04SZ**, the three conditions are equivalent for an
  algebraic stack.

## Implementation notes

The implication (1) ⟹ (3) is proved from the defining data of an algebraic stack directly, with
no appeal to the quotient-groupoid presentation of Stacks 04TI, and the smooth atlas of
Stacks 026O is turned into the flat, locally-of-finite-presentation atlas the bootstrap wants by
Stacks 04TA and Stacks 04AJ pointwise on the algebraic spaces representing its base changes,
rather than through Stacks 045F.

The smallness side condition that the model of the presheaf of isomorphism classes needs is
not an extra hypothesis of the main theorem: the fibres of an algebraic stack are essentially
small by `AlgebraicGeometry.Stack.essentiallySmall_fiber_algebraicStack`, and they are thin
because `𝒳` is a stack in setoids. The general engine
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_of_isStackInSetoids_of_flatPresentation`
takes essential smallness of the fibres as an explicit hypothesis, since it does not assume
algebraicity.

The flatness hypothesis names the two instance arguments of
`AlgebraicGeometry.Stack.HasRelativeProperty` explicitly, as the fppf form of Stacks 041W is
not available as an instance in any module this one may depend on; being `Prop`-valued they are
determined up to proof irrelevance, so nothing is strengthened. This follows the spelling of
`AlgebraicGeometry.Stack.hasRepresentableDiagonal_of_flatPresentation`.

## References

* [Stacks Project, Tag 026O](https://stacks.math.columbia.edu/tag/026O)
* [Stacks Project, Tag 02ZX](https://stacks.math.columbia.edu/tag/02ZX)
* [Stacks Project, Tag 0432](https://stacks.math.columbia.edu/tag/0432)
* [Stacks Project, Tag 04AJ](https://stacks.math.columbia.edu/tag/04AJ)
* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
* [Stacks Project, Tag 04SY](https://stacks.math.columbia.edu/tag/04SY)
* [Stacks Project, Tag 04SZ](https://stacks.math.columbia.edu/tag/04SZ)
* [Stacks Project, Tag 04TA](https://stacks.math.columbia.edu/tag/04TA)
* [Stacks Project, Tag 04TC](https://stacks.math.columbia.edu/tag/04TC)
-/

@[expose] public section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Stack

universe u w

attribute [local instance] Space.isFlat_isStableUnderBaseChange
  Space.isLocallyOfFinitePresentation_isStableUnderBaseChange

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The presheaf of isomorphism classes of a fibred category with thin, essentially small
fibres is `u`-small.** Its value at `V` is the skeleton of the fibre over `V`, and for a thin
fibre essential smallness is smallness of that skeleton. This is the side condition that makes
the `Type u` model `CategoryTheory.Functor.isoClassPresheafModel` available. -/
theorem small_isoClassPresheaf_of_isThin_fiber {D : Type (u + 1)} [Category.{u} D]
    (p : D ⥤ BigFppfOver B S hS) [p.IsFibered]
    (hthin : ∀ V : BigFppfOver B S hS, Quiver.IsThin (p.Fiber V))
    (hess : ∀ V : BigFppfOver B S hS, EssentiallySmall.{u} (p.Fiber V)) :
    CategoryTheory.FunctorToTypes.Small.{u} p.isoClassPresheaf := fun V =>
  (CategoryTheory.Functor.small_isoClassPresheaf_obj_iff_essentiallySmall.{u} p V.unop
    (hthin V.unop)).2 (hess V.unop)

section Engine

variable {𝒰 𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}

/-- **A stack in setoids with a flat presentation is representable by an algebraic space.**

Let `f : 𝒰 ⟶ 𝒳` be a 1-morphism of categories fibred in groupoids over the big fppf site of `S`
with `𝒳` a stack in setoids with essentially small fibres, with `𝒰` representable by an
algebraic space, and with `f` representable by algebraic spaces, surjective, flat and locally of
finite presentation. Then `𝒳` is representable by an algebraic space.

This is the engine of the implication (1) ⟹ (3) of Stacks 04SZ; algebraicity of `𝒳` is not
used, only the presentation data it provides. The last step is the bootstrap theorem
Stacks 04S6 part (3), `AlgebraicGeometry.Space.isBootstrapAlgebraicSpaceAlongFlatSurjection`,
applied to the model of the presheaf of isomorphism classes of `𝒳`. -/
theorem isRepresentableByAlgebraicSpace_of_isStackInSetoids_of_flatPresentation (f : 𝒰 ⟶ 𝒳)
    (h𝒳 : 𝒳.val.p.IsStackInSetoids (BigFppfOver.topology B S hS))
    (hess : ∀ V : BigFppfOver B S hS, EssentiallySmall.{u} (𝒳.val.p.Fiber V))
    (h𝒰 : IsRepresentableByAlgebraicSpace B S hS 𝒰)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom)
    (hsurj : HasRelativeProperty.{u, u, u + 1, u + 1} B S hS
      (Space.surjectiveMorphismProperty B S hS) f hf)
    (hflat : @HasRelativeProperty.{u, u, u + 1, u + 1} B S hS
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (k : X ⟶ Y) => Space.IsFlat B S hS k.hom)
      (Space.isFlat_isStableUnderBaseChange B S hS)
      ((Space.isFlat_isLocalAtTarget_fpqc B S hS).of_le
        (Space.fppfPrecoverage_le_fpqcPrecoverage B S hS))
      𝒰 𝒳 f hf)
    (hlfp : HasRelativeProperty.{u, u, u + 1, u + 1} B S hS
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (k : X ⟶ Y) =>
        Space.IsLocallyOfFinitePresentation B S hS k.hom) f hf) :
    IsRepresentableByAlgebraicSpace B S hS 𝒳 := by
  have : MorphismProperty.IsLocalAtTarget
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (k : X ⟶ Y) => Space.IsFlat B S hS k.hom)
      (Space.Topology.fppf.precoverage.{u, u + 1} B S hS) :=
    (Space.isFlat_isLocalAtTarget_fpqc B S hS).of_le
      (Space.fppfPrecoverage_le_fpqcPrecoverage B S hS)
  obtain ⟨h𝒰set, h𝒰iso⟩ := (isRepresentableByAlgebraicSpace_iff B S hS 𝒰).1 h𝒰
  have h𝒳set : 𝒳.val.p.IsFiberedInSetoids := ⟨𝒳.isFiberedInGroupoids, h𝒳.fiber_isThin⟩
  have : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
  have : 𝒰.val.p.IsFibered := 𝒰.isFiberedInGroupoids.isFibered
  have : CategoryTheory.FunctorToTypes.Small.{u} 𝒳.val.p.isoClassPresheaf :=
    small_isoClassPresheaf_of_isThin_fiber B S hS 𝒳.val.p h𝒳.fiber_isThin hess
  have : CategoryTheory.FunctorToTypes.Small.{u} 𝒰.val.p.isoClassPresheaf :=
    small_isoClassPresheaf_of_isAlgebraicSpaceIsoClassPresheaf B S hS _ h𝒰iso
  have h𝒰model : IsAlgebraicSpace B S hS
      (CategoryTheory.Functor.isoClassPresheafModel.{u} 𝒰.val.p) :=
    (isAlgebraicSpaceIsoClassPresheaf_iff_isAlgebraicSpace_isoClassPresheafModel B S hS _).1
      h𝒰iso
  have h𝒳sheaf := isSheaf_isoClassPresheafModel B S hS 𝒳.val.p h𝒳
  -- the two categories as categories fibred in setoids, and the induced map of models
  let 𝒳s : CatFiberedInSetoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS) :=
    CatFiberedInSetoids.mk 𝒳.val h𝒳set
  let 𝒰s : CatFiberedInSetoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS) :=
    CatFiberedInSetoids.mk 𝒰.val h𝒰set
  let fs : 𝒰s ⟶ 𝒳s := Bicategory.InducedBicategory.mkHom f.hom
  let a := CategoryTheory.Functor.isoClassPresheafModelMap.{u} 𝒰s.val.p 𝒳s.val.p
    (CatFiberedInGroupoids.homFunctor_comp_p fs)
  have ha : IsoClassCompatible B S hS fs
      (CategoryTheory.Functor.isoClassPresheafModel.{u} 𝒰s.val.p)
      (CategoryTheory.Functor.isoClassPresheafModel.{u} 𝒳s.val.p)
      (CategoryTheory.Functor.isoClassPresheafModelEquiv.{u} 𝒰s.val.p)
      (CategoryTheory.Functor.isoClassPresheafModelEquiv.{u} 𝒳s.val.p) a := fun W z =>
    CategoryTheory.Functor.isoClassPresheafModelMap_app_isoClassMk.{u} 𝒰s.val.p 𝒳s.val.p _ z
  have hfrep : IsRepresentableByAlgebraicSpaces B S hS
      (CatFiberedInSetoids.inclusion.map fs).hom := hf
  have harep := (isoClassMap_isRepresentableByAlgebraicSpaces_iff_model.{u, u, u + 1}
    B S hS fs a ha).2 hfrep
  -- Stacks 04S6 part (3) on the model of the presheaf of isomorphism classes of `𝒳`
  refine (isRepresentableByAlgebraicSpace_iff_isAlgebraicSpace_isoClassPresheafModel B S hS
    𝒳).2 ⟨h𝒳set, ?_⟩
  have key (P : MorphismProperty (AlgebraicSpaces B S hS)) [P.IsStableUnderBaseChange]
      [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, u + 1} B S hS)]
      (h : HasRelativeProperty.{u, u, u + 1, u + 1} B S hS P f hf) :=
    (isoClassMap_holdsOnEverySchemePoint_iff_model.{u, u, u + 1, u + 1} B S hS fs P a ha
      hfrep).2 h
  exact Space.isBootstrapAlgebraicSpaceAlongFlatSurjection B S hS a h𝒳sheaf h𝒰model harep
    (key _ hsurj) (key _ hflat) (key _ hlfp)

end Engine

section AlgebraicStack

variable (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))

/-- **The implication (1) ⟹ (3) of Stacks 04SZ.** An algebraic stack over the big fppf site of
`S` which is a stack in setoids for the fppf topology is representable by an algebraic space over
`S`.

The scheme presentation of the algebraic-stack condition is surjective and smooth, hence flat and
locally of finite presentation by Stacks 04TA and Stacks 04AJ; the fibres of an algebraic stack
are essentially small, and they are thin because `𝒳` is a stack in setoids, which is what makes
the `Type u` model of the presheaf of isomorphism classes available. The bootstrap theorem
Stacks 04S6 part (3) then makes that model an algebraic space. -/
theorem isRepresentableByAlgebraicSpace_of_isStackInSetoids
    (halg : IsAlgebraicStack.{u, w} B S hS 𝒳.val)
    (h𝒳 : 𝒳.val.p.IsStackInSetoids (BigFppfOver.topology B S hS)) :
    IsRepresentableByAlgebraicSpace B S hS 𝒳 := by
  have hess : ∀ V : BigFppfOver B S hS, EssentiallySmall.{u} (𝒳.val.p.Fiber V) :=
    essentiallySmall_fiber_algebraicStack B S hS ⟨𝒳, halg⟩
  obtain ⟨hgrp, -, -, U, g, hg, hgprop⟩ := halg
  exact isRepresentableByAlgebraicSpace_of_isStackInSetoids_of_flatPresentation B S hS
    (𝒰 := schemeFibredCategory B S hS U) (Bicategory.InducedBicategory.mkHom g) h𝒳 hess
    (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS U) hg
    (fun V y hy F hF h => (hgprop V y hy F hF h).1)
    (fun V y hy F hF h => Space.isFlat_of_isSmooth B S hS _ (hgprop V y hy F hF h).2)
    (fun V y hy F hF h =>
      Space.isLocallyOfFinitePresentation_of_isSmooth B S hS (hgprop V y hy F hF h).2)

/-- **Stacks 04SZ.** For an algebraic stack `𝒳` over the big fppf site of `S` the following are
equivalent:

1. `𝒳` is a stack in setoids;
2. the canonical 1-morphism `I_𝒳 ⟶ 𝒳` from the inertia is an equivalence;
3. `𝒳` is representable by an algebraic space.

The equivalence (1) ⟺ (2) is
`AlgebraicGeometry.Stack.isStackInSetoids_iff_inertiaProjection_isEquivalence_of_isAlgebraicStack`,
the implication (3) ⟹ (1) is
`AlgebraicGeometry.Stack.isStackInSetoids_of_isRepresentableByAlgebraicSpace`, and the
implication (1) ⟹ (3) is
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_of_isStackInSetoids`. -/
@[stacks 04SZ]
theorem isStackInSetoids_tfae (halg : IsAlgebraicStack.{u, w} B S hS 𝒳.val) :
    List.TFAE
      [𝒳.val.p.IsStackInSetoids (BigFppfOver.topology B S hS),
        (RelativeInertia.π 𝒳.val.p : AbsoluteInertia 𝒳.val.p ⥤ 𝒳.val.obj).IsEquivalence,
        IsRepresentableByAlgebraicSpace B S hS 𝒳] := by
  tfae_have 1 ↔ 2 :=
    isStackInSetoids_iff_inertiaProjection_isEquivalence_of_isAlgebraicStack B S hS 𝒳 halg
  tfae_have 1 → 3 := isRepresentableByAlgebraicSpace_of_isStackInSetoids B S hS 𝒳 halg
  tfae_have 3 → 1 := isStackInSetoids_of_isRepresentableByAlgebraicSpace B S hS 𝒳
  tfae_finish

end AlgebraicStack

end AlgebraicGeometry.Stack

end
