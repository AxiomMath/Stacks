module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.BootstrapEtaleSurjective
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStackIsStack
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeEtaleComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableDeligneMumford
public import StacksFrontier.AlgebraicGeometry.Stacks.StackInSetoidsRepresentableBySpace

/-!
# Deligne-Mumford stacks without automorphisms (Stacks 045H)

Let `S` be a scheme contained in a big fppf site `B` and let `𝒳` be a category fibred in
groupoids over the big fppf site of `S`. Stacks 045H says that, for `𝒳` an algebraic stack, the
following are equivalent:

1. `𝒳` is a Deligne-Mumford stack and a stack in setoids,
2. `𝒳` is a Deligne-Mumford stack and the canonical 1-morphism `I_𝒳 ⟶ 𝒳` from the inertia is an
   equivalence, and
3. `𝒳` is representable by an algebraic space.

All three conditions are proved equivalent here. As in
`StacksFrontier.AlgebraicGeometry.Stacks.RepresentableStackInSetoids`, the implications out of (3)
need no algebraicity hypothesis and none is assumed: representability by an algebraic space
already makes `𝒳` a Deligne-Mumford stack, by Stacks 03YS part (1).

## Main results

* `AlgebraicGeometry.Stack`
  `.isDeligneMumfordStack_and_isStackInSetoids_of_isRepresentableByAlgebraicSpace`:
  **Stacks 045H**, the implication (3) ⟹ (1).
* `AlgebraicGeometry.Stack`
  `.isDeligneMumfordStack_and_inertiaProjection_isEquivalence_of_isRepresentableByAlgebraicSpace`:
  **Stacks 045H**, the implication (3) ⟹ (2).
* `AlgebraicGeometry.Stack`
  `.isStackInSetoids_iff_inertiaProjection_isEquivalence_of_isDeligneMumfordStack`:
  **Stacks 045H**, the equivalence of parts (1) and (2).
* `AlgebraicGeometry.Stack`
  `.isRepresentableByAlgebraicSpace_of_isStackInSetoids_of_etalePresentation`: a stack in
  setoids with a surjective étale presentation by a category representable by an algebraic
  space is representable by an algebraic space.
* `AlgebraicGeometry.Stack`
  `.isRepresentableByAlgebraicSpace_of_isDeligneMumfordStack_isStackInSetoids`:
  **Stacks 045H**, the implication (1) ⟹ (3).
* `AlgebraicGeometry.Stack.isDeligneMumfordStack_isStackInSetoids_tfae`: **Stacks 045H**, the
  equivalence of all three parts.

## Implementation notes

The two conjuncts of (1) come from the two implications out of (3) proved in the library:
`AlgebraicGeometry.Stack.isDeligneMumfordStack_of_isRepresentableByAlgebraicSpace` (**Stacks
03YS**, part (1)) and `AlgebraicGeometry.Stack.isStackInSetoids_of_isRepresentableByAlgebraicSpace`
(**Stacks 04SZ**, the implication (3) ⟹ (1)). The implication (3) ⟹ (2) is the same pair with the
setoid conjunct replaced by
`AlgebraicGeometry.Stack.isEquivalence_inertiaProjection_of_isRepresentableByAlgebraicSpace`.

The equivalence of (1) and (2) is Stacks 04ZM,
`CategoryTheory.RelativeInertia.π_isEquivalence_iff`, whose stack hypothesis is supplied by the
algebraic-stack conjunct of the Deligne-Mumford condition through
`AlgebraicGeometry.Stack.isStackInSetoids_iff_inertiaProjection_isEquivalence_of_isAlgebraicStack`
(**Stacks 04SZ**, parts (1) and (2)). Stacks 045H's own statement of part (2) is "the canonical
1-morphism `I_𝒳 ⟶ 𝒳` is an equivalence", and the canonical 1-morphism is
`CategoryTheory.RelativeInertia.π` with `CategoryTheory.RelativeInertia.neutralSection` as its
inverse over the base; both of the general lemmas recording that are cited below rather than
restated.

The implication (1) ⟹ (3) is the source's proof. A stack in setoids is the category of elements
of the `Type u` model of its presheaf of isomorphism classes, and that presheaf is a sheaf by
**Stacks 0432**, so `AlgebraicGeometry.Stack`
`.isRepresentableByAlgebraicSpace_iff_isAlgebraicSpace_isoClassPresheafModel` (**Stacks 02ZX**)
reduces the conclusion to that sheaf being an algebraic space. The surjective étale presentation
by a scheme that the Deligne-Mumford condition provides becomes, under **Stacks 04SY** and
**Stacks 04TC**, a morphism of sheaves which is representable by algebraic spaces, surjective
and étale, and whose source is an algebraic space; the bootstrap theorem **Stacks 03Y3** under
its conditions (a) and (b), `AlgebraicGeometry.Space`
`.isAlgebraicSpace_of_isRepresentableByAlgebraicSpaces_surjective_etale`, then makes the target
an algebraic space. Nothing is assumed.

This is where the Deligne-Mumford hypothesis is used, and it is the whole of its use: the
corresponding implication of **Stacks 04SZ** has only a surjective *smooth* presentation
available, and the bootstrap theorem for such a presentation is **Stacks 04S6**, which the
library carries as the hypothesis
`AlgebraicGeometry.Space.IsBootstrapAlgebraicSpaceAlongFlatSurjection` of
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_of_isStackInSetoids`. The étale
bootstrap is unconditional, so no hypothesis is carried here.

## References

* [Stacks Project, Tag 02ZX](https://stacks.math.columbia.edu/tag/02ZX)
* [Stacks Project, Tag 0432](https://stacks.math.columbia.edu/tag/0432)
* [Stacks Project, Tag 03Y3](https://stacks.math.columbia.edu/tag/03Y3)
* [Stacks Project, Tag 03YS](https://stacks.math.columbia.edu/tag/03YS)
* [Stacks Project, Tag 045H](https://stacks.math.columbia.edu/tag/045H)
* [Stacks Project, Tag 04SY](https://stacks.math.columbia.edu/tag/04SY)
* [Stacks Project, Tag 04SZ](https://stacks.math.columbia.edu/tag/04SZ)
* [Stacks Project, Tag 04TC](https://stacks.math.columbia.edu/tag/04TC)
* [Stacks Project, Tag 04ZM](https://stacks.math.columbia.edu/tag/04ZM)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

add_to_stacks 045H "parts (1) and (2), the general inertia criterion"
  CategoryTheory.RelativeInertia.π_isEquivalence_iff
add_to_stacks 045H "inverse over the base in part (2)"
  CategoryTheory.RelativeInertia.π_comp_neutralSection_eq_id

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))

/-- **Stacks 045H, the implication (3) ⟹ (1).** A category fibred in groupoids over the big fppf
site of `S` which is representable by an algebraic space over `S` is a Deligne-Mumford stack and
a stack in setoids for the fppf topology.

The first conjunct is Stacks 03YS part (1) and the second is the implication (3) ⟹ (1) of Stacks
04SZ; neither uses algebraicity as a hypothesis, so none is assumed. -/
@[stacks 045H "the implication (3) ⟹ (1)"]
theorem isDeligneMumfordStack_and_isStackInSetoids_of_isRepresentableByAlgebraicSpace
    (h : IsRepresentableByAlgebraicSpace B S hS 𝒳) :
    IsDeligneMumfordStack.{u, w} B S hS 𝒳.val ∧
      𝒳.val.p.IsStackInSetoids (BigFppfOver.topology B S hS) :=
  ⟨isDeligneMumfordStack_of_isRepresentableByAlgebraicSpace.{u, w} B S hS 𝒳 h,
    isStackInSetoids_of_isRepresentableByAlgebraicSpace B S hS 𝒳 h⟩

/-- **Stacks 045H, the implication (3) ⟹ (2).** A category fibred in groupoids over the big fppf
site of `S` which is representable by an algebraic space over `S` is a Deligne-Mumford stack
whose canonical projection from the inertia category is an equivalence.

This is the implication (3) ⟹ (1) with its second conjunct passed through Stacks 04ZM, which is
the implication (3) ⟹ (2) of Stacks 04SZ. -/
@[stacks 045H "the implication (3) ⟹ (2)"]
theorem isDeligneMumfordStack_and_inertiaProjection_isEquivalence_of_isRepresentableByAlgebraicSpace
    (h : IsRepresentableByAlgebraicSpace B S hS 𝒳) :
    IsDeligneMumfordStack.{u, w} B S hS 𝒳.val ∧
      (RelativeInertia.π 𝒳.val.p :
        AbsoluteInertia 𝒳.val.p ⥤ 𝒳.val.obj).IsEquivalence :=
  ⟨isDeligneMumfordStack_of_isRepresentableByAlgebraicSpace.{u, w} B S hS 𝒳 h,
    isEquivalence_inertiaProjection_of_isRepresentableByAlgebraicSpace B S hS 𝒳 h⟩

/-- **Stacks 045H, the equivalence of parts (1) and (2).** A Deligne-Mumford stack over the big
fppf site of `S` is a stack in setoids if and only if the canonical projection from its inertia
category is an equivalence.

The Deligne-Mumford condition contains the algebraic-stack condition, which supplies the stack
hypothesis of Stacks 04ZM through
`AlgebraicGeometry.Stack.isStackInSetoids_iff_inertiaProjection_isEquivalence_of_isAlgebraicStack`;
the Deligne-Mumford conjunct is then common to both sides. -/
@[stacks 045H "the equivalence of parts (1) and (2)"]
theorem isStackInSetoids_iff_inertiaProjection_isEquivalence_of_isDeligneMumfordStack
    (h𝒳 : IsDeligneMumfordStack.{u, w} B S hS 𝒳.val) :
    𝒳.val.p.IsStackInSetoids (BigFppfOver.topology B S hS) ↔
      (RelativeInertia.π 𝒳.val.p :
        AbsoluteInertia 𝒳.val.p ⥤ 𝒳.val.obj).IsEquivalence :=
  isStackInSetoids_iff_inertiaProjection_isEquivalence_of_isAlgebraicStack.{u, w} B S hS 𝒳 h𝒳.1

section EtalePresentation

variable {𝒰 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}

/-- **A stack in setoids with an étale presentation is representable by an algebraic space.**

Let `f : 𝒰 ⟶ 𝒴` be a 1-morphism of categories fibred in groupoids over the big fppf site of `S`
with `𝒴` a stack in setoids with essentially small fibres, with `𝒰` representable by an algebraic
space, and with `f` representable by algebraic spaces, surjective and étale. Then `𝒴` is
representable by an algebraic space.

A stack in setoids is the category of elements of the `Type u` model of its presheaf of
isomorphism classes, which is a sheaf by Stacks 0432, and Stacks 04SY and Stacks 04TC turn `f`
into a morphism of sheaves with the same three properties whose source is an algebraic space;
Stacks 03Y3 then makes the target an algebraic space. Algebraicity of `𝒴` is not used, only the
presentation data. -/
theorem isRepresentableByAlgebraicSpace_of_isStackInSetoids_of_etalePresentation (f : 𝒰 ⟶ 𝒴)
    (h𝒴 : 𝒴.val.p.IsStackInSetoids (BigFppfOver.topology B S hS))
    (hess : ∀ V : BigFppfOver B S hS, EssentiallySmall.{u} (𝒴.val.p.Fiber V))
    (h𝒰 : IsRepresentableByAlgebraicSpace B S hS 𝒰)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom)
    (hsurj : HasRelativeProperty.{u, u, u + 1, u + 1} B S hS
      (Space.surjectiveMorphismProperty B S hS) f hf)
    (hetale : HasRelativeProperty.{u, u, u + 1, u + 1} B S hS
      (Space.etaleMorphisms B S hS) f hf) :
    IsRepresentableByAlgebraicSpace B S hS 𝒴 := by
  obtain ⟨h𝒰set, h𝒰iso⟩ := (isRepresentableByAlgebraicSpace_iff B S hS 𝒰).1 h𝒰
  have h𝒴set : 𝒴.val.p.IsFiberedInSetoids := ⟨𝒴.isFiberedInGroupoids, h𝒴.fiber_isThin⟩
  have : 𝒴.val.p.IsFibered := 𝒴.isFiberedInGroupoids.isFibered
  have : 𝒰.val.p.IsFibered := 𝒰.isFiberedInGroupoids.isFibered
  have : CategoryTheory.FunctorToTypes.Small.{u} 𝒴.val.p.isoClassPresheaf :=
    small_isoClassPresheaf_of_isThin_fiber B S hS 𝒴.val.p h𝒴.fiber_isThin hess
  have : CategoryTheory.FunctorToTypes.Small.{u} 𝒰.val.p.isoClassPresheaf :=
    small_isoClassPresheaf_of_isAlgebraicSpaceIsoClassPresheaf B S hS _ h𝒰iso
  have h𝒰model : IsAlgebraicSpace B S hS
      (CategoryTheory.Functor.isoClassPresheafModel.{u} 𝒰.val.p) :=
    (isAlgebraicSpaceIsoClassPresheaf_iff_isAlgebraicSpace_isoClassPresheafModel B S hS _).1
      h𝒰iso
  let 𝒴s : CatFiberedInSetoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS) :=
    CatFiberedInSetoids.mk 𝒴.val h𝒴set
  let 𝒰s : CatFiberedInSetoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS) :=
    CatFiberedInSetoids.mk 𝒰.val h𝒰set
  let fs : 𝒰s ⟶ 𝒴s := Bicategory.InducedBicategory.mkHom f.hom
  let a := CategoryTheory.Functor.isoClassPresheafModelMap.{u} 𝒰s.val.p 𝒴s.val.p
    (CatFiberedInGroupoids.homFunctor_comp_p fs)
  have ha : IsoClassCompatible B S hS fs
      (CategoryTheory.Functor.isoClassPresheafModel.{u} 𝒰s.val.p)
      (CategoryTheory.Functor.isoClassPresheafModel.{u} 𝒴s.val.p)
      (CategoryTheory.Functor.isoClassPresheafModelEquiv.{u} 𝒰s.val.p)
      (CategoryTheory.Functor.isoClassPresheafModelEquiv.{u} 𝒴s.val.p) a := fun W z =>
    CategoryTheory.Functor.isoClassPresheafModelMap_app_isoClassMk.{u} 𝒰s.val.p 𝒴s.val.p _ z
  have hfrep : IsRepresentableByAlgebraicSpaces B S hS
      (CatFiberedInSetoids.inclusion.map fs).hom := hf
  refine (isRepresentableByAlgebraicSpace_iff_isAlgebraicSpace_isoClassPresheafModel B S hS
    𝒴).2 ⟨h𝒴set, ?_⟩
  exact Space.isAlgebraicSpace_of_isRepresentableByAlgebraicSpaces_surjective_etale
    (isSheaf_isoClassPresheafModel B S hS 𝒴.val.p h𝒴) h𝒰model a
    ((isoClassMap_isRepresentableByAlgebraicSpaces_iff_model.{u, u, u + 1} B S hS fs a ha).2 hfrep)
    ((isoClassMap_holdsOnEverySchemePoint_iff_model.{u, u, u + 1, u + 1} B S hS fs
      (Space.surjectiveMorphismProperty B S hS) a ha hfrep).2 hsurj)
    ((isoClassMap_holdsOnEverySchemePoint_iff_model.{u, u, u + 1, u + 1} B S hS fs
      (Space.etaleMorphisms B S hS) a ha hfrep).2 hetale)

end EtalePresentation

/-- **Stacks 045H, the implication (1) ⟹ (3).** A Deligne-Mumford stack over the big fppf site
of `S` which is a stack in setoids for the fppf topology is representable by an algebraic space
over `S`.

The surjective étale presentation by a scheme that the Deligne-Mumford condition provides is the
presentation the étale engine consumes, and the fibres of an algebraic stack are essentially
small. -/
@[stacks 045H "the implication (1) ⟹ (3)"]
theorem isRepresentableByAlgebraicSpace_of_isDeligneMumfordStack_isStackInSetoids
    (h𝒳 : IsDeligneMumfordStack.{u, w} B S hS 𝒳.val)
    (hset : 𝒳.val.p.IsStackInSetoids (BigFppfOver.topology B S hS)) :
    IsRepresentableByAlgebraicSpace B S hS 𝒳 := by
  have hess : ∀ V : BigFppfOver B S hS, EssentiallySmall.{u} (𝒳.val.p.Fiber V) :=
    essentiallySmall_fiber_algebraicStack B S hS ⟨𝒳, h𝒳.1⟩
  obtain ⟨_halg, _hgrp, U, g, hg, hgprop⟩ := h𝒳
  exact isRepresentableByAlgebraicSpace_of_isStackInSetoids_of_etalePresentation B S hS
    (𝒰 := schemeFibredCategory B S hS U) (Bicategory.InducedBicategory.mkHom g.hom) hset hess
    (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS U) hg
    (fun V y hy F hF h => (hgprop V y hy F hF h).1)
    (fun V y hy F hF h => (hgprop V y hy F hF h).2)

/-- **Stacks 045H.** For a category fibred in groupoids over the big fppf site of `S` the
following are equivalent: it is a Deligne-Mumford stack and a stack in setoids for the fppf
topology; it is a Deligne-Mumford stack whose canonical projection from the inertia is an
equivalence; it is representable by an algebraic space over `S`.

No algebraicity hypothesis is assumed: algebraicity is part of the Deligne-Mumford condition of
the first two parts, and the third implies it by Stacks 03YS part (1). -/
@[stacks 045H "the equivalence of all three parts"]
theorem isDeligneMumfordStack_isStackInSetoids_tfae :
    List.TFAE
      [IsDeligneMumfordStack.{u, w} B S hS 𝒳.val ∧
          𝒳.val.p.IsStackInSetoids (BigFppfOver.topology B S hS),
        IsDeligneMumfordStack.{u, w} B S hS 𝒳.val ∧
          (RelativeInertia.π 𝒳.val.p :
            AbsoluteInertia 𝒳.val.p ⥤ 𝒳.val.obj).IsEquivalence,
        IsRepresentableByAlgebraicSpace B S hS 𝒳] := by
  tfae_have 1 ↔ 2 := and_congr_right
    (isStackInSetoids_iff_inertiaProjection_isEquivalence_of_isDeligneMumfordStack.{u, w} B S hS 𝒳)
  tfae_have 1 → 3 := fun h =>
    isRepresentableByAlgebraicSpace_of_isDeligneMumfordStack_isStackInSetoids.{u, w}
      B S hS 𝒳 h.1 h.2
  tfae_have 3 → 1 :=
    isDeligneMumfordStack_and_isStackInSetoids_of_isRepresentableByAlgebraicSpace.{u, w} B S hS 𝒳
  tfae_finish

end AlgebraicGeometry.Stack

end
