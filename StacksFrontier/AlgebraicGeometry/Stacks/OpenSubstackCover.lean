module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStackIsStack
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableStackInSetoids
public import StacksFrontier.AlgebraicGeometry.Stacks.StackInSetoidsRepresentableBySpace
public import StacksFrontier.AlgebraicGeometry.Stacks.Substack
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.FibreFunctor
public import StacksFrontier.CategoryTheory.Sites.Stack.MorSeparated

/-!
# An algebraic stack covered by open substacks which are algebraic spaces (Stacks 05WE)

Let `𝒳` be an algebraic stack over a scheme `S` contained in a big fppf site `B`, and let
`𝒳_i`, `i ∈ I`, be open substacks of `𝒳` which cover `𝒳` and are each representable by an
algebraic space. Stacks 05WE says that `𝒳` is then representable by an algebraic space.

The source proves this in two steps: `𝒳` is a stack in setoids, by Stacks 05W9 applied to
`⨿_{i ∈ I} 𝒳_i ⟶ 𝒳` and `id : 𝒳 ⟶ 𝒳`; and a stack in setoids is representable by an algebraic
space, by the implication (1) ⟹ (3) of Stacks 04SZ. This file proves the first step and applies
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_of_isStackInSetoids` for the second.

## Main definitions

* `AlgebraicGeometry.Stack.IsOpenSubstackCover`: a family of open substacks of `𝒳` covers `𝒳`,
  in the sense that every object of every fibre of `𝒳` restricts, over the members of some
  covering sieve of the fppf topology, into one of the substacks.

## Main results

* `CategoryTheory.Functor.Fiber.hom_eq_of_objectProperty_fiber_isThin`: two parallel morphisms
  of a fibre of `p` between objects lying in a full subcategory with thin fibres are equal. This
  is fullness of the induced functor on fibres,
  `CategoryTheory.Functor.Fiber.full_mapOfComp`, at the inclusion of a full subcategory.
* `AlgebraicGeometry.Stack.isStackInSetoids_of_isOpenSubstackCover`: an algebraic stack covered
  by open substacks which are representable by algebraic spaces is a stack in setoids. This is
  the first step of the proof of Stacks 05WE.
* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_of_isOpenSubstackCover`:
  **Stacks 05WE**.

## Implementation notes

**The two steps.** Being a stack in setoids
(`CategoryTheory.Functor.IsStackInSetoids`) is being a stack with groupoid fibres and *thin*
fibres; the first two conjuncts are part of `AlgebraicGeometry.Stack.IsAlgebraicStack`, so the
content of the first step is thinness of the fibres of `𝒳`, and that is what is proved here.
The second step, "a stack in setoids is representable by an algebraic space", is the implication
(1) ⟹ (3) of Stacks 04SZ,
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_of_isStackInSetoids`
(`StacksFrontier.AlgebraicGeometry.Stacks.StackInSetoidsRepresentableBySpace`).

**Why the substacks are not replaced by their coproduct.** The source applies Stacks 05W9,
`CategoryTheory.Functor.isStackInSetoids_of_isStackInSetoids_twoFibreProduct`, to the single
1-morphism `⨿_{i ∈ I} 𝒳_i ⟶ 𝒳`, which needs the coproduct of a family of algebraic stacks and
the identification of the 2-fibre product `(⨿_i 𝒳_i) ×_𝒳 𝒳` with `⨿_i 𝒳_i`; neither is in the
library. They are not needed. An open substack is by construction a *full* subcategory of `𝒳`
(`AlgebraicGeometry.Stack.OpenSubstack.property`, a `CategoryTheory.ObjectProperty`), so a
morphism of a fibre of `𝒳` between two objects lying in `𝒳_i` *is* a morphism of the
corresponding fibre of `𝒳_i` — the fibre-level fullness
`CategoryTheory.Functor.Fiber.full_mapOfComp` — so thinness of the fibres of `𝒳_i` bounds it
directly, which is `CategoryTheory.Functor.Fiber.hom_eq_of_objectProperty_fiber_isThin`. The
argument that
remains is the one Stacks 05W9 makes: the restriction of an endomorphism `γ` of an object of a
fibre of `𝒳` to each member of a covering sieve is the identity, and the presheaf `Mor(y, y)` is
a sheaf, so `γ` is the identity — `CategoryTheory.Functor.eq_of_pullbackFiberHom_locally_eq`.
Only one object's membership is needed that way, so no appeal to strict fullness of the
substacks is made.

**The covering condition.** `AlgebraicGeometry.Stack.IsOpenSubstackCover` is the fppf-local
membership condition, written exactly as the local essential surjectivity
`CategoryTheory.Functor.LocallyEssSurjOnFibers` that Stacks 05W9 consumes: over the members of a
covering sieve the chosen restriction of the object lies in one of the substacks, with the index
allowed to depend on the member. The source's condition `𝒳 = ⋃_{i ∈ I} 𝒳_i` is membership in
the union of Stacks 05UQ, which is not in the library — neither the union of a family of open
substacks nor the fact that it is one. Unfolding the definition of that union, the source's
condition says that `⨿_{i ∈ I} (𝒳_i ×_𝒳 T) ⟶ T` is surjective for every object over `T`; since
`𝒳_i ×_𝒳 T` is an open subscheme `T_i ⊆ T` and the restriction of the object to `T_i` lies in
`𝒳_i`, that condition implies this one, with the Zariski covering sieve generated by the `T_i`.
The implication needs Stacks 05UQ's analysis of the base change of an open substack, so it is
not available here and the hypothesis is stated in the local form, which is the weaker of the
two and hence gives the stronger statement.

Because the condition mentions the chosen restriction
`CategoryTheory.Functor.pullbackFiber`, one might ask whether it depends on that choice. It does
not: two chosen restrictions along the same morphism are isomorphic in the fibre, and
`AlgebraicGeometry.Stack.OpenSubstack.strictlyFull` makes the property of objects invariant
under isomorphism.

## References

* [Stacks Project, Tag 05WE](https://stacks.math.columbia.edu/tag/05WE)
* [Stacks Project, Tag 05W9](https://stacks.math.columbia.edu/tag/05W9)
* [Stacks Project, Tag 04SZ](https://stacks.math.columbia.edu/tag/04SZ)
* [Stacks Project, Tag 04YM](https://stacks.math.columbia.edu/tag/04YM)
* [Stacks Project, Tag 05UQ](https://stacks.math.columbia.edu/tag/05UQ)
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.Functor

universe v₁ v₂ u₁ u₂

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒳 : Type u₂} [Category.{v₂} 𝒳]

/-- Two parallel morphisms of the fibre of `p` over `V` between objects which lie in a full
subcategory with thin fibres are equal.

The full subcategory selected by a property `P` of the objects of `𝒳` has structure functor
`P.ι ⋙ p`, and the functor it induces on the fibre over `V` is full, by
`CategoryTheory.Functor.Fiber.full_mapOfComp` and `CategoryTheory.ObjectProperty.full_ι`. A
morphism of the fibre of `p` over `V` between two objects satisfying `P` is therefore the image
of a morphism of the fibre of `P.ι ⋙ p` over `V`, and thinness of the latter fibre bounds the
former. -/
theorem Fiber.hom_eq_of_objectProperty_fiber_isThin (p : 𝒳 ⥤ 𝒮) {P : ObjectProperty 𝒳}
    (hthin : ∀ V : 𝒮, Quiver.IsThin ((P.ι ⋙ p).Fiber V))
    {V : 𝒮} {z z' : p.Fiber V} (hz : P z.1) (hz' : P z'.1) (δ δ' : z ⟶ z') :
    δ = δ' := by
  have hrfl : P.ι ⋙ p = P.ι ⋙ p := rfl
  have hL := Fiber.full_mapOfComp (p := P.ι ⋙ p) (q := p) (F := P.ι) hrfl V
  let L := Fiber.mapOfComp (P.ι ⋙ p) p P.ι hrfl V
  let zP : (P.ι ⋙ p).Fiber V := ⟨⟨z.1, hz⟩, z.2⟩
  let z'P : (P.ι ⋙ p).Fiber V := ⟨⟨z'.1, hz'⟩, z'.2⟩
  obtain ⟨a, ha⟩ := hL.map_surjective (show L.obj zP ⟶ L.obj z'P from δ)
  obtain ⟨a', ha'⟩ := hL.map_surjective (show L.obj zP ⟶ L.obj z'P from δ')
  obtain rfl : a = a' := (hthin V zP z'P).elim a a'
  exact ha.symm.trans ha'

end CategoryTheory.Functor

namespace AlgebraicGeometry.Stack

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A family of open substacks of an algebraic stack `𝒳` *covers* `𝒳` when every object of every
fibre of `𝒳` restricts, over the members of some covering sieve of the fppf topology, into one of
the substacks, the substack being allowed to depend on the member.

This is the rendering of the hypothesis `𝒳 = ⋃_{i ∈ I} 𝒳_i` of Stacks 05WE that the proof of
that lemma uses, written as the local essential surjectivity
`CategoryTheory.Functor.LocallyEssSurjOnFibers` of Stacks 05W9 is written. See the implementation
notes of this module for its relation to the union of Stacks 05UQ, and for why it does not depend
on the choice of restrictions. -/
def IsOpenSubstackCover (𝒳 : AlgebraicStacks.{u, w} B S hS) {I : Type*}
    (𝒰 : I → OpenSubstack 𝒳) : Prop :=
  haveI : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
  ∀ (T : BigFppfOver B S hS) (x : 𝒳.val.val.p.Fiber T),
    ∃ R ∈ BigFppfOver.topology B S hS T, ∀ ⦃V : BigFppfOver B S hS⦄ (f : V ⟶ T), R f →
      ∃ i, (𝒰 i).property (Functor.pullbackFiber 𝒳.val.val.p x f).1

/-- The fibres of an open substack of `𝒳` which is representable by an algebraic space are thin.

This is the implication (3) ⟹ (1) of Stacks 04SZ,
`AlgebraicGeometry.Stack.isStackInSetoids_of_isRepresentableByAlgebraicSpace`, followed by the
`fiber_isThin` field of `CategoryTheory.Functor.IsStackInSetoids`, read through the definitional
equality of the structure functor of the full subcategory with `P.ι ⋙ 𝒳.val.val.p`. -/
theorem fiber_isThin_of_isRepresentableByAlgebraicSpace_openSubstack
    {𝒳 : AlgebraicStacks.{u, w} B S hS} (𝒰 : OpenSubstack 𝒳)
    (h : IsRepresentableByAlgebraicSpace B S hS
      (fullSubcategoryAlgebraicStack 𝒳 𝒰.property 𝒰.isAlgebraic).val)
    (V : BigFppfOver B S hS) :
    Quiver.IsThin ((𝒰.property.ι ⋙ 𝒳.val.val.p).Fiber V) :=
  (isStackInSetoids_of_isRepresentableByAlgebraicSpace B S hS
    (fullSubcategoryAlgebraicStack 𝒳 𝒰.property 𝒰.isAlgebraic).val h).fiber_isThin V

/-- **The first step of the proof of Stacks 05WE.** Every endomorphism of an object of a fibre of
an algebraic stack covered by open substacks which are representable by algebraic spaces is the
identity.

Over each member `f : V ⟶ T` of the covering sieve supplied by the covering hypothesis, the
chosen restriction `f^* y` lies in one of the substacks, so the endomorphism `f^* γ` of it is an
endomorphism of the fibre of that substack over `V`; those fibres are thin, so `f^* γ` is the
identity. The presheaf `Mor(y, y)` of `𝒳` is a sheaf, `𝒳` being a stack, so `γ` is the
identity. -/
theorem eq_id_of_isOpenSubstackCover (𝒳 : AlgebraicStacks.{u, w} B S hS) {I : Type*}
    (𝒰 : I → OpenSubstack 𝒳) (hcover : IsOpenSubstackCover 𝒳 𝒰)
    (hspace : ∀ i, IsRepresentableByAlgebraicSpace B S hS
      (fullSubcategoryAlgebraicStack 𝒳 (𝒰 i).property (𝒰 i).isAlgebraic).val)
    {T : BigFppfOver B S hS}
    (y : haveI : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
      𝒳.val.val.p.Fiber T) (γ : y ⟶ y) :
    γ = 𝟙 y := by
  have : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
  obtain ⟨R, hR, hRmem⟩ := hcover T y
  refine Functor.eq_of_pullbackFiberHom_locally_eq 𝒳.val.val.p
    ((isStack_of_isAlgebraicStack B S hS 𝒳.property).isMorSheaf T y y) hR fun V f hf ↦ ?_
  rw [Functor.pullbackFiberHom_id]
  obtain ⟨i, hi⟩ := hRmem f hf
  exact Functor.Fiber.hom_eq_of_objectProperty_fiber_isThin 𝒳.val.val.p
    (fiber_isThin_of_isRepresentableByAlgebraicSpace_openSubstack (𝒰 i) (hspace i)) hi hi _ _

/-- **The first step of the proof of Stacks 05WE.** An algebraic stack covered by open substacks
which are representable by algebraic spaces is a stack in setoids for the fppf topology.

Being a stack and having groupoid fibres are part of the algebraic-stack condition, so the
content is thinness of the fibres, and that is
`AlgebraicGeometry.Stack.eq_id_of_isOpenSubstackCover` applied to `β ∘ α⁻¹`, the fibres being
groupoids — exactly as in
`CategoryTheory.Functor.isStackInSetoids_of_isStackInSetoids_twoFibreProduct`, Stacks 05W9. -/
theorem isStackInSetoids_of_isOpenSubstackCover (𝒳 : AlgebraicStacks.{u, w} B S hS) {I : Type*}
    (𝒰 : I → OpenSubstack 𝒳) (hcover : IsOpenSubstackCover 𝒳 𝒰)
    (hspace : ∀ i, IsRepresentableByAlgebraicSpace B S hS
      (fullSubcategoryAlgebraicStack 𝒳 (𝒰 i).property (𝒰 i).isAlgebraic).val) :
    𝒳.val.val.p.IsStackInSetoids (BigFppfOver.topology B S hS) where
  isStack := isStack_of_isAlgebraicStack B S hS 𝒳.property
  fiber_isGroupoid := 𝒳.val.isFiberedInGroupoids.fiber_isGroupoid
  fiber_isThin T y y' := by
    refine ⟨fun α β ↦ ?_⟩
    have : IsGroupoid (𝒳.val.val.p.Fiber T) := 𝒳.val.isFiberedInGroupoids.fiber_isGroupoid T
    have : IsIso α := IsGroupoid.all_isIso α
    exact ((comp_inv_eq_id α).mp
      (eq_id_of_isOpenSubstackCover 𝒳 𝒰 hcover hspace y (β ≫ CategoryTheory.inv α))).symm

/-- **Stacks 05WE.** Let `𝒳` be an algebraic stack over `S` and let `𝒰 i`, `i ∈ I`, be open
substacks of `𝒳` which cover `𝒳` and are each representable by an algebraic space over `S`. Then
`𝒳` is representable by an algebraic space.

The covering hypothesis makes `𝒳` a stack in setoids,
`AlgebraicGeometry.Stack.isStackInSetoids_of_isOpenSubstackCover`, which is the first step of the
source's proof; the second step is the implication (1) ⟹ (3) of Stacks 04SZ,
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_of_isStackInSetoids`. -/
@[stacks 05WE]
theorem isRepresentableByAlgebraicSpace_of_isOpenSubstackCover
    (𝒳 : AlgebraicStacks.{u, w} B S hS) {I : Type*} (𝒰 : I → OpenSubstack 𝒳)
    (hcover : IsOpenSubstackCover 𝒳 𝒰)
    (hspace : ∀ i, IsRepresentableByAlgebraicSpace B S hS
      (fullSubcategoryAlgebraicStack 𝒳 (𝒰 i).property (𝒰 i).isAlgebraic).val) :
    IsRepresentableByAlgebraicSpace B S hS 𝒳.val :=
  isRepresentableByAlgebraicSpace_of_isStackInSetoids B S hS 𝒳.val 𝒳.property
    (isStackInSetoids_of_isOpenSubstackCover 𝒳 𝒰 hcover hspace)

end AlgebraicGeometry.Stack

end
