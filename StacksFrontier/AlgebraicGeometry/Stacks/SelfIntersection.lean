module

public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableDiagonal
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverComposable

/-!
# The self-intersection of a point of an algebraic stack (Stacks 04T4)

Let `S` be a scheme contained in a big fppf site `B`, let `𝒳` be a category fibred in
groupoids over the big fppf site of `S`, let `𝒰` be another one and let `f : 𝒰 ⟶ 𝒳` be a
1-morphism. The *relation* of `f` is the 2-fibre product
`ℛ = 𝒰 ×_{f, 𝒳, f} 𝒰`; over a scheme `T` its objects are the triples `(a, b, α)` with
`a`, `b` objects of the fibre of `𝒰` over `T` and `α : f a ≅ f b` a morphism of the fibre of
`𝒳` over `T`.

This file carries parts (2) and (3) of Stacks 04T4:

* part (2), the canonical equivalence
  `𝒰 ×_𝒳 𝒰 ×_𝒳 𝒰 = ℛ ×_{pr₁, 𝒰, pr₀} ℛ`, which on fibres over `T` sends the object
  `((a, b, α), c, β)` of the left-hand side to the object `((a, b, α), (b, c, β))` of the
  right-hand side, together with the five identities describing it on objects;
* part (3), the outer projection
  `pr₀₂ : ℛ ×_{pr₁, 𝒰, pr₀} ℛ ⟶ ℛ`, which sends `((a, b, α), (b, c, β))` to
  `(a, c, β ∘ α)`, together with the three identities describing it on objects.

The two categories and their structure functors are 2-fibre products over the big fppf site
of `S`, so every comparison isomorphism occurring in them is vertical over the test scheme.

## Main definitions

* `AlgebraicGeometry.Stack.SelfIntersection.relation`: the 2-fibre product `ℛ`.
* `AlgebraicGeometry.Stack.SelfIntersection.triple`,
  `AlgebraicGeometry.Stack.SelfIntersection.tripleProjection`,
  `AlgebraicGeometry.Stack.SelfIntersection.composable`,
  `AlgebraicGeometry.Stack.SelfIntersection.composableProjection`: the three-fold product,
  the category of composable pairs, and their structure functors.

## Main results

* `AlgebraicGeometry.Stack.SelfIntersection.tripleEquivComposable`: **Stacks 04T4 (2)**, with
  `tripleEquivComposable_fst`, `tripleEquivComposable_last`,
  `tripleEquivComposable_middle`, `tripleEquivComposable_secondIso` and
  `tripleEquivComposable_middleIso`.
* `AlgebraicGeometry.Stack.SelfIntersection.composition`: **Stacks 04T4 (3)**, with
  `composition_fst`, `composition_snd` and `composition_iso`.
* `AlgebraicGeometry.Stack.SelfIntersection.hasRepresentableDiagonal_of_isAlgebraicStack`
  and `AlgebraicGeometry.Stack.SelfIntersection.isRepresentableByAlgebraicSpace_relation`:
  the two halves of the reduction of Stacks 04T4 (1) to the implication from condition (1)
  to condition (8) of Stacks 045G.

## Implementation notes

Both parts are pure 2-category theory: no hypothesis on `𝒳` beyond being fibred in
groupoids over the site is used, and in particular neither part needs `𝒳` to be an
algebraic stack. They are read off from the over-the-base comparison of a triple 2-fibre
product with a category of composable pairs,
`CategoryTheory.TwoFibreProductOver.composableEquivalenceOver`, and from the over-the-base
outer projection `CategoryTheory.TwoFibreProductOver.outerProjection`, instantiated at
`𝒜 = ℬ = ℰ = 𝒰` and `F = G = H = f`. The only input those need is that `f` is a 1-morphism
over the site, which is `CategoryTheory.BasedFunctor.w`.

Parts (1), (4), (5) and (6) of Stacks 04T4 are **not** in this file. Part (1), that `ℛ` is
representable by an algebraic space, is exactly the implication from condition (1) to
condition (8) of Stacks 045G (`AlgebraicGeometry.Stack.HasRepresentableDiagonal` to
`AlgebraicGeometry.Stack.HasAlgebraicSpaceProducts`), applied to `𝒰` twice; it is
`isRepresentableByAlgebraicSpace_relation_of_isAlgebraicStack`, in the same namespace.
Parts (4) to (6) build the groupoid in algebraic spaces on the representing spaces of `𝒰` and
`ℛ` and the canonical 1-morphism out of its quotient stack; they rest on part (1), since the
representing spaces are what they are about.

## References

* [Stacks Project, Tag 04T4](https://stacks.math.columbia.edu/tag/04T4)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.SelfIntersection

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable (𝒰 𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
variable (f : 𝒰.val ⥤ᵇ 𝒳.val)

/-- The self-intersection `ℛ = 𝒰 ×_{f, 𝒳, f} 𝒰` of a 1-morphism into a category fibred in
groupoids, as a category fibred in groupoids over the big fppf site of `S`. -/
abbrev relation : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS) :=
  Stack.twoFibreProduct B S hS 𝒳 𝒰 𝒰 f f

/-- The three-fold 2-fibre product `𝒰 ×_𝒳 𝒰 ×_𝒳 𝒰` over the big fppf site of `S`,
bracketed at the left. -/
abbrev triple :=
  TwoFibreProductOver (relation B S hS 𝒰 𝒳 f).val.p 𝒰.val.p 𝒳.val.p
    (TwoFibreProductOver.snd 𝒰.val.p 𝒰.val.p 𝒳.val.p f.toFunctor f.toFunctor ⋙ f.toFunctor)
    f.toFunctor

/-- The structure functor of the three-fold product to the big fppf site of `S`. -/
abbrev tripleProjection :=
  TwoFibreProductOver.structureFunctor (relation B S hS 𝒰 𝒳 f).val.p 𝒰.val.p 𝒳.val.p
    (TwoFibreProductOver.snd 𝒰.val.p 𝒰.val.p 𝒳.val.p f.toFunctor f.toFunctor ⋙ f.toFunctor)
    f.toFunctor

/-- The category `ℛ ×_{pr₁, 𝒰, pr₀} ℛ` of pairs of arrows of the relation composable over
the big fppf site of `S`. -/
abbrev composable :=
  TwoFibreProductOver (relation B S hS 𝒰 𝒳 f).val.p (relation B S hS 𝒰 𝒳 f).val.p 𝒰.val.p
    (TwoFibreProductOver.snd 𝒰.val.p 𝒰.val.p 𝒳.val.p f.toFunctor f.toFunctor)
    (TwoFibreProductOver.fst 𝒰.val.p 𝒰.val.p 𝒳.val.p f.toFunctor f.toFunctor)

/-- The structure functor of the category of composable pairs to the big fppf site of `S`. -/
abbrev composableProjection :=
  TwoFibreProductOver.structureFunctor (relation B S hS 𝒰 𝒳 f).val.p
    (relation B S hS 𝒰 𝒳 f).val.p 𝒰.val.p
    (TwoFibreProductOver.snd 𝒰.val.p 𝒰.val.p 𝒳.val.p f.toFunctor f.toFunctor)
    (TwoFibreProductOver.fst 𝒰.val.p 𝒰.val.p 𝒳.val.p f.toFunctor f.toFunctor)

/-- Condition (1) of Stacks 045G holds for an algebraic stack: it is one of the defining
clauses of `AlgebraicGeometry.Stack.IsAlgebraicStack`, written with
`AlgebraicGeometry.Stack.diagonalBasedFunctor` rather than with the product category of
`AlgebraicGeometry.Stack.HasRepresentableDiagonal`, and the two agree
(`AlgebraicGeometry.Stack.hasRepresentableDiagonal_iff`). -/
theorem hasRepresentableDiagonal_of_isAlgebraicStack
    (h𝒳 : Stack.IsAlgebraicStack.{u, w} B S hS 𝒳.val) :
    Stack.HasRepresentableDiagonal B S hS 𝒳 := by
  obtain ⟨_, -, hd, -⟩ := h𝒳
  exact hd

/-- **Stacks 04T4 (1), reduced to condition (8) of Stacks 045G and to nothing else.**
Granting that condition for `𝒳`, the self-intersection of a 1-morphism `f : 𝒰 ⟶ 𝒳` whose
source is representable by an algebraic space is itself representable by an algebraic space:
it is the condition instantiated at `𝒯₁ = 𝒯₂ = 𝒰` and `x = y = f`.

Together with `hasRepresentableDiagonal_of_isAlgebraicStack` and the implication from
condition (1) to condition (8) of Stacks 045G,
`AlgebraicGeometry.Stack.hasAlgebraicSpaceProducts_of_hasRepresentableDiagonal`, this gives
Stacks 04T4 (1) for an algebraic stack `𝒳`. -/
theorem isRepresentableByAlgebraicSpace_relation
    (h₈ : Stack.HasAlgebraicSpaceProducts.{u, u, u + 1, u, u, u, u} B S hS 𝒳)
    (h𝒰 : Stack.IsRepresentableByAlgebraicSpace B S hS 𝒰) :
    Stack.IsRepresentableByAlgebraicSpace B S hS (relation B S hS 𝒰 𝒳 f) :=
  h₈ 𝒰 𝒰 h𝒰 h𝒰 f f

/-- The category structure of the three-fold product. Instance synthesis cannot find it on
its own: matching the legs of the product forces `(relation B S hS 𝒰 𝒳 f).val.obj` against
`CategoryTheory.TwoFibreProductOver 𝒰.val.p 𝒰.val.p 𝒳.val.p f.toFunctor f.toFunctor`, which
is an unfolding of `AlgebraicGeometry.Stack.twoFibreProduct` and so is invisible at the
reducible transparency instance search uses. -/
local instance : Category.{u, u + 1} (triple B S hS 𝒰 𝒳 f) :=
  TwoFibreProductOver.instCategory

/-- The category structure of the category of composable pairs; see the note on the previous
instance. -/
local instance : Category.{u, u + 1} (composable B S hS 𝒰 𝒳 f) :=
  TwoFibreProductOver.instCategory

/-- **Stacks 04T4 (2).** The canonical equivalence, in the 2-category of categories over the
big fppf site of `S`, between the three-fold 2-fibre product `𝒰 ×_𝒳 𝒰 ×_𝒳 𝒰` and the
category `ℛ ×_{pr₁, 𝒰, pr₀} ℛ` of composable pairs of arrows of the relation. On fibres over
a scheme `T` it sends `((a, b, α), c, β)` to `((a, b, α), (b, c, β))`. -/
@[stacks 04T4 "part (2): three-fold product as composable arrows"]
noncomputable def tripleEquivComposable :
    StacksRepresentableCFG.EquivalenceOver (tripleProjection B S hS 𝒰 𝒳 f)
      (composableProjection B S hS 𝒰 𝒳 f) :=
  TwoFibreProductOver.composableEquivalenceOver (p𝒜 := 𝒰.val.p) (pℬ := 𝒰.val.p)
    (pℰ := 𝒰.val.p) (p𝒮 := 𝒳.val.p) (F := f.toFunctor) (G := f.toFunctor)
    (H := f.toFunctor) f.w

/-- The comparison of Stacks 04T4 (2) leaves the first relation arrow unchanged. -/
@[stacks 04T4 "part (2): first arrow of the comparison"]
theorem tripleEquivComposable_fst (x : triple B S hS 𝒰 𝒳 f) :
    ((tripleEquivComposable B S hS 𝒰 𝒳 f).hom.functor.obj x).x = x.x := rfl

/-- The comparison of Stacks 04T4 (2) leaves the final object unchanged. -/
@[stacks 04T4 "part (2): last object of the comparison"]
theorem tripleEquivComposable_last (x : triple B S hS 𝒰 𝒳 f) :
    ((tripleEquivComposable B S hS 𝒰 𝒳 f).hom.functor.obj x).y.y = x.y := rfl

/-- Under the comparison of Stacks 04T4 (2) the second relation arrow starts at the first
arrow's endpoint. -/
@[stacks 04T4 "part (2): middle object of the comparison"]
theorem tripleEquivComposable_middle (x : triple B S hS 𝒰 𝒳 f) :
    ((tripleEquivComposable B S hS 𝒰 𝒳 f).hom.functor.obj x).y.x = x.x.y := rfl

/-- Under the comparison of Stacks 04T4 (2) the second relation arrow carries the original
second isomorphism. -/
@[stacks 04T4 "part (2): second isomorphism of the comparison"]
theorem tripleEquivComposable_secondIso (x : triple B S hS 𝒰 𝒳 f) :
    HEq ((tripleEquivComposable B S hS 𝒰 𝒳 f).hom.functor.obj x).y.iso x.iso := HEq.rfl

/-- Under the comparison of Stacks 04T4 (2) the identification of the two middle objects is
the identity. -/
@[stacks 04T4 "part (2): identity at the middle object"]
theorem tripleEquivComposable_middleIso (x : triple B S hS 𝒰 𝒳 f) :
    HEq ((tripleEquivComposable B S hS 𝒰 𝒳 f).hom.functor.obj x).iso
      (Iso.refl x.x.y) := HEq.rfl

/-- **Stacks 04T4 (3).** The outer projection `pr₀₂`, induced through the comparison of part
(2) by the projection of the three-fold product onto its outer two factors: a 1-morphism
from the category of composable pairs to the relation, sending `((a, b, α), (b, c, β))` to
`(a, c, β ∘ α)`. -/
@[stacks 04T4 "part (3): composition of the relation"]
noncomputable def composition :
    BasedCategory.ofFunctor (composableProjection B S hS 𝒰 𝒳 f) ⥤ᵇ
      (relation B S hS 𝒰 𝒳 f).val where
  toFunctor :=
    TwoFibreProductOver.outerProjection (p𝒜 := 𝒰.val.p) (pℬ := 𝒰.val.p) (pℰ := 𝒰.val.p)
      (p𝒮 := 𝒳.val.p) (F := f.toFunctor) (G := f.toFunctor) (H := f.toFunctor) f.w
  w :=
    TwoFibreProductOver.outerProjection_comp_structureFunctor (p𝒜 := 𝒰.val.p)
      (pℬ := 𝒰.val.p) (pℰ := 𝒰.val.p) (p𝒮 := 𝒳.val.p) (F := f.toFunctor)
      (G := f.toFunctor) (H := f.toFunctor) f.w

/-- The composite of Stacks 04T4 (3) begins at the first arrow's source. -/
@[stacks 04T4 "part (3): source of the composite"]
theorem composition_fst (x : composable B S hS 𝒰 𝒳 f) :
    ((composition B S hS 𝒰 𝒳 f).toFunctor.obj x).x = x.x.x := rfl

/-- The composite of Stacks 04T4 (3) ends at the second arrow's target. -/
@[stacks 04T4 "part (3): target of the composite"]
theorem composition_snd (x : composable B S hS 𝒰 𝒳 f) :
    ((composition B S hS 𝒰 𝒳 f).toFunctor.obj x).y = x.y.y := rfl

/-- On objects the outer arrow of Stacks 04T4 (3) carries the composite of the two
isomorphisms, including the identification of their middle objects. -/
@[stacks 04T4 "part (3): composition on fibre objects"]
theorem composition_iso (x : composable B S hS 𝒰 𝒳 f) :
    HEq ((composition B S hS 𝒰 𝒳 f).toFunctor.obj x).iso
      (x.x.iso ≪≫ f.toFunctor.mapIso x.iso ≪≫ x.y.iso) := HEq.rfl

end AlgebraicGeometry.Stack.SelfIntersection

end
