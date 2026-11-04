module

public import StacksFrontier.AlgebraicGeometry.Stacks.AutomorphismSpaceOverAlgebraicSpace
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.RelativeDiagonalFibre

/-!
# The Isom objects of Stacks 06PP are the sheaves of isomorphisms

Let `𝒳` be an algebraic stack over `S`, let `Z` be an algebraic space over `S` and let
`x₁, x₂ : Z ⟶ 𝒳` be two algebraic-space-valued points. `Stacks 06PP` names two objects, and
`StacksFrontier/AlgebraicGeometry/Stacks/AutomorphismSpaceOverAlgebraicSpace.lean` builds each of
them as a 2-fibre product over `Z`, namely as the fibre of a diagonal along a point:

```text
Isom_𝒳(x₁, x₂)        = Z ×_{(x₁, x₂),   𝒳 × 𝒳,   Δ}   𝒳
Isom^α_{𝒳/𝒴}(x₁, x₂)  = Z ×_{(x₁, x₂, α), 𝒳 ×_𝒴 𝒳, Δ_f} 𝒳
```

What the source *means* by each of them is a sheaf of isomorphisms: the sections of the first
over a point `z` of `Z` should be the isomorphisms `x₁(z) ≅ x₂(z)` of the fibre of `𝒳`, and the
sections of the second the isomorphisms whose image under `f` is the component `α_z`. This file
proves that they are, by identifying each 2-fibre product, as a category over `Z`, with the
category of elements of the corresponding presheaf of vertical morphisms on the category of
elements of `Z`:

* `CategoryTheory.TwoFibreProductOver.DiagonalFibre.vertHomPresheaf`, whose sections over a
  point `a` of `Z` are the vertical morphisms `x₁(a) ⟶ x₂(a)` of `𝒳` — every one of which is
  invertible, the fibres of `𝒳` being groupoids;
* `CategoryTheory.TwoFibreProductOver.RelativeDiagonalFibre.relVertHomPresheaf`, whose sections
  over `a` are the vertical morphisms `x₁(a) ⟶ x₂(a)` whose image under `f` is the comparison
  isomorphism carried by the twisted point at `a`, which is the component `α_a`.

This is the comparison the implementation notes of
`StacksFrontier/AlgebraicGeometry/Stacks/AutomorphismSpaceOverAlgebraicSpace.lean` record as
missing, taken by the route those notes prescribe.

## Main results

* `AlgebraicGeometry.Stack.nonempty_equivalenceOver_isomorphismSpaceOverSpaceProj`:
  **Stacks 06PP**, the absolute case — `Isom_𝒳(x₁, x₂)` is, over `Z`, the sheaf of isomorphisms
  from `x₁` to `x₂`.
* `AlgebraicGeometry.Stack.nonempty_equivalenceOver_relativeIsomorphismSpaceOverSpaceProj`:
  **Stacks 06PP** part (2) — `Isom^α_{𝒳/𝒴}(x₁, x₂)` is, over `Z`, the sheaf of isomorphisms
  from `x₁` to `x₂` lifting `α`.

## Implementation notes

Each proof is the general identification of the fibre of a diagonal with a presheaf of vertical
morphisms — `CategoryTheory.TwoFibreProductOver.DiagonalFibre.equivalenceOver` and its relative
counterpart `CategoryTheory.TwoFibreProductOver.RelativeDiagonalFibre.equivalenceOver`, the
latter being Stacks 04XT — read at these objects. Both are stated for an arbitrary category over
the base, so no hypothesis beyond the two stacks being fibred in groupoids is used, and in
particular neither algebraicity nor the representability of the diagonals enters: the comparison
is a statement about the shape of the 2-fibre product, not about its representability.

The friction the notes of `AutomorphismSpaceOverAlgebraicSpace.lean` anticipated is that the
category structure of a 2-fibre product of the 2-category of categories fibred in groupoids is
found through `CategoryTheory.BasedCategory.ofFunctor`, which is not reducible. It is resolved by
making that definition reducible for instance search in this file, as
`StacksFrontier/AlgebraicGeometry/Stacks/RelativeAutomorphismGroupOverSpace.lean` does; the
projections `AlgebraicGeometry.Stack.isomorphismSpaceOverSpaceProj` and
`AlgebraicGeometry.Stack.relativeIsomorphismSpaceOverSpaceProj` are then recognised as the first
projections the two general results speak about, and the two 1-morphisms over the site that the
source's data provide — the pair `(x₁, x₂)` and the twisted point `(x₁, x₂, α)` — supply the
hypotheses `hY` directly through their own `w` fields.

## What is not proved here

Two further comparisons of renderings of the same objects remain open.

* The presheaves `AlgebraicGeometry.Stack.isomSpaceOverSpace` and
  `AlgebraicGeometry.Stack.relativeIsomSpaceOverSpace` of
  `StacksFrontier/AlgebraicGeometry/Stacks/IsomSpaceOverAlgebraicSpace.lean` are built on the big
  fppf site of `S`, not on the category of elements of `Z`; their sections over a scheme `W` are
  the *pairs* of a point `z` of `Z` over `W` and an isomorphism over `z`. The total-presheaf
  construction that turns a presheaf on the category of elements of `Z` into a presheaf over `Z`
  on the site, together with the identification of the two categories of elements over the site,
  is `CategoryTheory.PresheafOfCategories.elementsTotalPresheaf` and
  `CategoryTheory.PresheafOfCategories.totalElementsEquivalenceOver`; applying it to the two
  presheaves of this file gives the sheaves of isomorphisms on the site together with their
  algebraicity over `Z`, in
  `StacksFrontier/AlgebraicGeometry/Stacks/IsomTotalPresheafAlgebraic.lean`. What is still not
  proved is that *those* presheaves are the hand-built ones: the sections of
  `isomSpaceOverSpace` are isomorphisms of the fibre categories of `𝒳` and the sections of the
  total presheaves are vertical morphisms of its total category, and the comparison of the two
  descriptions is not made.
* The iterated form of part (2),
  `AlgebraicGeometry.Stack.relativeIsomorphismIteratedSpace`, is a 2-fibre product of the
  twisted *diagonal* `Δ^α` along the map `H` on absolute isomorphism categories, which is not of
  the shape either general result above covers, so neither identifies it.

## References

* [Stacks Project, Tag 003V](https://stacks.math.columbia.edu/tag/003V)
* [Stacks Project, Tag 0040](https://stacks.math.columbia.edu/tag/0040)
* [Stacks Project, Tag 04XT](https://stacks.math.columbia.edu/tag/04XT)
* [Stacks Project, Tag 06PP](https://stacks.math.columbia.edu/tag/06PP)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable (Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hZ : IsAlgebraicSpace B S hS Z)
variable {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}

/-- **Stacks 06PP: `Isom_𝒳(x₁, x₂)` is the sheaf of isomorphisms from `x₁` to `x₂`.** The
2-fibre product `Z ×_{(x₁, x₂), 𝒳 × 𝒳, Δ} 𝒳` of
`AlgebraicGeometry.Stack.isomorphismSpaceOverSpace` is equivalent, as a category over `Z`, to
the category of elements of the presheaf on the category of elements of `Z` whose sections over a
point `a` are the vertical morphisms `x₁(a) ⟶ x₂(a)` of `𝒳`. Those are exactly the isomorphisms
`x₁(a) ≅ x₂(a)` of the fibre of `𝒳`, the fibres of an algebraic stack being groupoids
(Stacks 003V), so this is the statement that the 2-fibre product the last paragraph of
Stacks 06PP writes `Isom_𝒳(x₁, x₂)` is the *sheaf of isomorphisms from `x₁` to `x₂`*.

This is `CategoryTheory.TwoFibreProductOver.DiagonalFibre.equivalenceOver` read at the pair
`(x₁, x₂) = AlgebraicGeometry.Stack.isomorphismPairPoint`. -/
@[stacks 06PP "the sheaf of isomorphisms from x₁ to x₂: the 2-fibre product is that sheaf"]
theorem nonempty_equivalenceOver_isomorphismSpaceOverSpaceProj
    (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) :
    Nonempty (StacksRepresentableCFG.EquivalenceOver
      (isomorphismSpaceOverSpaceProj B S hS Z hZ x₁ x₂).toFunctor
      (PresheafOfCategories.discreteProjection
        (TwoFibreProductOver.DiagonalFibre.vertHomPresheaf 𝒳.val.isFiberedInGroupoids
          (isomorphismPairPoint B S hS Z hZ x₁ x₂).hom.w))) :=
  ⟨TwoFibreProductOver.DiagonalFibre.equivalenceOver _ _⟩

/-- **Stacks 06PP, part (2): `Isom^α_{𝒳/𝒴}(x₁, x₂)` is the sheaf of isomorphisms lifting `α`.**
The 2-fibre product `Z ×_{(x₁, x₂, α), 𝒳 ×_𝒴 𝒳, Δ_f} 𝒳` of
`AlgebraicGeometry.Stack.relativeIsomorphismSpaceOverSpace` is equivalent, as a category over
`Z`, to the category of elements of the presheaf on the category of elements of `Z` whose
sections over a point `a` are the vertical morphisms `x₁(a) ⟶ x₂(a)` of `𝒳` whose image under
`f` is the comparison isomorphism carried by the twisted point at `a`, that is the component
`α_a`. So the object part (2) defines is the *relative sheaf of isomorphisms from `x₁` to `x₂`*
that the source says it is.

This is `CategoryTheory.TwoFibreProductOver.RelativeDiagonalFibre.equivalenceOver` —
Stacks 04XT — read at the twisted point
`AlgebraicGeometry.Stack.relativeIsomorphismTwistedPoint`. -/
@[stacks 06PP "part (2): the 2-fibre product is the sheaf of isomorphisms lifting α"]
theorem nonempty_equivalenceOver_relativeIsomorphismSpaceOverSpaceProj (f : 𝒳 ⟶ 𝒴)
    (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) (α : x₁ ≫ f ⟶ x₂ ≫ f) :
    Nonempty (StacksRepresentableCFG.EquivalenceOver
      (relativeIsomorphismSpaceOverSpaceProj B S hS Z hZ f x₁ x₂ α).toFunctor
      (PresheafOfCategories.discreteProjection
        (TwoFibreProductOver.RelativeDiagonalFibre.relVertHomPresheaf
          𝒴.val.isFiberedInGroupoids 𝒳.val.isFiberedInGroupoids
          (relativeIsomorphismTwistedPoint B S hS Z hZ f x₁ x₂ α).w f.hom.hom.w))) :=
  ⟨TwoFibreProductOver.RelativeDiagonalFibre.equivalenceOver _ _ _ _⟩

end AlgebraicGeometry.Stack

end
