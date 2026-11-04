module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStack
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStackPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.BaseChangeRepresentableBySpace
public import StacksFrontier.AlgebraicGeometry.Stacks.InertiaAlgebraic
public import StacksFrontier.AlgebraicGeometry.Stacks.InertiaProjectionRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeInertiaProjectionRepresentable
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.LocallyGroupoid
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CatFiberedInGroupoids
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverBase

/-!
# The Isom algebraic spaces of Stacks 06PP

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S` and let `Z` be an algebraic space
over `S`. **Stacks 06PP** attaches three objects to algebraic-space-valued points of `𝒳`, and
asserts of each that it is an algebraic space over `Z`:

```text
(1)  Isom_{𝒳/𝒴}(x, x)      = Z ×_{x, 𝒳} ℐ_{𝒳/𝒴}                       for x : Z ⟶ 𝒳
(2)  Isom^α_{𝒳/𝒴}(x₁, x₂)  = Z ×_{(x₁, x₂, α), 𝒳 ×_𝒴 𝒳, Δ_f} 𝒳         for α : x₁ ≫ f ⟶ x₂ ≫ f
     Isom_𝒳(x₁, x₂)        = Z ×_{(x₁, x₂), 𝒳 × 𝒳, Δ} 𝒳                when 𝒴 is a space
```

This file builds the three 2-fibre products, in the 2-category of categories fibred in groupoids
over the big fppf site of `S` where the inertia and the diagonals live, each with its projection
to the stack of `Z`, and proves for each that it *is* an algebraic space over `Z`: the object is
represented by an algebraic space over `S`, and its projection to `Z` is representable by
algebraic spaces, so the two together are a morphism of algebraic spaces with target `Z`.

Every proof is the same two steps, and none of them needs anything the library does not already
have. One of the three cospan legs is representable by algebraic spaces:

* `ℐ_{𝒳/𝒴} ⟶ 𝒳` by Stacks 050Q
  (`Stack.isRepresentableByAlgebraicSpaces_relativeInertiaProjection_of_isAlgebraicStack`),
  and `ℐ_𝒳 ⟶ 𝒳` likewise
  (`Stack.isRepresentableByAlgebraicSpaces_inertiaProjection_of_isAlgebraicStack`);
* `Δ_f : 𝒳 ⟶ 𝒳 ×_𝒴 𝒳` by
  `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_relativeDiagonal`;
* `Δ : 𝒳 ⟶ 𝒳 × 𝒳` by the third clause of `AlgebraicGeometry.Stack.IsAlgebraicStack` itself.

And the other leg comes out of the stack of `Z`, which is represented by `Z`
(`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_fibredCategory`). So Stacks 0300
(`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_twoFibreProduct`) makes the 2-fibre
product an algebraic space and Stacks 0302
(`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_twoFibreProductFst`) makes its
projection to `Z` a morphism of algebraic spaces.

## Main definitions

* `AlgebraicGeometry.Stack.relativeAutomorphismSpaceOverSpace`: **Stacks 06PP** part (1),
  `Z ×_{x, 𝒳} ℐ_{𝒳/𝒴}`, and `AlgebraicGeometry.Stack.automorphismSpaceOverSpace`, the absolute
  case `Z ×_{x, 𝒳} ℐ_𝒳`.
* `AlgebraicGeometry.Stack.isomorphismSpaceOverSpace`: `Isom_𝒳(x₁, x₂)`, the fibre of the
  diagonal of `𝒳` over the pair `AlgebraicGeometry.Stack.isomorphismPairPoint`.
* `AlgebraicGeometry.Stack.relativeIsomorphismSpaceOverSpace`: **Stacks 06PP** part (2),
  `Isom^α_{𝒳/𝒴}(x₁, x₂)`, the fibre of the relative diagonal of `f` over the twisted point
  `AlgebraicGeometry.Stack.relativeIsomorphismTwistedPoint`.
* The projections to the stack of `Z`:
  `AlgebraicGeometry.Stack.relativeAutomorphismSpaceOverSpaceProj`,
  `AlgebraicGeometry.Stack.automorphismSpaceOverSpaceProj`,
  `AlgebraicGeometry.Stack.isomorphismSpaceOverSpaceProj`,
  `AlgebraicGeometry.Stack.relativeIsomorphismSpaceOverSpaceProj`.

## Main results

Each of the four objects is an algebraic space, and each projection to `Z` is representable by
algebraic spaces:
`isRepresentableByAlgebraicSpace_relativeAutomorphismSpaceOverSpace` and
`isRepresentableByAlgebraicSpaces_relativeAutomorphismSpaceOverSpaceProj`,
`isRepresentableByAlgebraicSpace_automorphismSpaceOverSpace` and
`isRepresentableByAlgebraicSpaces_automorphismSpaceOverSpaceProj`,
`isRepresentableByAlgebraicSpace_isomorphismSpaceOverSpace` and
`isRepresentableByAlgebraicSpaces_isomorphismSpaceOverSpaceProj`,
`isRepresentableByAlgebraicSpace_relativeIsomorphismSpaceOverSpace` and
`isRepresentableByAlgebraicSpaces_relativeIsomorphismSpaceOverSpaceProj`, all in the namespace
`AlgebraicGeometry.Stack`.

## Implementation notes

*What is not here, and where it is.* Two things.

The **group law** of part (1). Stacks 06PP endows `Isom_{𝒳/𝒴}(x, x)` with the structure of a
group algebraic space over `Z` *by pulling back the composition law of Stacks 050R*, and that
structure is not constructed in this file. It is constructed in
`StacksFrontier/AlgebraicGeometry/Stacks/RelativeAutomorphismSpaceGroupLaw.lean`, as an equivalence
over `Z` between `AlgebraicGeometry.Stack.relativeAutomorphismSpaceOverSpace` and the category
of elements of the presheaf of groups
`AlgebraicGeometry.Stack.relativeAutomorphismGroupPresheaf`, whose group law is identified there
with the composition law, the neutral element and the inverse of Stacks 050R read at the objects
of the relative inertia pulled back along `x`
(`AlgebraicGeometry.Stack.RelativeAutomorphismSpace.nonempty_isEquivalenceOver_comparison` and
`…inertiaObj_mul`, `…inertiaObj_one`, `…inertiaObj_inv`). What that route does *not* use, and
what the library still does not have, is the base-change compatibility of
`CategoryTheory.RelativeInertia.composition` along `x` in product form: an identification of
`Isom_{𝒳/𝒴}(x, x) ×_Z Isom_{𝒳/𝒴}(x, x)` with `Z ×_{x, 𝒳} (ℐ_{𝒳/𝒴} ×_𝒳 ℐ_{𝒳/𝒴})`. Over a
*scheme* `T` instead of an algebraic space `Z`, and absolutely, the group algebraic space is
constructed: `AlgebraicGeometry.Stack.automorphismGroupSpace` and
`AlgebraicGeometry.Stack.isomSpaceGrpObj` (Stacks 04YP), with
`AlgebraicGeometry.Space.GroupAlgebraicSpace` as the target notion.

The **comparison with the explicit presheaves** of
`StacksFrontier/AlgebraicGeometry/Stacks/IsomSpaceOverAlgebraicSpace.lean`. That file builds
`Isom_𝒳(x₁, x₂)` and `Isom^α_{𝒳/𝒴}(x₁, x₂)` as presheaves of sets on the big fppf site, by hand,
and this file builds them as 2-fibre products; the equivalence over the site between the two
renderings is not proved. What identifies the sections of the 2-fibre product with the
isomorphisms is `CategoryTheory.TwoFibreProductOver.DiagonalFibre.equivalenceOver`, which is
stated for an arbitrary category over the site and so applies here; stating it at these objects
needs the category instance of the 2-fibre product to be found through
`CategoryTheory.BasedCategory.ofFunctor`, which is not reducible — the same friction the
implementation notes of `StacksFrontier/AlgebraicGeometry/Stacks/DiagonalCriteria.lean` record.

*The two forms of `Isom` for distinct points.* Stacks 06PP writes part (2) as the iterated fibre
product `(Z ×_{x₁, 𝒳, x₂} Z) ×_{Z ×_{y₁, 𝒴, y₂} Z, Δ^α} Z`, and the absolute case as
`(Z ×_{x₁, 𝒳, x₂} Z) ×_{Z × Z, Δ_Z} Z`. Here each is the base change of the corresponding
diagonal along a point of the corresponding product, which is the form the representability of
the diagonals is stated in and the form Stacks 045G conditions (1) and (2) use. The iterated
form of part (2) is built, with its algebraicity over `Z`, in
`StacksFrontier/AlgebraicGeometry/Stacks/RelativeIsomSpaceIteratedForm.lean`
(`AlgebraicGeometry.Stack.relativeIsomorphismIteratedSpace`), and the iterated form of the
absolute case is `AlgebraicGeometry.Stack.absoluteIsomorphismCategory` cut down by
`AlgebraicGeometry.Stack.absoluteIsomorphismDiagonalSubcategory`. The comparison of the iterated
forms with the diagonal-fibre forms of this file is not proved anywhere.

*The universes.* Stacks 050Q and the representability of the relative diagonal are stated at
`CatFiberedInGroupoids.{u, max u v, u + 1, max (max (u + 1) w) v}`, which at `v := u` and
`w := u + 1` is `CatFiberedInGroupoids.{u, u, u + 1, u + 1}`, the 2-category underlying
`AlgebraicGeometry.Stack.AlgebraicStacks`; the universe arguments are passed explicitly at each
use, since `max` on the right of a universe metavariable is not solvable by unification. Stacks
0300 and Stacks 0302 place no relation on the universes of the three categories of a cospan.

*The inertia and the diagonals are the library's own*: `AlgebraicGeometry.Stack.relativeInertia`
and `AlgebraicGeometry.Stack.inertia` with `CategoryTheory.RelativeInertia.basedProjection`,
and `AlgebraicGeometry.Stack.diagonalBasedFunctor`,
`AlgebraicGeometry.Stack.relativeDiagonalBasedFunctor`. No local repackaging of any of them is
introduced.

## References

* [Stacks Project, Tag 0040](https://stacks.math.columbia.edu/tag/0040)
* [Stacks Project, Tag 0300](https://stacks.math.columbia.edu/tag/0300)
* [Stacks Project, Tag 0302](https://stacks.math.columbia.edu/tag/0302)
* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
* [Stacks Project, Tag 04YP](https://stacks.math.columbia.edu/tag/04YP)
* [Stacks Project, Tag 050Q](https://stacks.math.columbia.edu/tag/050Q)
* [Stacks Project, Tag 050R](https://stacks.math.columbia.edu/tag/050R)
* [Stacks Project, Tag 06PP](https://stacks.math.columbia.edu/tag/06PP)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable (Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hZ : IsAlgebraicSpace B S hS Z)
variable {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}

/-! ### The relative sheaf of automorphisms -/

/-- **Stacks 06PP, part (1): the relative sheaf of automorphisms of `x`.** For a 1-morphism
`f : 𝒳 ⟶ 𝒴` of algebraic stacks and an algebraic-space-valued point `x : Z ⟶ 𝒳`, the 2-fibre
product

```text
Isom_{𝒳/𝒴}(x, x) = Z ×_{x, 𝒳} ℐ_{𝒳/𝒴}
```

of `x` with the forgetful 1-morphism of the relative inertia, read in the 2-category of
categories fibred in groupoids over the big fppf site of `S`. Its objects over a scheme `W` are
the triples of a point `z` of `Z` over `W`, an object `(a, α)` of the relative inertia over `W` —
that is, an object `a` of `𝒳` over `W` together with an automorphism `α` of `a` killed by `f` —
and a vertical isomorphism `x(z) ≅ a`; so a section over `W` is an automorphism of `x(z)` killed
by `f`, which is what the source calls an automorphism of `x` over `W` relative to `𝒴`. -/
@[stacks 06PP "part (1): the relative sheaf of automorphisms, Z ×_{x, X} I_{X/Y}"]
noncomputable def relativeAutomorphismSpaceOverSpace (f : 𝒳 ⟶ 𝒴)
    (x : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) :
    CatFiberedInGroupoids (BigFppfOver B S hS) :=
  twoFibreProduct B S hS 𝒳.val (algebraicSpaceStack.{u, w} B S hS Z hZ).val
    (relativeInertia B S hS f.hom) x.hom.hom
    (RelativeInertia.basedProjection f.hom.hom)

/-- The projection `Isom_{𝒳/𝒴}(x, x) ⟶ Z` of the relative sheaf of automorphisms of `x` to the
stack of `Z`: it keeps the point of `Z` and forgets the automorphism. This is the structure
morphism that makes `Isom_{𝒳/𝒴}(x, x)` an object over `Z`. -/
noncomputable def relativeAutomorphismSpaceOverSpaceProj (f : 𝒳 ⟶ 𝒴)
    (x : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) :
    (relativeAutomorphismSpaceOverSpace B S hS Z hZ f x).val ⥤ᵇ
      (algebraicSpaceStack.{u, w} B S hS Z hZ).val.val :=
  twoFibreProductFst B S hS 𝒳.val (algebraicSpaceStack.{u, w} B S hS Z hZ).val
    (relativeInertia B S hS f.hom) x.hom.hom
    (RelativeInertia.basedProjection f.hom.hom)

/-- **Stacks 06PP, part (1): `Isom_{𝒳/𝒴}(x, x)` is an algebraic space.** The relative sheaf of
automorphisms of an algebraic-space-valued point `x : Z ⟶ 𝒳` of an algebraic stack is
represented by an algebraic space over `S`.

Stacks 050Q makes the forgetful 1-morphism `ℐ_{𝒳/𝒴} ⟶ 𝒳` of the relative inertia representable
by algebraic spaces — only the representability of the two diagonals, the second clause of
`AlgebraicGeometry.Stack.IsAlgebraicStack`, is used for that — and `Z` represents the stack of
`Z`, so Stacks 0300 applies to the cospan `(x, ℐ_{𝒳/𝒴} ⟶ 𝒳)`. -/
@[stacks 06PP "part (1): Isom_{X/Y}(x, x) is an algebraic space"]
theorem isRepresentableByAlgebraicSpace_relativeAutomorphismSpaceOverSpace (f : 𝒳 ⟶ 𝒴)
    (x : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) :
    IsRepresentableByAlgebraicSpace B S hS
      (relativeAutomorphismSpaceOverSpace B S hS Z hZ f x) :=
  isRepresentableByAlgebraicSpace_twoFibreProduct B S hS 𝒳.val
    (algebraicSpaceStack.{u, w} B S hS Z hZ).val (relativeInertia B S hS f.hom)
    x.hom.hom (RelativeInertia.basedProjection f.hom.hom)
    (isRepresentableByAlgebraicSpaces_relativeInertiaProjection_of_isAlgebraicStack.{u, u, u + 1, w}
      B S hS 𝒳.val 𝒴.val f.hom 𝒳.property 𝒴.property)
    (isRepresentableByAlgebraicSpace_fibredCategory B S hS Z hZ)

/-- **Stacks 06PP, part (1): `Isom_{𝒳/𝒴}(x, x)` is an algebraic space over `Z`.** The projection
of the relative sheaf of automorphisms of `x` to the stack of `Z` is representable by algebraic
spaces, so — together with
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_relativeAutomorphismSpaceOverSpace`, which
makes its source an algebraic space — it is a morphism of algebraic spaces with target `Z`.

This is Stacks 0302 for the base change of the representable 1-morphism `ℐ_{𝒳/𝒴} ⟶ 𝒳` of
Stacks 050Q along `x`. -/
@[stacks 06PP "part (1): Isom_{X/Y}(x, x) is an algebraic space over Z"]
theorem isRepresentableByAlgebraicSpaces_relativeAutomorphismSpaceOverSpaceProj (f : 𝒳 ⟶ 𝒴)
    (x : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) :
    IsRepresentableByAlgebraicSpaces B S hS
      (relativeAutomorphismSpaceOverSpaceProj B S hS Z hZ f x) :=
  isRepresentableByAlgebraicSpaces_twoFibreProductFst B S hS 𝒳.val
    (algebraicSpaceStack.{u, w} B S hS Z hZ).val (relativeInertia B S hS f.hom)
    x.hom.hom (RelativeInertia.basedProjection f.hom.hom)
    (isRepresentableByAlgebraicSpaces_relativeInertiaProjection_of_isAlgebraicStack.{u, u, u + 1, w}
      B S hS 𝒳.val 𝒴.val f.hom 𝒳.property 𝒴.property)

/-! ### The absolute sheaf of automorphisms -/

/-- **Stacks 06PP: the sheaf of automorphisms of `x`.** For an algebraic-space-valued point
`x : Z ⟶ 𝒳` of an algebraic stack, the 2-fibre product

```text
Isom_𝒳(x, x) = Z ×_{x, 𝒳} ℐ_𝒳
```

of `x` with the forgetful 1-morphism of the inertia. This is the object the last paragraph of
Stacks 06PP writes `Isom_𝒳(x, x)`: part (1) of that definition when `𝒴` is an algebraic space,
in which case the relative inertia of `𝒳` over `𝒴` is the absolute inertia of `𝒳`. -/
@[stacks 06PP "the sheaf of automorphisms of x, Z ×_{x, X} I_X"]
noncomputable def automorphismSpaceOverSpace
    (x : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) :
    CatFiberedInGroupoids (BigFppfOver B S hS) :=
  twoFibreProduct B S hS 𝒳.val (algebraicSpaceStack.{u, w} B S hS Z hZ).val
    (inertia B S hS 𝒳.val) x.hom.hom
    (RelativeInertia.basedProjection
      (𝒴 := BasedCategory.ofFunctor (𝟭 (BigFppfOver B S hS)))
      ⟨𝒳.val.val.p, Functor.comp_id 𝒳.val.val.p⟩)

/-- The projection `Isom_𝒳(x, x) ⟶ Z` of the sheaf of automorphisms of `x` to the stack of
`Z`. -/
noncomputable def automorphismSpaceOverSpaceProj
    (x : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) :
    (automorphismSpaceOverSpace B S hS Z hZ x).val ⥤ᵇ
      (algebraicSpaceStack.{u, w} B S hS Z hZ).val.val :=
  twoFibreProductFst B S hS 𝒳.val (algebraicSpaceStack.{u, w} B S hS Z hZ).val
    (inertia B S hS 𝒳.val) x.hom.hom
    (RelativeInertia.basedProjection
      (𝒴 := BasedCategory.ofFunctor (𝟭 (BigFppfOver B S hS)))
      ⟨𝒳.val.val.p, Functor.comp_id 𝒳.val.val.p⟩)

/-- **Stacks 06PP: `Isom_𝒳(x, x)` is an algebraic space.** The sheaf of automorphisms of an
algebraic-space-valued point of an algebraic stack is represented by an algebraic space over
`S`: Stacks 050Q for the absolute inertia projection, together with Stacks 0300. -/
@[stacks 06PP "Isom_X(x, x) is an algebraic space"]
theorem isRepresentableByAlgebraicSpace_automorphismSpaceOverSpace
    (x : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) :
    IsRepresentableByAlgebraicSpace B S hS (automorphismSpaceOverSpace B S hS Z hZ x) :=
  isRepresentableByAlgebraicSpace_twoFibreProduct B S hS 𝒳.val
    (algebraicSpaceStack.{u, w} B S hS Z hZ).val (inertia B S hS 𝒳.val) x.hom.hom _
    (isRepresentableByAlgebraicSpaces_inertiaProjection_of_isAlgebraicStack.{u, u, u + 1, w}
      B S hS 𝒳.val 𝒳.property)
    (isRepresentableByAlgebraicSpace_fibredCategory B S hS Z hZ)

/-- **Stacks 06PP: `Isom_𝒳(x, x)` is an algebraic space over `Z`.** The projection of the sheaf
of automorphisms of `x` to the stack of `Z` is representable by algebraic spaces — Stacks 0302 for
the base change of the representable 1-morphism `ℐ_𝒳 ⟶ 𝒳` of Stacks 050Q along `x`. -/
@[stacks 06PP "Isom_X(x, x) is an algebraic space over Z"]
theorem isRepresentableByAlgebraicSpaces_automorphismSpaceOverSpaceProj
    (x : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) :
    IsRepresentableByAlgebraicSpaces B S hS
      (automorphismSpaceOverSpaceProj B S hS Z hZ x) :=
  isRepresentableByAlgebraicSpaces_twoFibreProductFst B S hS 𝒳.val
    (algebraicSpaceStack.{u, w} B S hS Z hZ).val (inertia B S hS 𝒳.val) x.hom.hom _
    (isRepresentableByAlgebraicSpaces_inertiaProjection_of_isAlgebraicStack.{u, u, u + 1, w}
      B S hS 𝒳.val 𝒳.property)


/-! ### The sheaf of isomorphisms between two points -/

/-- The pair `(x₁, x₂) : Z ⟶ 𝒳 × 𝒳` of two algebraic-space-valued points of `𝒳`: the diagonal of
the stack of `Z` followed by the product of `x₁` and `x₂`. It is the 1-morphism the sheaf of
isomorphisms from `x₁` to `x₂` is the fibre of the diagonal of `𝒳` over. -/
noncomputable def isomorphismPairPoint (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) :
    (algebraicSpaceStack.{u, w} B S hS Z hZ).val ⟶
      CatFiberedInGroupoids.product 𝒳.val 𝒳.val :=
  diagonal.{u, u, u + 1} B S hS (algebraicSpaceStack.{u, w} B S hS Z hZ).val ≫
    CatFiberedInGroupoids.productMap x₁.hom x₂.hom

/-- **Stacks 06PP: the sheaf of isomorphisms from `x₁` to `x₂`.** For two
algebraic-space-valued points `x₁, x₂ : Z ⟶ 𝒳` of an algebraic stack, the 2-fibre product

```text
Isom_𝒳(x₁, x₂) = Z ×_{(x₁, x₂), 𝒳 × 𝒳, Δ} 𝒳
```

of the pair `(x₁, x₂)` with the diagonal of `𝒳`. Its objects over a scheme `W` are the
quadruples of a point `z` of `Z` over `W`, an object `a` of `𝒳` over `W` and two vertical
isomorphisms `x₁(z) ≅ a`, `x₂(z) ≅ a`, so a section over `W` is an isomorphism
`x₁(z) ≅ x₂(z)` of the fibre of `𝒳` over `W` — which is what the last paragraph of Stacks 06PP
calls the *sheaf of isomorphisms from `x₁` to `x₂`*.

This is the presentation of `Isom` that the diagonal conditions (1) and (2) of Stacks 045G are
stated with, and it is the one
`CategoryTheory.TwoFibreProductOver.DiagonalFibre.equivalenceOver` identifies with the presheaf
of vertical morphisms from `x₁` to `x₂`. The equivalent iterated form the source writes,
`(Z ×_{x₁, 𝒳, x₂} Z) ×_{Z × Z, Δ_Z} Z`, is `AlgebraicGeometry.Stack.absoluteIsomorphismCategory`
cut down by `AlgebraicGeometry.Stack.absoluteIsomorphismDiagonalSubcategory`; this file does not
prove the comparison of the two forms. -/
@[stacks 06PP "the sheaf of isomorphisms from x₁ to x₂, as the fibre of the diagonal"]
noncomputable def isomorphismSpaceOverSpace
    (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) :
    CatFiberedInGroupoids (BigFppfOver B S hS) :=
  twoFibreProduct B S hS (CatFiberedInGroupoids.product 𝒳.val 𝒳.val)
    (algebraicSpaceStack.{u, w} B S hS Z hZ).val 𝒳.val
    (isomorphismPairPoint B S hS Z hZ x₁ x₂).hom (diagonalBasedFunctor B S hS 𝒳.val)

/-- The projection `Isom_𝒳(x₁, x₂) ⟶ Z` of the sheaf of isomorphisms from `x₁` to `x₂` to the
stack of `Z`. -/
noncomputable def isomorphismSpaceOverSpaceProj
    (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) :
    (isomorphismSpaceOverSpace B S hS Z hZ x₁ x₂).val ⥤ᵇ
      (algebraicSpaceStack.{u, w} B S hS Z hZ).val.val :=
  twoFibreProductFst B S hS (CatFiberedInGroupoids.product 𝒳.val 𝒳.val)
    (algebraicSpaceStack.{u, w} B S hS Z hZ).val 𝒳.val
    (isomorphismPairPoint B S hS Z hZ x₁ x₂).hom (diagonalBasedFunctor B S hS 𝒳.val)

/-- **Stacks 06PP: `Isom_𝒳(x₁, x₂)` is an algebraic space.** The sheaf of isomorphisms from one
algebraic-space-valued point of an algebraic stack to another is represented by an algebraic
space over `S`.

It is the base change of the diagonal of `𝒳` along the pair `(x₁, x₂)`, the diagonal is
representable by algebraic spaces because `𝒳` is an algebraic stack, and `Z` represents the stack
of `Z`; so this is Stacks 0300. -/
@[stacks 06PP "Isom_X(x₁, x₂) is an algebraic space"]
theorem isRepresentableByAlgebraicSpace_isomorphismSpaceOverSpace
    (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) :
    IsRepresentableByAlgebraicSpace B S hS (isomorphismSpaceOverSpace B S hS Z hZ x₁ x₂) := by
  obtain ⟨hfib, hst, hΔ, hatl⟩ := id 𝒳.property
  exact isRepresentableByAlgebraicSpace_twoFibreProduct B S hS _ _ _ _ _ hΔ
    (isRepresentableByAlgebraicSpace_fibredCategory B S hS Z hZ)

/-- **Stacks 06PP: `Isom_𝒳(x₁, x₂)` is an algebraic space over `Z`.** Its projection to the stack
of `Z` is representable by algebraic spaces — Stacks 0302 for the base change of the diagonal of
`𝒳` along the pair `(x₁, x₂)`. -/
@[stacks 06PP "Isom_X(x₁, x₂) is an algebraic space over Z"]
theorem isRepresentableByAlgebraicSpaces_isomorphismSpaceOverSpaceProj
    (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) :
    IsRepresentableByAlgebraicSpaces B S hS
      (isomorphismSpaceOverSpaceProj B S hS Z hZ x₁ x₂) := by
  obtain ⟨hfib, hst, hΔ, hatl⟩ := id 𝒳.property
  exact isRepresentableByAlgebraicSpaces_twoFibreProductFst B S hS _ _ _ _ _ hΔ

/-! ### The relative sheaf of isomorphisms lifting a 2-morphism -/

/-- **The twisted point `(x₁, x₂, α) : Z ⟶ 𝒳 ×_𝒴 𝒳`** determined by two algebraic-space-valued
points `x₁, x₂ : Z ⟶ 𝒳` and a 2-morphism `α : x₁ ≫ f ⟶ x₂ ≫ f` of the target: it sends a point
`z` of `Z` to the triple of `x₁(z)`, `x₂(z)` and the component of `α` at `z`. The 2-morphism is
invertible because the 2-category of categories fibred in groupoids is locally groupoidal
(`CategoryTheory.CatFiberedInGroupoids.twoIso`) and its components are vertical, which is the
mediating-1-morphism datum Stacks 0040 asks for.

This is the 1-morphism the source calls `Δ^α` composed into the cospan: the source forms the
fibre product of `Z ×_{x₁, 𝒳, x₂} Z ⟶ Z ×_{y₁, 𝒴, y₂} Z` along
`Δ^α : Z ⟶ Z ×_{y₁, 𝒴, y₂} Z`, and this point is the resulting 1-morphism to `𝒳 ×_𝒴 𝒳`. -/
noncomputable def relativeIsomorphismTwistedPoint (f : 𝒳 ⟶ 𝒴)
    (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) (α : x₁ ≫ f ⟶ x₂ ≫ f) :
    (algebraicSpaceStack.{u, w} B S hS Z hZ).val.val ⥤ᵇ
      (twoFibreProduct B S hS 𝒴.val 𝒳.val 𝒳.val f.hom.hom f.hom.hom).val where
  toFunctor :=
    TwoFibreProductOver.lift 𝒳.val.val.p 𝒳.val.val.p 𝒴.val.val.p
      f.hom.hom.toFunctor f.hom.hom.toFunctor
      (algebraicSpaceStack.{u, w} B S hS Z hZ).val.val.p
      x₁.hom.hom.toFunctor x₂.hom.hom.toFunctor x₁.hom.hom.w x₂.hom.hom.w
      (CatFiberedInGroupoids.underlyingIso (CatFiberedInGroupoids.twoIso α.hom))
      (fun a => α.hom.hom.isHomLift' a)
  w := TwoFibreProductOver.lift_comp_structureFunctor ..

/-- **Stacks 06PP, part (2): the relative sheaf of isomorphisms from `x₁` to `x₂`.** For a
1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks, two algebraic-space-valued points
`x₁, x₂ : Z ⟶ 𝒳` and a 2-morphism `α : x₁ ≫ f ⟶ x₂ ≫ f`, the 2-fibre product

```text
Isom^α_{𝒳/𝒴}(x₁, x₂) = Z ×_{(x₁, x₂, α), 𝒳 ×_𝒴 𝒳, Δ_f} 𝒳
```

of the twisted point of `AlgebraicGeometry.Stack.relativeIsomorphismTwistedPoint` with the
relative diagonal of `f`. Its sections over a scheme `W` are the isomorphisms
`x₁(z) ≅ x₂(z)` of the fibre of `𝒳` over `W` whose image under `f` is the component of `α` at
`z`, which is what the source calls the *relative sheaf of isomorphisms from `x₁` to `x₂`*.

The source writes the same object as the iterated fibre product
`(Z ×_{x₁, 𝒳, x₂} Z) ×_{Z ×_{y₁, 𝒴, y₂} Z, Δ^α} Z`; that is the fibre of `Δ^α` and this is the
fibre of `Δ_f` along the twisted point, which is the form the representability of the relative
diagonal is stated for. This file does not prove the comparison of the two forms, nor the
comparison with the explicit sub-presheaf
`AlgebraicGeometry.Stack.relativeIsomSpaceOverSpace`. -/
@[stacks 06PP "part (2): the relative sheaf of isomorphisms, as the fibre of the relative diagonal"]
noncomputable def relativeIsomorphismSpaceOverSpace (f : 𝒳 ⟶ 𝒴)
    (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) (α : x₁ ≫ f ⟶ x₂ ≫ f) :
    CatFiberedInGroupoids (BigFppfOver B S hS) :=
  twoFibreProduct B S hS (twoFibreProduct B S hS 𝒴.val 𝒳.val 𝒳.val f.hom.hom f.hom.hom)
    (algebraicSpaceStack.{u, w} B S hS Z hZ).val 𝒳.val
    (relativeIsomorphismTwistedPoint B S hS Z hZ f x₁ x₂ α)
    (relativeDiagonalBasedFunctor B S hS 𝒳.val 𝒴.val f.hom.hom)

/-- The projection `Isom^α_{𝒳/𝒴}(x₁, x₂) ⟶ Z` of the relative sheaf of isomorphisms to the stack
of `Z`. -/
noncomputable def relativeIsomorphismSpaceOverSpaceProj (f : 𝒳 ⟶ 𝒴)
    (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) (α : x₁ ≫ f ⟶ x₂ ≫ f) :
    (relativeIsomorphismSpaceOverSpace B S hS Z hZ f x₁ x₂ α).val ⥤ᵇ
      (algebraicSpaceStack.{u, w} B S hS Z hZ).val.val :=
  twoFibreProductFst B S hS
    (twoFibreProduct B S hS 𝒴.val 𝒳.val 𝒳.val f.hom.hom f.hom.hom)
    (algebraicSpaceStack.{u, w} B S hS Z hZ).val 𝒳.val
    (relativeIsomorphismTwistedPoint B S hS Z hZ f x₁ x₂ α)
    (relativeDiagonalBasedFunctor B S hS 𝒳.val 𝒴.val f.hom.hom)

/-- The relative diagonal of a 1-morphism of algebraic stacks is representable by algebraic
spaces. -/
private theorem isRepresentableByAlgebraicSpaces_relativeDiagonal_of_algebraicStacks
    (f : 𝒳 ⟶ 𝒴) :
    IsRepresentableByAlgebraicSpaces B S hS
      (relativeDiagonalBasedFunctor B S hS 𝒳.val 𝒴.val f.hom.hom) := by
  obtain ⟨_, _, hΔ𝒳, _⟩ := id 𝒳.property
  obtain ⟨_, _, hΔ𝒴, _⟩ := id 𝒴.property
  exact isRepresentableByAlgebraicSpaces_relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val 𝒴.val f.hom
    hΔ𝒳 hΔ𝒴

/-- **Stacks 06PP, part (2): `Isom^α_{𝒳/𝒴}(x₁, x₂)` is an algebraic space.** The relative sheaf
of isomorphisms from `x₁` to `x₂` lifting `α` is represented by an algebraic space over `S`.

It is the base change of the relative diagonal `Δ_f : 𝒳 ⟶ 𝒳 ×_𝒴 𝒳` along the twisted point; the
relative diagonal is representable by algebraic spaces as soon as the diagonals of `𝒳` and `𝒴`
are (`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_relativeDiagonal`), which they are
because `𝒳` and `𝒴` are algebraic stacks, and `Z` represents the stack of `Z`; so this is
Stacks 0300. -/
@[stacks 06PP "part (2): Isom^α_{X/Y}(x₁, x₂) is an algebraic space"]
theorem isRepresentableByAlgebraicSpace_relativeIsomorphismSpaceOverSpace (f : 𝒳 ⟶ 𝒴)
    (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) (α : x₁ ≫ f ⟶ x₂ ≫ f) :
    IsRepresentableByAlgebraicSpace B S hS
      (relativeIsomorphismSpaceOverSpace B S hS Z hZ f x₁ x₂ α) := by
  exact isRepresentableByAlgebraicSpace_twoFibreProduct B S hS _ _ _ _ _
    (isRepresentableByAlgebraicSpaces_relativeDiagonal_of_algebraicStacks B S hS f)
    (isRepresentableByAlgebraicSpace_fibredCategory B S hS Z hZ)

/-- **Stacks 06PP, part (2): `Isom^α_{𝒳/𝒴}(x₁, x₂)` is an algebraic space over `Z`.** Its
projection to the stack of `Z` is representable by algebraic spaces — Stacks 0302 for the base
change of the relative diagonal of `f` along the twisted point. -/
@[stacks 06PP "part (2): Isom^α_{X/Y}(x₁, x₂) is an algebraic space over Z"]
theorem isRepresentableByAlgebraicSpaces_relativeIsomorphismSpaceOverSpaceProj (f : 𝒳 ⟶ 𝒴)
    (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) (α : x₁ ≫ f ⟶ x₂ ≫ f) :
    IsRepresentableByAlgebraicSpaces B S hS
      (relativeIsomorphismSpaceOverSpaceProj B S hS Z hZ f x₁ x₂ α) := by
  exact isRepresentableByAlgebraicSpaces_twoFibreProductFst B S hS _ _ _ _ _
    (isRepresentableByAlgebraicSpaces_relativeDiagonal_of_algebraicStacks B S hS f)

end AlgebraicGeometry.Stack

end
