module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.ResidualGerbe
public import StacksFrontier.AlgebraicGeometry.Stacks.ResidualGerbeEquivalentConditions
public import StacksFrontier.CategoryTheory.FiberedCategory.IsoOver

/-!
# Functoriality of residual gerbes (Stacks 0DTH)

**Stacks 0DTH.** Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S`, let `x` be a
point of `𝒳` and let `y` be its image in `𝒴`. If the residual gerbes `𝒵_x ⊂ 𝒳` and `𝒵_y ⊂ 𝒴`
of `x` and `y` exist, then `f` induces a commutative diagram
```
  𝒵_x ⟶ 𝒳
   ↓      ↓f
  𝒵_y ⟶ 𝒴
```
i.e. a 1-morphism `𝒵_x ⟶ 𝒵_y` whose composite with the inclusion of `𝒵_y` is the composite of
the inclusion of `𝒵_x` with `f`.

Residual gerbes are not constructed in this library. What it has is the *specification* they are
asserted to satisfy uniquely, `AlgebraicGeometry.Stack.IsResidualGerbeAt` (the final assertion of
**Stacks 06MT**): a property `P` of the objects of `𝒳`, closed under isomorphism, whose full
subcategory is a reduced, locally Noetherian algebraic stack with exactly one point, lying over
`x`. So "`𝒵_x ⊂ 𝒳` exists" is read here as "`P` satisfies that specification", and `𝒵_x` is the
algebraic stack `AlgebraicGeometry.Stack.fullSubcategoryAlgebraicStack 𝒳 P _` with its canonical
inclusion `AlgebraicGeometry.Stack.fullSubcategoryInclusion`.

In that reading the whole of the source's proof is concentrated in one statement: that `f` carries
the objects of `𝒵_x` into `𝒵_y`. The source gets it by choosing a surjective, flat, locally
finitely presented 1-morphism `Spec k ⟶ 𝒵_x`, factoring the composite `Spec k ⟶ 𝒴` through `𝒵_y`
by **Stacks 06MW**, and concluding from **Stacks 06MQ** that the resulting substack
`𝒵_x ×_𝒴 𝒵_y` of `𝒵_x` is all of `𝒵_x`. That argument is
`AlgebraicGeometry.Stack.map_mem_of_isResidualGerbeAt`, with the nonemptiness of
`𝒵_x ×_𝒴 𝒵_y` read off **Stacks 04XH** directly. Like Stacks 06MW it needs the inclusion
`𝒵_y ⟶ 𝒴` to be a monomorphism, hence representable by algebraic spaces, which the source takes
from Stacks 04Y5; the library has the implication (2) ⟹ (3) of Stacks 04Y5 from the bootstrap
theorem Stacks 04S6 part (3),
`AlgebraicGeometry.Space.isBootstrapAlgebraicSpaceAlongFlatSurjection`.
Everything downstream — the 1-morphism `𝒵_x ⟶ 𝒵_y`, the commutativity of
the square, and the fact that it is the *only* 1-morphism making the square commute — is proved
from the membership statement.

## Main definitions

* `AlgebraicGeometry.Stack.residualGerbeMap`: the 1-morphism `𝒵_x ⟶ 𝒵_y` induced by `f`, built
  as the lift of the underlying functor of `𝒵_x ⟶ 𝒳 ⟶ 𝒴` through the full subcategory `𝒵_y`.

## Main results

* `AlgebraicGeometry.Stack.residualGerbeMap_comp_inclusion`: the square commutes, on the nose.
* `AlgebraicGeometry.Stack.eq_residualGerbeMap`: it is the unique 1-morphism doing so, which is
  what makes it *induced*.
* `AlgebraicGeometry.Stack.map_mem_of_isResidualGerbeAt`: `f` carries the residual gerbe at `x`
  into the residual gerbe at `y`, the source's argument from Stacks 06MQ.
* `AlgebraicGeometry.Stack.residualGerbeMap_comp_inclusion_of_isResidualGerbeAt`: **Stacks
  0DTH**.

## Implementation notes

The construction `AlgebraicGeometry.Stack.residualGerbeMap` is stated for any pair of algebraic
substacks `P` of `𝒳` and `Q` of `𝒴`, with an argument `hmem : ∀ ξ, P ξ → Q (f ξ)` saying that `f`
carries the first into the second; at residual gerbes that argument is supplied by
`AlgebraicGeometry.Stack.map_mem_of_isResidualGerbeAt`.

Commutativity is an equality of 1-morphisms rather than a 2-isomorphism, and it holds by `rfl`.
That is not a tautology dressed up as a theorem: the residual gerbes are *strictly* full
subcategories here, the inclusions are the induced-category inclusions, and the lift of a functor
through a full subcategory composed with the inclusion is the functor itself, definitionally. The
same strictness is what makes the induced 1-morphism unique, via `eq_residualGerbeMap`: a functor
into a full subcategory is recovered from its composite with the inclusion.

The membership hypothesis is stated for objects of `𝒳` satisfying `P`, rather than for objects of
`𝒵_x`, because that is the form in which the source's argument delivers it and because the two
differ only by the membership proof that the inclusion forgets.

## References

* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
* [Stacks Project, Tag 04XH](https://stacks.math.columbia.edu/tag/04XH)
* [Stacks Project, Tag 04Y5](https://stacks.math.columbia.edu/tag/04Y5)
* [Stacks Project, Tag 06MQ](https://stacks.math.columbia.edu/tag/06MQ)
* [Stacks Project, Tag 06MT](https://stacks.math.columbia.edu/tag/06MT)
* [Stacks Project, Tag 06MW](https://stacks.math.columbia.edu/tag/06MW)
* [Stacks Project, Tag 0DTH](https://stacks.math.columbia.edu/tag/0DTH)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

-- A based functor is determined by its underlying functor:
-- `CategoryTheory.BasedCategory.BasedFunctor.ext'`, public in
-- `StacksFrontier.CategoryTheory.FiberedCategory.IsoOver`. A `private` re-declaration,
-- one of ten across the library, stood here.

/-- A functor into a strictly full subcategory is the lift of its composite with the inclusion.
Equivalently: the lift is the *unique* functor whose composite with the inclusion is the given
functor, so post-composition with the inclusion is injective. -/
private theorem eq_lift_of_comp_ι_eq.{v₁, v₂, w₁, w₂}
    {C : Type w₁} [Category.{v₁} C] {D : Type w₂} [Category.{v₂} D]
    (P : ObjectProperty D) (G : C ⥤ P.FullSubcategory) (F : C ⥤ D) (hF : ∀ X, P (F.obj X))
    (h : G ⋙ P.ι = F) : G = P.lift F hF := by
  subst h
  rfl

/-- **The 1-morphism induced by `f` on residual gerbes, Stacks 0DTH.** Let `f : 𝒳 ⟶ 𝒴` be a
1-morphism of algebraic stacks over `S`, let `P` cut out a substack `𝒵_x` of `𝒳` and let `Q` cut
out a substack `𝒵_y` of `𝒴`. If `f` carries every object of `𝒳` with the property `P` to an
object of `𝒴` with the property `Q`, then it induces a 1-morphism `𝒵_x ⟶ 𝒵_y`, namely the lift
through the full subcategory `𝒵_y` of the underlying functor of `𝒵_x ⟶ 𝒳 ⟶ 𝒴`.

In the application `P` and `Q` are the residual gerbes of `𝒳` at `x` and of `𝒴` at its image,
and `hmem` is `AlgebraicGeometry.Stack.map_mem_of_isResidualGerbeAt`. -/
@[stacks 0DTH "the 1-morphism induced between substacks whose objects f carries into one another"]
def residualGerbeMap
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    {P : ObjectProperty 𝒳.val.val.obj} {Q : ObjectProperty 𝒴.val.val.obj}
    (hP : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 P))
    (hQ : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒴 Q))
    (hmem : ∀ ξ : 𝒳.val.val.obj, P ξ → Q (f.hom.hom.toFunctor.obj ξ)) :
    fullSubcategoryAlgebraicStack 𝒳 P hP ⟶ fullSubcategoryAlgebraicStack 𝒴 Q hQ :=
  Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom
    { toFunctor :=
        Q.lift (fullSubcategoryInclusion 𝒳 P hP ≫ f).hom.hom.toFunctor
          fun ξ => hmem ξ.obj ξ.property
      w := (fullSubcategoryInclusion 𝒳 P hP ≫ f).hom.hom.w })

/-- **The commutative square of Stacks 0DTH.** The induced 1-morphism `𝒵_x ⟶ 𝒵_y` composed with
the inclusion of `𝒵_y` into `𝒴` is the inclusion of `𝒵_x` into `𝒳` composed with `f`. -/
@[stacks 0DTH "the commutativity of the square for that 1-morphism"]
theorem residualGerbeMap_comp_inclusion
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    {P : ObjectProperty 𝒳.val.val.obj} {Q : ObjectProperty 𝒴.val.val.obj}
    (hP : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 P))
    (hQ : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒴 Q))
    (hmem : ∀ ξ : 𝒳.val.val.obj, P ξ → Q (f.hom.hom.toFunctor.obj ξ)) :
    residualGerbeMap B S hS f hP hQ hmem ≫ fullSubcategoryInclusion 𝒴 Q hQ =
      fullSubcategoryInclusion 𝒳 P hP ≫ f :=
  rfl

/-- The 1-morphism `𝒵_x ⟶ 𝒵_y` making the square of Stacks 0DTH commute is unique: this is what
it means for it to be *induced* by `f`. -/
theorem eq_residualGerbeMap
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    {P : ObjectProperty 𝒳.val.val.obj} {Q : ObjectProperty 𝒴.val.val.obj}
    (hP : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 P))
    (hQ : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒴 Q))
    (hmem : ∀ ξ : 𝒳.val.val.obj, P ξ → Q (f.hom.hom.toFunctor.obj ξ))
    (g : fullSubcategoryAlgebraicStack 𝒳 P hP ⟶ fullSubcategoryAlgebraicStack 𝒴 Q hQ)
    (hg : g ≫ fullSubcategoryInclusion 𝒴 Q hQ = fullSubcategoryInclusion 𝒳 P hP ≫ f) :
    g = residualGerbeMap B S hS f hP hQ hmem := by
  refine Bicategory.InducedBicategory.hom_ext (Bicategory.InducedBicategory.hom_ext ?_)
  refine BasedCategory.BasedFunctor.ext' ?_
  exact eq_lift_of_comp_ι_eq Q g.hom.hom.toFunctor
    (fullSubcategoryInclusion 𝒳 P hP ≫ f).hom.hom.toFunctor _
    (congrArg (fun u => u.hom.hom.toFunctor) hg)

/-- **`f` carries the residual gerbe at `x` into the residual gerbe at `y`, the argument of
Stacks 0DTH.** Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S`, let `x` be a point
of `𝒳` with image `y` in `𝒴`, and let `P` and `Q` be residual gerbes of `𝒳` at `x` and of `𝒴` at
`y`. Then every object of `𝒳` satisfying `P` is sent by `f` to an object satisfying `Q`.

Both residual gerbes satisfy condition (2) of **Stacks 06MP**, and every point of either lies over
`x`, respectively `y`, so this is
`AlgebraicGeometry.Stack.map_mem_of_isReducedLocallyNoetherianUniquePointSubstack`: the projection
`𝒵_x ×_𝒴 𝒵_y ⟶ 𝒵_x` is a monomorphism with nonempty source, hence an equivalence by
**Stacks 06MQ**. The monomorphy uses representability by algebraic spaces of the inclusion
`𝒵_y ⟶ 𝒴`, the implication (2) ⟹ (3) of **Stacks 04Y5**, which the library has from the
bootstrap theorem Stacks 04S6 part (3). -/
theorem map_mem_of_isResidualGerbeAt
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (x : points B S hS 𝒳.val.val (Classical.choose 𝒳.property))
    (y : points B S hS 𝒴.val.val (Classical.choose 𝒴.property))
    (hxy : pointsMap B S hS 𝒳.val.val (Classical.choose 𝒳.property)
      (Classical.choose 𝒴.property) f.hom.hom x = y)
    {P : ObjectProperty 𝒳.val.val.obj} {Q : ObjectProperty 𝒴.val.val.obj}
    (hx : IsResidualGerbeAt B S hS 𝒳 x P) (hy : IsResidualGerbeAt B S hS 𝒴 y Q) :
    ∀ ξ : 𝒳.val.val.obj, P ξ → Q (f.hom.hom.toFunctor.obj ξ) :=
  map_mem_of_isReducedLocallyNoetherianUniquePointSubstack B S hS f
    (isReducedLocallyNoetherianUniquePointSubstack_of_isResidualGerbeAt B S hS hx)
    (isReducedLocallyNoetherianUniquePointSubstack_of_isResidualGerbeAt B S hS hy)
    fun hPalg hQalg zP zQ => by
      rw [AlgebraicStacks.pointsMap_comp, Function.comp_apply,
        pointsMap_eq_of_isResidualGerbeAt B S hS hx hPalg zP,
        pointsMap_eq_of_isResidualGerbeAt B S hS hy hQalg zQ]
      exact hxy

/-- **Stacks 0DTH.** Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S`, let `x` be a
point of `𝒳` and let `y` be its image under `f`. Assume the residual gerbes of `𝒳` at `x` and of
`𝒴` at `y` exist, cut out by the object properties `P` and `Q` respectively, in the sense of the
specification `AlgebraicGeometry.Stack.IsResidualGerbeAt` of Stacks 06MT. Then `f` induces a
commutative square: the 1-morphism `residualGerbeMap` from the residual gerbe at `x` to the
residual gerbe at `y`, composed with the inclusion of the latter, is the inclusion of the former
composed with `f`.

That `f` carries the residual gerbe at `x` into the one at `y` is
`AlgebraicGeometry.Stack.map_mem_of_isResidualGerbeAt`, the source's argument through Stacks 06MQ;
it uses the bootstrap theorem Stacks 04S6 part (3) for the representability by algebraic spaces
of the inclusion of the residual gerbe at `y` that the source takes from Stacks 04Y5. -/
@[stacks 0DTH]
theorem residualGerbeMap_comp_inclusion_of_isResidualGerbeAt
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (x : points B S hS 𝒳.val.val (Classical.choose 𝒳.property))
    (y : points B S hS 𝒴.val.val (Classical.choose 𝒴.property))
    (hxy : pointsMap B S hS 𝒳.val.val (Classical.choose 𝒳.property)
      (Classical.choose 𝒴.property) f.hom.hom x = y)
    (P : ObjectProperty 𝒳.val.val.obj) (Q : ObjectProperty 𝒴.val.val.obj)
    (hx : IsResidualGerbeAt B S hS 𝒳 x P) (hy : IsResidualGerbeAt B S hS 𝒴 y Q) :
    residualGerbeMap B S hS f hx.2.choose hy.2.choose
        (map_mem_of_isResidualGerbeAt B S hS f x y hxy hx hy) ≫
        fullSubcategoryInclusion 𝒴 Q hy.2.choose =
      fullSubcategoryInclusion 𝒳 P hx.2.choose ≫ f :=
  residualGerbeMap_comp_inclusion B S hS f hx.2.choose hy.2.choose _

end AlgebraicGeometry.Stack

end
