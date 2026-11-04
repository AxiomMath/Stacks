module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteria
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteriaProductsToDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentabilityInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.SecondDiagonal
public import StacksFrontier.CategoryTheory.FiberedCategory.EquivalenceInvariance

/-!
# Representability of the diagonal is invariant under equivalence over the site

Let `S` be a scheme contained in a big fppf site `B` and let `𝒳`, `𝒴` be categories fibred in
groupoids over the big fppf site of `S` which are equivalent as categories over that site. Then
the diagonal of `𝒳` is representable by algebraic spaces if and only if the diagonal of `𝒴` is.

The two self-2-fibre-products are *not* compared directly — the same obstruction as in
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_diagonalBasedFunctor_changeBase_iff`
applies, and there is in any case no canonical 1-morphism between them until the equivalence has
been pushed through both factors. The route is **Stacks 045G**: the clause is equivalent to
condition (3) of that tag, representability of every 1-morphism out of a scheme-valued point, and
*that* transports along the equivalence by **Stacks 0457**, because a scheme-valued point of `𝒴`
composed with the quasi-inverse of the equivalence is a scheme-valued point of `𝒳` and the two
sit in a 2-commutative square whose horizontal 1-morphisms are the identity and the quasi-inverse.

## Main results

* `AlgebraicGeometry.Stack.isRepresentableFromSchemes_of_equivalence`: condition (3) of
  Stacks 045G transports along an equivalence over the site.
* `AlgebraicGeometry.Stack.isRepresentableFromSchemes_iff_of_equivalence`: the same, as a
  biconditional.
* `AlgebraicGeometry.Stack.hasRepresentableDiagonal_iff_of_equivalence` and (in the same
  namespace) `isRepresentableByAlgebraicSpaces_diagonalBasedFunctor_iff_of_equivalence`:
  condition (1) of Stacks 045G transports along an equivalence over the site, in its two
  spellings.

## Implementation notes

The equivalence is `CategoryTheory.BasedCategory.Equivalence` (**Stacks 042G**), so its functors
and its unit and counit isomorphisms all lie over the site. Stacks 0457 asks for its two
horizontal 1-morphisms to have underlying functors which are equivalences: for the identity of
the scheme-valued point's source that is `CategoryTheory.Functor.instIsEquivalenceId`, and for the
quasi-inverse it is the forward functor of `CategoryTheory.BasedCategory.Equivalence.equiv` of the
reversed equivalence.

The two spellings of condition (1) are related by
`AlgebraicGeometry.Stack.hasRepresentableDiagonal_iff`, which is `Iff.rfl`; both are provided
because `AlgebraicGeometry.Stack.IsAlgebraicStack` is stated with the second one while the
criteria of Stacks 045G are stated with the first.

`CategoryTheory.BasedCategory.Equivalence` is stated for two categories over the site with the
same object and morphism universes, so the two categories here share them; Stacks 0457, which is
universe-polymorphic in all four, is applied at that common pair.

## References

* [Stacks Project, Tag 042G](https://stacks.math.columbia.edu/tag/042G)
* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
* [Stacks Project, Tag 0457](https://stacks.math.columbia.edu/tag/0457)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u v w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Condition (3) of Stacks 045G transports along an equivalence over the site.** If every
1-morphism to `𝒳` from the category represented by a scheme over `S` is representable by
algebraic spaces, and `𝒴` is equivalent to `𝒳` as a category over the big fppf site of `S`, then
the same holds for `𝒴`.

A scheme-valued point `y` of `𝒴` is compared with the scheme-valued point `y ⋙ e⁻¹` of `𝒳` in the
2-commutative square whose horizontal 1-morphisms are the identity of the point's source and the
quasi-inverse of the equivalence; Stacks 0457 then transfers representability. -/
theorem isRepresentableFromSchemes_of_equivalence
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)}
    (e : BasedCategory.Equivalence 𝒳.val 𝒴.val)
    (h : IsRepresentableFromSchemes B S hS 𝒳) :
    IsRepresentableFromSchemes B S hS 𝒴 := by
  intro U y
  have : Functor.IsEquivalence
      (BasedFunctor.id (schemeFibredCategory B S hS U).val).toFunctor := by
    show Functor.IsEquivalence (𝟭 _)
    infer_instance
  have : Functor.IsEquivalence e.inverse.toFunctor := e.symm.equiv.isEquivalence_functor
  exact (isRepresentableByAlgebraicSpaces_iff_of_equivalences B S hS y
    (BasedFunctor.comp y e.inverse)
    (BasedFunctor.id (schemeFibredCategory B S hS U).val) e.inverse
    (Iso.refl _)).mp (h U (BasedFunctor.comp y e.inverse))

/-- **Condition (3) of Stacks 045G is invariant under equivalence over the site.** -/
theorem isRepresentableFromSchemes_iff_of_equivalence
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)}
    (e : BasedCategory.Equivalence 𝒳.val 𝒴.val) :
    IsRepresentableFromSchemes B S hS 𝒳 ↔ IsRepresentableFromSchemes B S hS 𝒴 :=
  ⟨isRepresentableFromSchemes_of_equivalence B S hS e,
    isRepresentableFromSchemes_of_equivalence B S hS e.symm⟩

/-- **Condition (1) of Stacks 045G is invariant under equivalence over the site.** Two categories
fibred in groupoids over the big fppf site of `S` which are equivalent as categories over the site
have representable diagonals at the same time.

The clause is routed through conditions (2) and (3) of Stacks 045G, which is where the
equivalence can be used; see the module docstring. -/
theorem hasRepresentableDiagonal_iff_of_equivalence
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)}
    (e : BasedCategory.Equivalence 𝒳.val 𝒴.val) :
    HasRepresentableDiagonal B S hS 𝒳 ↔ HasRepresentableDiagonal B S hS 𝒴 :=
  ((hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf B S hS 𝒳).trans
      (isAlgebraicSpaceIsomPresheaf_iff_isRepresentableFromSchemes B S hS 𝒳)).trans
    ((isRepresentableFromSchemes_iff_of_equivalence B S hS e).trans
      ((hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf B S hS 𝒴).trans
        (isAlgebraicSpaceIsomPresheaf_iff_isRepresentableFromSchemes B S hS 𝒴)).symm)

/-- **Condition (1) of Stacks 045G is invariant under equivalence over the site**, in the spelling
`AlgebraicGeometry.Stack.IsAlgebraicStack` uses: representability by algebraic spaces of the
diagonal 1-morphism to the self-2-fibre-product. -/
theorem isRepresentableByAlgebraicSpaces_diagonalBasedFunctor_iff_of_equivalence
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)}
    (e : BasedCategory.Equivalence 𝒳.val 𝒴.val) :
    IsRepresentableByAlgebraicSpaces B S hS (diagonalBasedFunctor B S hS 𝒳) ↔
      IsRepresentableByAlgebraicSpaces B S hS (diagonalBasedFunctor B S hS 𝒴) :=
  ((hasRepresentableDiagonal_iff B S hS 𝒳).symm.trans
      (hasRepresentableDiagonal_iff_of_equivalence B S hS e)).trans
    (hasRepresentableDiagonal_iff B S hS 𝒴)

end AlgebraicGeometry.Stack

end
