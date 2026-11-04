module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.IsomSpaceFpqcSheaf
public import StacksFrontier.AlgebraicGeometry.Stacks.QuotientStackRepresentableDiagonal
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Equalizers

/-!
# Equalizers in algebraic stacks

A category fibred in groupoids over the big fppf site of a scheme `S` whose isomorphism presheaves
are algebraic spaces has equalizers; in particular every algebraic stack has equalizers, and so
does the quotient stack of a groupoid in algebraic spaces, whose isomorphism sheaves are algebraic
spaces by Stacks 04TB. These are parts (2) and (3) of Stacks 06WY; part (1), fibre products, is
`AlgebraicGeometry.BigFppfOver.hasPullbacks_of_isFiberedInGroupoids`.

## Main results

* `AlgebraicGeometry.Stack.hasEqualizers_of_isAlgebraicSpaceIsomPresheaf`: Stacks 06WY (2).
* `AlgebraicGeometry.Stack.hasEqualizers_of_isAlgebraicStack`: Stacks 06WY (3), for algebraic
  stacks, with the instance `AlgebraicGeometry.Stack.AlgebraicStacks.hasEqualizers`.
* `AlgebraicGeometry.Stack.hasEqualizers_quotientStack`: Stacks 06WY (3), for the quotient
  stacks of its parenthetical.

## Implementation notes

The proof is that of the source. For two morphisms `a b : x ⟶ y` the equalizer is a lift to `x`
of a subobject of `p x`, built in three steps
(`CategoryTheory.Functor.IsFiberedInGroupoids.hasEqualizers_of_morPresheaf`): the equalizer of
`p a` and `p b` in the base, then the locus where the automorphism `i` with `i ≫ a = b` is the
identity. That locus is the one where the sections `id` and `i` of `Isom(x, x)` agree, i.e. the
pullback of the diagonal of the algebraic space `Isom(x, x)` along the pair `(id, i)`, which is a
scheme because the diagonal of an algebraic space is representable
(`CategoryTheory.Presheaf.hasRepresentableEqualizerLoci_of_relativelyRepresentable_diag`). The
isomorphism presheaf of the hypothesis is a presheaf on the big fppf site of the base scheme of
`x`, which is transported to the slice of the site of `S` along the iterated-slice equivalence.

For the quotient stack `[U/R]` of a groupoid in algebraic spaces the isomorphism presheaves are
algebraic spaces by Stacks 04TB, `AlgebraicGeometry.Stack.isAlgebraicSpace_isomPresheaf`, in its
`ULift`-free pointwise form, which
`AlgebraicGeometry.Stack.isAlgebraicSpaceIsomPresheaf_of_pointwiseEquiv` repackages as the
hypothesis of part (2).

## References

* [Stacks Project, Tag 06WY](https://stacks.math.columbia.edu/tag/06WY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u v w t

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The big fppf site of a scheme has equalizers. -/
instance hasEqualizers_bigFppfOver : HasEqualizers (BigFppfOver B S hS) :=
  have : HasBinaryProducts (BigFppfOver B S hS) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  hasEqualizers_of_hasPullbacks_and_binary_products

/-- **Stacks 06WY (2).** Let `𝒳` be a category fibred in groupoids over the big fppf site of `S`
whose isomorphism presheaves `Isom(x, y)` are algebraic spaces. Then `𝒳` has equalizers. -/
@[stacks 06WY "part (2)"]
theorem hasEqualizers_of_isAlgebraicSpaceIsomPresheaf
    (𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS))
    (h : IsAlgebraicSpaceIsomPresheaf B S hS 𝒳) : HasEqualizers 𝒳.val.obj := by
  have hp := 𝒳.isFiberedInGroupoids
  let : 𝒳.val.p.IsFibered := hp.isFibered
  refine hp.hasEqualizers_of_morPresheaf fun U x => ?_
  obtain ⟨F, hF, ⟨e⟩⟩ := h U x x
  have hF' := Presheaf.hasRepresentableEqualizerLoci_of_relativelyRepresentable_diag F
    hF.diagonal_representable
  have h₁ : Presheaf.HasRepresentableEqualizerLoci
      ((Over.iteratedSliceBackward U).op ⋙ 𝒳.val.p.morPresheaf x x) :=
    Presheaf.HasRepresentableEqualizerLoci.of_iso
      (Functor.isoWhiskerRight (Functor.isoWhiskerLeft (Over.iteratedSliceBackward U).op
        (isomPresheafIsoMorPresheaf 𝒳.val.p hp x x).symm) uliftFunctor ≪≫ e.symm) hF'
  have h₂ := Presheaf.HasRepresentableEqualizerLoci.comp_equivalence
    (Over.iteratedSliceEquiv U) h₁
  exact Presheaf.HasRepresentableEqualizerLoci.of_iso'
    (P := 𝒳.val.p.morPresheaf x x)
    (Functor.isoWhiskerRight (NatIso.op (Over.iteratedSliceEquiv U).unitIso)
      (𝒳.val.p.morPresheaf x x)).symm h₂

/-- **Stacks 06WY, part (3).** An algebraic stack over `S` has equalizers, its isomorphism
presheaves being algebraic spaces. -/
@[stacks 06WY "part (3)"]
theorem hasEqualizers_of_isAlgebraicStack
    (𝒳 : CatFiberedInGroupoids.{u, v, u + 1, t} (BigFppfOver B S hS))
    (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val) : HasEqualizers 𝒳.val.obj :=
  hasEqualizers_of_isAlgebraicSpaceIsomPresheaf B S hS 𝒳
    (isAlgebraicSpaceIsomPresheaf_of_isAlgebraicStack_univ B S hS 𝒳 h𝒳)

/-- An algebraic stack over `S` has equalizers: `hasEqualizers_of_isAlgebraicStack` as an
instance on `AlgebraicGeometry.Stack.AlgebraicStacks`. -/
instance AlgebraicStacks.hasEqualizers (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    HasEqualizers 𝒳.val.val.obj :=
  hasEqualizers_of_isAlgebraicStack B S hS 𝒳.val 𝒳.property

/-- **Stacks 06WY, part (3), for quotient stacks.** The quotient stack `[U/R]` of a groupoid in
algebraic spaces over `S` has equalizers.

Its isomorphism presheaves are algebraic spaces by Stacks 04TB,
`AlgebraicGeometry.Stack.isAlgebraicSpace_isomPresheaf`, and part (2) applies. -/
@[stacks 06WY "part (3), the quotient stacks of its parenthetical"]
theorem hasEqualizers_quotientStack {A : AlgebraicSpaces B S hS}
    (G : GroupoidInAlgebraicSpaces B S hS A) :
    HasEqualizers (quotientStack G).obj :=
  hasEqualizers_of_isAlgebraicSpaceIsomPresheaf B S hS
    (CatFiberedInGroupoids.mk (quotientStack G) (isFiberedInGroupoids_quotientStack G))
    (isAlgebraicSpaceIsomPresheaf_of_pointwiseEquiv B S hS _
      fun T x y => isAlgebraicSpace_isomPresheaf B S hS A G T x y)

end AlgebraicGeometry.Stack

end
