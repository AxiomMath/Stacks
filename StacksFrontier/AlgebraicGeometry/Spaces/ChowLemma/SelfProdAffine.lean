module

public import StacksFrontier.AlgebraicGeometry.Spaces.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.DiagonalComplementObj
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.SelfProdUnderlying
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.AffineDiagonal

/-!
# Affineness of a finite self-product over a separated algebraic space

The `n`-fold self-product `U^n = U ×_X ⋯ ×_X U` of an object `U` of the spaces-étale site of
an algebraic space `X` is affine as soon as `U` is affine and `X` is separated, **provided
`n ≥ 1`**. The empty product is excluded, and must be: it is a final object of the site, whose
underlying algebraic space is `X` itself, and a separated `X` need not be affine.

This is the first step of the affineness chain of the proof of [Stacks, Tag 072B]: the
complement `W` of the diagonals in `U^{p+1}` is a *closed* subspace of it by
`AlgebraicGeometry.Space.SpacesEtale.isClosedImmersion_diagonalComplementι`, so once `U^{p+1}`
is affine so is `W`, and from there the quotient `U_p = W/S_{p+1}` is affine by
[Stacks, Tag 03BM].

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.Space.IsAffineSpace.of_isPullback_of_isAbsolutelySeparated`: a fibre
  product of two affine algebraic spaces over a separated algebraic space is affine.
* `AlgebraicGeometry.Space.SpacesEtale.isAffineSpace_underlying_selfProd_succ`: a nonempty
  finite self-product of an affine object of the spaces-étale site of a separated `X` has
  affine underlying algebraic space.

## What is and is not proved

Nothing here carries a Stacks attribute. The fibre-product statement is the composite of
[Stacks, Tag 08GB] part (4)
(`AlgebraicGeometry.Space.isAffineHom_of_affine_source_of_isAbsolutelySeparated`: a morphism
from an affine object to a separated algebraic space is affine), [Stacks, Tag 03WI]
(`AlgebraicGeometry.Space.IsAffineHom.of_isPullback`: affineness of a morphism is stable under
base change) and `AlgebraicGeometry.Space.IsAffineHom.isAffineSpace_source`; each of the three
already carries its own attribute where it has one, and the composite is an unlabelled step of
the proof of Tag 072B.

Separatedness is taken in the absolute sense of [Stacks, Tag 03BS],
`AlgebraicGeometry.Space.IsAbsolutelySeparated`, and not in the relative sense
`AlgebraicGeometry.Space.IsSeparatedOver`. That is the hypothesis Tag 08GB part (4) takes, and
it is the one the mathematics needs: what makes `U ×_X V` affine is that it is a closed
subspace of the *absolute* product `U ×_{Spec ℤ} V`, which is affine with no hypothesis on `S`,
whereas `U ×_S V` is affine only when `S` is. For a separated `S` the two notions of
separatedness of `X` agree, through
`AlgebraicGeometry.Space.isAbsolutelySeparated_of_isSeparated_to_affine`.

## References

* [Stacks Project, Tag 03BS](https://stacks.math.columbia.edu/tag/03BS)
* [Stacks Project, Tag 03WI](https://stacks.math.columbia.edu/tag/03WI)
* [Stacks Project, Tag 072B](https://stacks.math.columbia.edu/tag/072B)
* [Stacks Project, Tag 08GB](https://stacks.math.columbia.edu/tag/08GB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))

/-- **A morphism from an affine algebraic space to a separated algebraic space is affine.**
This is [Stacks, Tag 08GB] part (4) with the source presented as an affine algebraic space
rather than as an affine object of the site: the source is isomorphic to such an object, and
an isomorphism of presheaves is an affine morphism. -/
theorem isAffineHom_of_isAffineSpace_source_of_isAbsolutelySeparated
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G)
    (hF : IsAffineSpace B S hS F) (hG : IsAbsolutelySeparated B S hS hZ G) :
    IsAffineHom B S hS f := by
  obtain ⟨T, hT, ⟨e⟩⟩ := hF
  have _ : MorphismProperty.ContainsIdentities
      (@_root_.AlgebraicGeometry.IsAffineHom.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsMultiplicative.toContainsIdentities
  have _ : MorphismProperty.RespectsIso
      (@_root_.AlgebraicGeometry.IsAffineHom.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have _ : MorphismProperty.ContainsIdentities
      (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.IsAffineHom.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)) :=
    MorphismProperty.ContainsIdentities.inverseImage (BigFppfOver.toScheme B S hS)
  have _ : MorphismProperty.RespectsIso
      (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.IsAffineHom.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)) :=
    MorphismProperty.RespectsIso.inverseImage _ (BigFppfOver.toScheme B S hS)
  have hiso : IsAffineHom B S hS e.hom :=
    isAffineHom_of_presheaf (MorphismProperty.presheaf_of_isIso _ e.hom)
  have hcomp : IsAffineHom B S hS (e.inv ≫ f) :=
    isAffineHom_of_affine_source_of_isAbsolutelySeparated B S hS hZ ⟨T, hT⟩ (e.inv ≫ f) hG
  have hf : e.hom ≫ e.inv ≫ f = f := by rw [← Category.assoc, e.hom_inv_id, Category.id_comp]
  exact hf ▸ isAffineHom_comp B S hS e.hom (e.inv ≫ f) hiso hcomp

/-- **A fibre product of two affine algebraic spaces over a separated algebraic space is
affine.** The morphism `f : F ⟶ X` out of the affine `F` is affine by [Stacks, Tag 08GB]
part (4), its base change `q : P ⟶ G` along `g` is affine by [Stacks, Tag 03WI], and the
source of an affine morphism with affine target is affine.

This is the step of the proof of [Stacks, Tag 072B] that uses separatedness of the space: a
fibre product of two affine *schemes* over a separated space is a closed subscheme of their
absolute product, hence affine. -/
theorem IsAffineSpace.of_isPullback_of_isAbsolutelySeparated
    {X F G P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : F ⟶ X} {g : G ⟶ X}
    {p : P ⟶ F} {q : P ⟶ G} (sq : IsPullback p q f g)
    (hX : IsAbsolutelySeparated B S hS hZ X)
    (hF : IsAffineSpace B S hS F) (hG : IsAffineSpace B S hS G) :
    IsAffineSpace B S hS P :=
  IsAffineHom.isAffineSpace_source
    (IsAffineHom.of_isPullback sq
      (isAffineHom_of_isAffineSpace_source_of_isAbsolutelySeparated B S hS hZ f hF hX)) hG

variable (X : AlgebraicSpaces B S hS)

namespace SpacesEtale

/-- **A nonempty finite self-product of an affine object of the spaces-étale site of a
separated algebraic space is affine.** If `X` is a separated algebraic space over `S` in the
absolute sense of [Stacks, Tag 03BS] and the algebraic space underlying `U` is affine, then so
is the algebraic space underlying the `(n + 1)`-fold self-product `U ×_X ⋯ ×_X U`.

The induction is the one of
`AlgebraicGeometry.Space.SpacesEtale.isRepresentable_underlying_selfProd_succ`: the one-fold
self-product is `U` itself, and a self-product with one more factor has, by
`AlgebraicGeometry.Space.SpacesEtale.underlyingSelfProdSuccIso`, the fibre product over `X` of
`U` with the previous self-product as underlying algebraic space, so
`AlgebraicGeometry.Space.IsAffineSpace.of_isPullback_of_isAbsolutelySeparated` applies.

The empty self-product is excluded, and has to be: it is a final object of the site, whose
underlying algebraic space is `X`, and a separated algebraic space need not be affine. -/
theorem isAffineSpace_underlying_selfProd_succ (U : SpacesEtale B S hS X)
    (hU : IsAffineSpace B S hS (underlying B S hS X U).obj)
    (hX : IsAbsolutelySeparated B S hS hZ X.obj) :
    ∀ n : ℕ, IsAffineSpace B S hS (underlying B S hS X (selfProd B S hS X U (n + 1))).obj
  | 0 =>
      IsAffineSpace.of_iso hU ((ObjectProperty.ι (algebraicSpaceProperty B S hS)).mapIso
        (underlyingSelfProdOneIso B S hS X U).symm)
  | n + 1 =>
      IsAffineSpace.of_iso
        (IsAffineSpace.of_isPullback_of_isAbsolutelySeparated B S hS hZ
          (IsPullback.of_hasPullback U.1.hom.hom (selfProd B S hS X U (n + 1)).1.hom.hom) hX hU
          (isAffineSpace_underlying_selfProd_succ U hU hX n))
        ((pullbackFiberProductIso B S hS U.1.hom
          (selfProd B S hS X U (n + 1)).1.hom).symm.trans
          ((ObjectProperty.ι (algebraicSpaceProperty B S hS)).mapIso
            (underlyingSelfProdSuccIso B S hS X U (n + 1)).symm))

end SpacesEtale

end AlgebraicGeometry.Space

end
