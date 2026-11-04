module

public import StacksFrontier.AlgebraicGeometry.Spaces.AlternatingCech.DiagonalComplementQuotientAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.AlternatingCech.DiagonalComplementSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.FiniteFreeActionSchematicLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedRepresentable

/-!
# The quotient `U_p` is a separated algebraic space

Let `X` be an algebraic space over a scheme `S` and let `U` be an object of its spaces-étale
site with representable and separated underlying algebraic space and separated structure
morphism.  The quotient
`U_p = W_{p+1}/S_{p+1}` of the complement of the diagonals in the `(p+1)`-fold self-product of
`U` over `X` is then a **separated** algebraic space, in the absolute sense of
[Stacks, Tag 03BS] part (1), with **no hypothesis on `X`**.

This is the clause "since `U` is separated, the schemes `W_p` are separated, hence `U_p` is
separated" of the proof of [Stacks, Tag 072C], and it is what that proof uses in place of
separatedness of `X`: the alternating Čech argument of [Stacks, Tag 072B] applies to `U_p`
even when `X` is only quasi-separated.

`AlgebraicGeometry.Space.SpacesEtale.isSeparatedOver_diagonalComplementQuotient` already has the
statement relative to `S`, but it draws the separatedness of `W_p` from separatedness of `X`,
through the empty self-product; the empty self-product is a final object of the site, whose
underlying algebraic space is `X` itself, which is why that hypothesis appears.  Starting the
induction at the *one-fold* self-product instead — which is `U`, and is separated by
hypothesis — removes it, at the cost of excluding the empty product.  That is harmless here: the
alternating Čech spectral sequence only ever forms `W_{p+1}`.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.Space.isAbsolutelySeparated_of_iso`: separatedness transports along an
  isomorphism of presheaves.
* `AlgebraicGeometry.Space.SpacesEtale.isAbsolutelySeparated_underlying_selfProd_succ`: a nonempty
  finite self-product of a separated object of the spaces-étale site is separated.
* `AlgebraicGeometry.Space.SpacesEtale.isAbsolutelySeparated_underlying_diagonalComplement`:
  hence so is the complement `W_{p+1}` of the diagonals in it, an open subspace.
* `AlgebraicGeometry.Space.SpacesEtale.isAbsolutelySeparated_diagonalComplementQuotient`:
  **the quotient `U_p = W_{p+1}/S_{p+1}` is a separated algebraic space.**

## Implementation notes

The last step is [Stacks, Tag 05Z2] part (2),
`AlgebraicGeometry.Space.isAbsolutelySeparated_of_isSurjective_of_universallyClosed`, applied to
the quotient sheaf `V/S_{p+1}` of an object `V` representing `W_{p+1}`, which is `U_p` by
`AlgebraicGeometry.Space.SpacesEtale.diagonalComplementQuotientIsoActionQuotient`: the chart
`h_V ⟶ V/S_{p+1}` is surjective, and it is universally closed because it is finite locally free
after every representable base change
(`AlgebraicGeometry.Space.isFiniteLocallyFree_presheaf_freeActionQuotientMap`), a finite locally
free morphism of schemes being finite and hence universally closed.  Separatedness then descends
from `W_{p+1}`.

The relative statement goes instead through the diagonal of the quotient and the descent of
`AlgebraicGeometry.Space.presheaf_diag_actionQuotient`; that route is not available here, since
it produces separatedness over the base of the site rather than over the terminal scheme, and
the absolute notion is the one [Stacks, Tag 08GB] part (4) consumes.

## References

* [Stacks Project, Tag 03BS](https://stacks.math.columbia.edu/tag/03BS)
* [Stacks Project, Tag 04ZH](https://stacks.math.columbia.edu/tag/04ZH)
* [Stacks Project, Tag 05Z2](https://stacks.math.columbia.edu/tag/05Z2)
* [Stacks Project, Tag 072B](https://stacks.math.columbia.edu/tag/072B)
* [Stacks Project, Tag 072C](https://stacks.math.columbia.edu/tag/072C)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))

/-- **Separatedness of an algebraic space transports along an isomorphism of presheaves.**  An
isomorphism is a monomorphism, hence a separated morphism, so this is [Stacks, Tag 04ZH]
part (1). -/
theorem isAbsolutelySeparated_of_iso {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : F ≅ G)
    (hG : IsAbsolutelySeparated B S hS hZ G) :
    IsAbsolutelySeparated B S hS hZ F :=
  isAbsolutelySeparated_of_isSeparated B S hS hZ hG
    (isSeparated_of_mono e.hom inferInstance)

variable (X : AlgebraicSpaces B S hS)

namespace SpacesEtale

/-- **A nonempty finite self-product of a separated object of the spaces-étale site of `X` is
separated**, with no hypothesis on `X`.  If the algebraic space underlying `U` is separated and
the structure morphism of `U` is separated, then so is the algebraic space underlying the
`(n + 1)`-fold self-product `U ×_X ⋯ ×_X U`.

The induction is the one of
`AlgebraicGeometry.Space.SpacesEtale.isAffineSpace_underlying_selfProd_succ`: the one-fold
self-product is `U` itself, and a self-product with one more factor has the fibre product over
`X` of `U` with the previous self-product as underlying algebraic space, whose second projection
is a base change of the structure morphism of `U` and so separated.

The empty self-product is excluded, and has to be: it is a final object of the site, whose
underlying algebraic space is `X`, and `X` is not assumed separated. -/
theorem isAbsolutelySeparated_underlying_selfProd_succ (U : SpacesEtale B S hS X)
    (hU : IsAbsolutelySeparated B S hS hZ (underlying B S hS X U).obj)
    (hsep : IsSeparated B S hS U.1.hom.hom) :
    ∀ n : ℕ, IsAbsolutelySeparated B S hS hZ
      (underlying B S hS X (selfProd B S hS X U (n + 1))).obj
  | 0 =>
      isAbsolutelySeparated_of_iso B S hS hZ
        ((ObjectProperty.ι (algebraicSpaceProperty B S hS)).mapIso
          (underlyingSelfProdOneIso B S hS X U)) hU
  | n + 1 =>
      isAbsolutelySeparated_of_iso B S hS hZ
        (((pullbackFiberProductIso B S hS U.1.hom
            (selfProd B S hS X U (n + 1)).1.hom).symm.trans
          ((ObjectProperty.ι (algebraicSpaceProperty B S hS)).mapIso
            (underlyingSelfProdSuccIso B S hS X U (n + 1)).symm)).symm)
        (isAbsolutelySeparated_of_isSeparated B S hS hZ
          (isAbsolutelySeparated_underlying_selfProd_succ U hU hsep n)
          (isSeparated_pullbackSnd B S hS (selfProd B S hS X U (n + 1)).1.hom.hom hsep))

/-- **The space `W_{n+1}` of [Stacks, Tag 0726] is a separated algebraic space** when the
algebraic space underlying the chart is separated and the structure morphism of the chart is
separated.  Its inclusion into the self-product is the inclusion of a subfunctor, hence a
monomorphism. -/
theorem isAbsolutelySeparated_underlying_diagonalComplement (U : SpacesEtale B S hS X) (n : ℕ)
    (hsep : IsSeparated B S hS U.1.hom.hom)
    (hU : IsAbsolutelySeparated B S hS hZ (underlying B S hS X U).obj) :
    IsAbsolutelySeparated B S hS hZ
      (underlying B S hS X (diagonalComplement B S hS X U (n + 1) hsep)).obj :=
  isAbsolutelySeparated_of_isSeparated B S hS hZ
    (isAbsolutelySeparated_underlying_selfProd_succ B S hS hZ X U hU hsep n)
    (isSeparated_of_mono
      (Subfunctor.ι (diagonalComplementSubspace B S hS X U (n + 1) hsep).1)
      (inferInstanceAs (Mono (Subfunctor.ι _))))

variable [HasSheafify (BigFppfOver.topology B S hS) (Type u)]

/-- **The quotient `U_p = W_{p+1}/S_{p+1}` is a separated algebraic space**, with no hypothesis
on `X`.

This is [Stacks, Tag 05Z2] part (2) at the chart `h_V ⟶ V/S_{p+1} ≅ U_p` of an object `V`
representing `W_{p+1}`: that chart is surjective, it is
universally closed because it is finite locally free after every representable base change, and
`W_{p+1}` is separated by
`AlgebraicGeometry.Space.SpacesEtale.isAbsolutelySeparated_underlying_diagonalComplement`.

It is the clause "since `U` is separated, the schemes `W_p` are separated, hence `U_p` is
separated" of the proof of [Stacks, Tag 072C]. -/
theorem isAbsolutelySeparated_diagonalComplementQuotient (U : SpacesEtale B S hS X) (p : ℕ)
    (hsep : IsSeparated B S hS U.1.hom.hom)
    (hUrep : (underlying B S hS X U).obj.IsRepresentable)
    (hU : IsAbsolutelySeparated B S hS hZ (underlying B S hS X U).obj) :
    IsAbsolutelySeparated B S hS hZ
      (diagonalComplementQuotient B S hS X U (p + 1) hsep).obj := by
  obtain ⟨V, ⟨e⟩⟩ := exists_siteObj_iso_underlying_diagonalComplement B S hS X U hUrep p hsep
  have hV : IsAbsolutelySeparated B S hS hZ (yoneda.obj V) :=
    isAbsolutelySeparated_of_iso B S hS hZ e
      (isAbsolutelySeparated_underlying_diagonalComplement B S hS hZ X U p hsep hU)
  have hfree := actsFreelyOnNonemptyPoints_diagonalComplementSchemeAut B S hS X U (p + 1) hsep V e
  have hQ := isAlgebraicSpace_actionQuotient_of_actsFreelyOnNonemptyPoints
    (Equiv.Perm (Fin (p + 1))) B hS V (diagonalComplementOverAut B S hS X U (p + 1) hsep V e) hfree
  have hle : (MorphismProperty.inverseImage
        (@Stacks.Morphisms.IsFiniteLocallyFree.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)) ≤
      (MorphismProperty.inverseImage
        (@AlgebraicGeometry.UniversallyClosed.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)) := by
    intro A A' g hg
    have _ : Stacks.Morphisms.IsFiniteLocallyFree ((BigFppfOver.toScheme B S hS).map g) := hg
    have _ : AlgebraicGeometry.IsFinite ((BigFppfOver.toScheme B S hS).map g) :=
      Stacks.Morphisms.IsFiniteLocallyFree.isFinite _
    exact inferInstanceAs
      (AlgebraicGeometry.UniversallyClosed ((BigFppfOver.toScheme B S hS).map g))
  have hpres := MorphismProperty.relative_monotone hle _
    (isFiniteLocallyFree_presheaf_freeActionQuotientMap (Equiv.Perm (Fin (p + 1))) B S hS V
      (diagonalComplementOverAut B S hS X U (p + 1) hsep V e) hfree)
  refine isAbsolutelySeparated_of_iso B S hS hZ
    (diagonalComplementQuotientIsoActionQuotient B S hS X U (p + 1) hsep V e) ?_
  exact isAbsolutelySeparated_of_isSurjective_of_universallyClosed B S hS hZ
    (isAlgebraicSpace_yoneda B S hS V) hQ
    (freeActionQuotientMap (Equiv.Perm (Fin (p + 1))) B S hS V
      (diagonalComplementOverAut B S hS X U (p + 1) hsep V e) hfree)
    (isSurjective_of_presheafSurjective B S hS _
      (surjective_presheaf_freeActionQuotientMap (Equiv.Perm (Fin (p + 1))) B S hS V
        (diagonalComplementOverAut B S hS X U (p + 1) hsep V e) hfree))
    (universallyClosed_of_presheaf_universallyClosed B S hS
      (isAlgebraicSpace_yoneda B S hS V) hQ hpres.rep hpres)
    hV

end SpacesEtale

end AlgebraicGeometry.Space

end
