module

public import StacksFrontier.AlgebraicGeometry.Spaces.AlternatingCech.DiagonalComplementQuotientScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.DiagonalComplementAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.DiagonalComplementObj
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.FreeActionQuotientAffine

/-!
# Affineness of the quotient `U_p`

The quotient `U_p = W_p / S_{p+1}` of the complement of the diagonals in `U^{p+1}` by the
action of the symmetric group is an affine algebraic space over `S`, for an affine chart `U`
over a separated `X`.

This closes the affineness chain of the proof of [Stacks, Tag 072B]:

* (a) `U^{p+1}` is affine, by
  `AlgebraicGeometry.Space.SpacesEtale.isAffineSpace_underlying_selfProd_succ`;
* (b) `W_p ↪ U^{p+1}` is a closed immersion, by
  `AlgebraicGeometry.Space.SpacesEtale.isClosedImmersion_diagonalComplementι`;
* (c) a closed subspace of an affine space is affine, by
  `AlgebraicGeometry.Space.IsAffineSpace.of_isClosedImmersion`, whence `W_p` is affine by
  `AlgebraicGeometry.Space.SpacesEtale.isAffineSpace_underlying_diagonalComplement`;
* (d) `U_p = W_p/S_{p+1}` is affine: it is the quotient sheaf `V/S_{p+1}` of the graph relation
  of the transported action on an object `V` representing `W_p`, by
  `AlgebraicGeometry.Space.SpacesEtale.diagonalComplementQuotientIsoActionQuotient`, and that is
  affine by `AlgebraicGeometry.Space.isAffineSpace_actionQuotient_of_isAffine`, which is
  [Stacks, Tag 03BM] for the graph relation of the action.

The affineness of `U_p` is one of the two inputs the inner vanishing of Tag 072B needs, the other
being the `E₁`-page identification `Ext^q(K^p, ℱ) ≅ H^q(U_p, ℱ|_{U_p} ⊗ ℤ(χ_p))`, which is
`AlgebraicGeometry.Space.SpacesEtale.nonempty_zExtKoszulSignTwistAddEquiv`.

Separatedness of `X` is taken in the absolute sense of [Stacks, Tag 03BS], as in step (a); the
hypothesis on `U` is affineness of its underlying algebraic space, which for a chart of the
spaces-étale site is the usual hypothesis in the proof of Tag 072B.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.Space.SpacesEtale.isAffineSpace_diagonalComplementQuotient`: the quotient
  `U_p` is an affine algebraic space.

## References

* [Stacks Project, Tag 03BM](https://stacks.math.columbia.edu/tag/03BM)
* [Stacks Project, Tag 072B](https://stacks.math.columbia.edu/tag/072B)
* [Stacks Project, Tag 0726](https://stacks.math.columbia.edu/tag/0726)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.SpacesEtale

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u})) (X : AlgebraicSpaces B S hS)
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)]

/-- **The quotient `U_p = W_p/S_{p+1}` is an affine algebraic space.** The complement `W_p` of
the diagonals in the `(p + 1)`-fold self-product of an affine chart `U` over a separated `X` is
affine by `AlgebraicGeometry.Space.SpacesEtale.isAffineSpace_underlying_diagonalComplement`, so
an object `V` of the site representing it has affine underlying scheme by
`AlgebraicGeometry.Space.isAffine_toScheme_obj_of_isAffineSpace`, and the action of `S_{p+1}`
on it is free by
`AlgebraicGeometry.Space.SpacesEtale.actsFreelyOnNonemptyPoints_diagonalComplementSchemeAut`;
`AlgebraicGeometry.Space.isAffineSpace_actionQuotient_of_isAffine`, which is
[Stacks, Tag 03BM], then represents `V/S_{p+1}` by the spectrum of the ring of invariant
functions, and `V/S_{p+1}` is `U_p` by
`AlgebraicGeometry.Space.SpacesEtale.diagonalComplementQuotientIsoActionQuotient`. -/
theorem isAffineSpace_diagonalComplementQuotient (U : SpacesEtale B S hS X) (p : ℕ)
    (hsep : IsSeparated B S hS U.1.hom.hom)
    (hU : IsAffineSpace B S hS (underlying B S hS X U).obj)
    (hX : IsAbsolutelySeparated B S hS hZ X.obj) :
    IsAffineSpace B S hS (diagonalComplementQuotient B S hS X U (p + 1) hsep).obj := by
  obtain ⟨T, hT, ⟨i⟩⟩ := hU
  obtain ⟨V, ⟨e⟩⟩ := exists_siteObj_iso_underlying_diagonalComplement B S hS X U
    (Functor.IsRepresentable.mk' i.symm) p hsep
  exact IsAffineSpace.of_iso
    (isAffineSpace_actionQuotient_of_isAffine (Equiv.Perm (Fin (p + 1))) B S hS V
      (diagonalComplementOverAut B S hS X U (p + 1) hsep V e)
      (actsFreelyOnNonemptyPoints_diagonalComplementSchemeAut B S hS X U (p + 1) hsep V e)
      (isAffine_toScheme_obj_of_isAffineSpace V
        (IsAffineSpace.of_iso
          (isAffineSpace_underlying_diagonalComplement B S hS hZ X U p hsep ⟨T, hT, ⟨i⟩⟩ hX)
          e.symm)))
    (diagonalComplementQuotientIsoActionQuotient B S hS X U (p + 1) hsep V e).symm

end AlgebraicGeometry.Space.SpacesEtale

end
