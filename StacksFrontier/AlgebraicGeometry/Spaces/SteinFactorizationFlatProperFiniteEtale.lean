module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProperFlatStein.FiniteEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperFlatStein.FibreBettiNumbers
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperFlatStructureSheafPushforward

/-!
# Stacks 0E0D: the Stein factorization of a flat proper morphism with reduced fibres

Let `f : X ⟶ Y` be a proper morphism of algebraic spaces over `S` with Stein factorization
`X ⟶ Y' ⟶ Y` (Stacks 0A1C), `Y'` the normalization of `Y` in `X`.  If `f` is of finite
presentation, flat, with geometrically reduced fibres, then `Y' ⟶ Y` is finite étale.

## Main results

* `AlgebraicGeometry.Space.isFinite_and_isEtale_normalizationInQcqsHom`: **Stacks 0E0D**.

## Implementation notes

The proof is
`AlgebraicGeometry.Space.ProperFlatStein.isFinite_and_isEtale_normalizationInQcqsHom_of_inputs`,
fed with Stacks 0E0R (1) and (2) for the degree-zero Betti numbers of the fibres
(`AlgebraicGeometry.Space.ProperFlatStein.fibreBetti_baseChange`,
`AlgebraicGeometry.Space.ProperFlatStein.upperSemicontinuous_fibreBetti`) and with Stacks 0E0S
(`AlgebraicGeometry.Space.isIso_structureSharp_and_baseChange_of_geometricFibres`).

## References

* [Stacks Project, Tag 0E0D](https://stacks.math.columbia.edu/tag/0E0D)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0E0D.**  Let `f : X ⟶ Y` be a proper morphism of algebraic spaces over `S`, and let
`X ⟶ Y' ⟶ Y` be its Stein factorization (Stacks 0A1C): `Y'` is the normalization of `Y` in `X`,
`AlgebraicGeometry.Space.normalizationInQcqs`, with structure morphism
`AlgebraicGeometry.Space.normalizationInQcqsHom`.  If `f` is of finite presentation, flat, with
geometrically reduced fibres (Stacks 0E08), then `Y' ⟶ Y` is finite étale. -/
@[stacks 0E0D "for the Stein factorization X ⟶ Y' ⟶ Y of 0A1C, Y' the normalization of Y in X: \
Y' ⟶ Y is finite and étale when f is proper, flat, of finite presentation, with geometrically \
reduced fibres"]
theorem isFinite_and_isEtale_normalizationInQcqsHom
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsProper B S hS f.hom)
    (hfp : IsFinitePresentation B S hS f.hom) (hfl : IsFlat B S hS f.hom)
    (hred : ∀ y, IsGeometricallyReducedFibreAt B S hS f.hom X.2 Y.2 y) :
    let h := isQuasiCompact_isQuasiSeparated_of_isProper B S hS f hf
    IsFinite B S hS (normalizationInQcqsHom B S hS f h.1 h.2).hom ∧
      IsEtale B S hS (normalizationInQcqsHom B S hS f h.1 h.2).hom :=
  ProperFlatStein.isFinite_and_isEtale_normalizationInQcqsHom_of_inputs B S hS
    (fun {_ _} f hf hfp F hFfp hF {_} g i =>
      ProperFlatStein.fibreBetti_baseChange f hf hfp F hFfp hF g i)
    (fun f hf hfp F hFfp hF i =>
      ProperFlatStein.upperSemicontinuous_fibreBetti f hf hfp F hFfp hF i)
    (fun f hf hfl hfp hred hconn =>
      isIso_structureSharp_and_baseChange_of_geometricFibres B S hS f hf hfl hfp hred hconn)
    f hf hfp hfl hred

end AlgebraicGeometry.Space

end
