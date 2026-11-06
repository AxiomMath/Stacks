module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.DiagonalComplementClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.SelfProdUnderlying
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae

/-!
# Quasi-compactness of a finite self-product of the spaces-étale site

The `n`-fold self-product `U^n = U ×_X ⋯ ×_X U` of an object `U` of the spaces-étale site of an
algebraic space `X` has quasi-compact underlying algebraic space as soon as `X` is
quasi-compact and the structure morphism of `U` is a quasi-compact morphism.

## Main results

* `AlgebraicGeometry.Space.SpacesEtale.isQuasiCompactSpace_underlying_selfProd`: a finite
  self-product of the spaces-étale site has quasi-compact underlying algebraic space.
* `AlgebraicGeometry.Space.SpacesEtale.isQuasiCompactSpace_underlying_diagonalComplement`: so
  does the complement of the diagonals in it.

## References

* [Stacks Project, Tag 03E3](https://stacks.math.columbia.edu/tag/03E3)
* [Stacks Project, Tag 03HE](https://stacks.math.columbia.edu/tag/03HE)
* [Stacks Project, Tag 089J](https://stacks.math.columbia.edu/tag/089J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out without
this shortcut). -/
private instance (priority := high) hasPullback_presheaf_selfProdQuasiCompact
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

namespace SpacesEtale

/-- If `X` is a quasi-compact algebraic space over `S` and the structure morphism of `U` is a
quasi-compact morphism, then the algebraic space underlying the `n`-fold self-product
`U ×_X ⋯ ×_X U` is quasi-compact. -/
theorem isQuasiCompactSpace_underlying_selfProd (U : SpacesEtale B S hS X)
    (hX : IsQuasiCompactSpace B S hS X.1)
    (hU : IsQuasiCompact B S hS U.1.hom.hom) (n : ℕ) :
    IsQuasiCompactSpace B S hS (underlying B S hS X (selfProd B S hS X U n)).1 := by
  induction n with
  | zero =>
      have hlim : IsLimit (Fan.mk (∏ᶜ fun _ : Fin 0 => U) (Pi.π fun _ : Fin 0 => U)) :=
        productIsProduct _
      have hT : IsTerminal (selfProd B S hS X U 0) :=
        (isLimitEquivIsTerminalOfIsEmpty _ _) hlim
      refine IsQuasiCompactSpace.of_iso B S hS hX ?_
      exact ((ObjectProperty.ι (algebraicSpaceProperty B S hS)).mapIso
        ((toSpaces B S hS X).mapIso
          ((final_isTerminal B S hS X).uniqueUpToIso hT)))
  | succ n ih =>
      have hqc := hU (underlying B S hS X (selfProd B S hS X U n)).1
        (underlying B S hS X (selfProd B S hS X U n)).2 ih
        (selfProd B S hS X U n).1.hom.hom
      refine IsQuasiCompactSpace.of_iso B S hS
        (IsQuasiCompactSpace.of_iso B S hS hqc
          (pullbackSymmetry (selfProd B S hS X U n).1.hom.hom U.1.hom.hom)) ?_
      refine (pullbackFiberProductIso B S hS U.1.hom
        (selfProd B S hS X U n).1.hom).symm ≪≫ ?_
      exact (ObjectProperty.ι (algebraicSpaceProperty B S hS)).mapIso
        (underlyingSelfProdSuccIso B S hS X U n).symm

/-- If `X` is a quasi-compact algebraic space over `S` and the structure morphism of `U` is
separated and quasi-compact, then the algebraic space underlying the complement of the diagonals
in the `n`-fold self-product `U ×_X ⋯ ×_X U` is quasi-compact. -/
theorem isQuasiCompactSpace_underlying_diagonalComplement (U : SpacesEtale B S hS X)
    (hX : IsQuasiCompactSpace B S hS X.1)
    (hU : IsQuasiCompact B S hS U.1.hom.hom) (n : ℕ)
    (hsep : IsSeparated B S hS U.1.hom.hom) :
    IsQuasiCompactSpace B S hS
      (underlying B S hS X (diagonalComplement B S hS X U n hsep)).1 :=
  isQuasiCompactSpace_diagonalComplement B S hS X U n hsep
    (isQuasiCompactSpace_underlying_selfProd B S hS X U hX hU n)

end SpacesEtale

end AlgebraicGeometry.Space

end
