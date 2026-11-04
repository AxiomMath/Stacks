module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleZariskiLocalCartesian
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.AffineDiagonalTarget

/-!
# A covering family of the final object of `X_étale` whose members are affine over `Y`

Let `a : X ⟶ Y` be a morphism of schemes of a big étale site. For a separated `Y`, in particular
for an affine `Y`, this file constructs a covering family of the final object of `X_étale` whose
members are affine over `Y`.

The family consists of the affine opens of `X`, viewed as objects of `X_étale` through
`AlgebraicGeometry.SmallEtale.opensToSmallEtale`. The affine opens form a Zariski covering of
`X`, and the image of a Zariski covering covers the final object of the small étale site. The
index type is `X.affineOpens`, which lies in `Type u`, so the family is a
`CategoryTheory.PreZeroHypercover.{u}`.

A morphism from an affine scheme to a separated scheme is affine [Stacks, Tag 01SG] part (4), so
the members of the family are affine over `Y` when `Y` is separated. For a non-separated `Y` a
morphism `U ⟶ Y` out of an affine scheme need not be affine.

## Main definitions

* `AlgebraicGeometry.SmallEtale.affineOpensHypercoverFinal`: the affine opens of `S` as a
  `CategoryTheory.PreZeroHypercover.{u}` of the final object of `S_étale`.
* `AlgebraicGeometry.SmallEtale.toBaseHom`: the structure morphism to `Y` of an object of
  `X_étale`.

## Main results

* `AlgebraicGeometry.SmallEtale.coversTop_affineOpensHypercoverFinal`: this family covers the
  final object of `S_étale`.
* `AlgebraicGeometry.SmallEtale.isAffine_toScheme_affineOpensHypercoverFinal`: its members have
  affine underlying scheme.
* `AlgebraicGeometry.SmallEtale.isAffineHom_of_isAffine_toScheme`: every morphism from the
  underlying scheme of an object of `X_étale` with affine underlying scheme to a separated `Y` is
  affine.
* `AlgebraicGeometry.SmallEtale.exists_coversTop_isAffineHom_of_isSeparated`: for a separated
  `Y`, there is a covering family of the final object of `X_étale` whose members have affine
  underlying scheme and are affine over `Y`.
* `AlgebraicGeometry.SmallEtale.exists_coversTop_isAffineHom_of_isAffine`: the same for an
  affine `Y`.

## References

* [Stacks Project, Tag 01SG](https://stacks.math.columbia.edu/tag/01SG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.SmallEtale

section Family

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The affine opens of `S` as a `CategoryTheory.PreZeroHypercover.{u}` of the final object of
`S_étale`, indexed by `AlgebraicGeometry.Scheme.affineOpens`. -/
public def affineOpensHypercoverFinal : PreZeroHypercover.{u} (final B S hS) where
  I₀ := S.affineOpens
  X V := (opensToSmallEtale B S hS).obj (V : S.Opens)
  f _ := (finalIsTerminal B S hS).from _

/-- The member of `AlgebraicGeometry.SmallEtale.affineOpensHypercoverFinal` indexed by an affine
open `V` is the image of `V` under `AlgebraicGeometry.SmallEtale.opensToSmallEtale`. -/
@[simp]
public theorem affineOpensHypercoverFinal_X (V : S.affineOpens) :
    (affineOpensHypercoverFinal B S hS).X V = (opensToSmallEtale B S hS).obj (V : S.Opens) :=
  rfl

/-- The affine opens of `S` cover the final object of `S_étale`. -/
public theorem coversTop_affineOpensHypercoverFinal :
    (topology B S hS).CoversTop (affineOpensHypercoverFinal B S hS).X :=
  coversTop_opensToSmallEtale B S hS (fun V : S.affineOpens ↦ (V : S.Opens))
    (coversTop_affineOpens S)

/-- The underlying scheme of a member of
`AlgebraicGeometry.SmallEtale.affineOpensHypercoverFinal` is the affine open itself, hence
affine. -/
public instance isAffine_toScheme_affineOpensHypercoverFinal (V : S.affineOpens) :
    AlgebraicGeometry.IsAffine
      ((toScheme B S hS).obj ((affineOpensHypercoverFinal B S hS).X V)) :=
  V.2

end Family

section AffineOverBase

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (a : X ⟶ Y)

/-- If `Y` is separated and `U` is an object of `X_étale` with affine underlying scheme, then
every morphism from the underlying scheme of `U` to `Y` is affine. -/
public theorem isAffineHom_of_isAffine_toScheme [Y.obj.IsSeparated]
    (U : SmallEtale B X.obj X.property)
    (hU : AlgebraicGeometry.IsAffine ((toScheme B X.obj X.property).obj U))
    (g : (toScheme B X.obj X.property).obj U ⟶ Y.obj) : IsAffineHom g :=
  have := hU
  isAffineHom_of_isAffine_of_isSeparated g

/-- The structure morphism to `Y` of an object of the small étale site of `X`: its structure
morphism to `X`, followed by `a`. -/
public abbrev toBaseHom (U : SmallEtale B X.obj X.property) :
    (toScheme B X.obj X.property).obj U ⟶ Y.obj :=
  B.inclusion.map U.obj.hom ≫ schemeHom B a

/-- If `Y` is separated, an object of `X_étale` with affine underlying scheme has affine
structure morphism to `Y`. -/
public theorem isAffineHom_toBaseHom [Y.obj.IsSeparated] (U : SmallEtale B X.obj X.property)
    (hU : AlgebraicGeometry.IsAffine ((toScheme B X.obj X.property).obj U)) :
    IsAffineHom (toBaseHom B a U) :=
  isAffineHom_of_isAffine_toScheme B U hU _

/-- If `Y` is separated, there is a `CategoryTheory.PreZeroHypercover.{u}` of the final object
of `X_étale` which covers it, whose members have affine underlying scheme, and whose members are
affine over `Y`. -/
public theorem exists_coversTop_isAffineHom_of_isSeparated [Y.obj.IsSeparated] :
    ∃ E : PreZeroHypercover.{u} (final B X.obj X.property),
      (topology B X.obj X.property).CoversTop E.X ∧
        (∀ i, AlgebraicGeometry.IsAffine ((toScheme B X.obj X.property).obj (E.X i))) ∧
        ∀ i, IsAffineHom (toBaseHom B a (E.X i)) :=
  ⟨affineOpensHypercoverFinal B X.obj X.property,
    coversTop_affineOpensHypercoverFinal B X.obj X.property,
    fun i ↦ isAffine_toScheme_affineOpensHypercoverFinal B X.obj X.property i,
    fun i ↦ isAffineHom_toBaseHom B a _
      (isAffine_toScheme_affineOpensHypercoverFinal B X.obj X.property i)⟩

/-- If `Y` is affine, there is a `CategoryTheory.PreZeroHypercover.{u}` of the final object of
`X_étale` which covers it, whose members have affine underlying scheme, and whose members are
affine over `Y`. -/
public theorem exists_coversTop_isAffineHom_of_isAffine
    [AlgebraicGeometry.IsAffine Y.obj] :
    ∃ E : PreZeroHypercover.{u} (final B X.obj X.property),
      (topology B X.obj X.property).CoversTop E.X ∧
        (∀ i, AlgebraicGeometry.IsAffine ((toScheme B X.obj X.property).obj (E.X i))) ∧
        ∀ i, IsAffineHom (toBaseHom B a (E.X i)) :=
  exists_coversTop_isAffineHom_of_isSeparated B a

end AffineOverBase

end AlgebraicGeometry.SmallEtale

end
