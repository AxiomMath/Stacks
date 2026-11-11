module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.DominantRationalMaps
public import StacksFrontier.RingTheory.GeometricallyIntegral.BirationalResidueField

/-!
# Birationality over a base of integral schemes, tested on generic residue fields

Stacks 0552: for integral schemes `X` and `Y` locally of finite type over a base `S`, with
generic points `x` and `y`, the following are equivalent: (1) `X` and `Y` are `S`-birational,
(2) some nonempty opens of `X` and `Y` are `S`-isomorphic, and (3) `x` and `y` have the same
image `s` in `S` and `κ(x) ≅ κ(y)` as `κ(s)`-extensions.

## Main results

* `AlgebraicGeometry.tfae_dominantBirationalOver_residueField_genericPoint`: Stacks 0552.

## Implementation notes

Item (1) is Stacks' notion of `S`-birationality (Stacks 0A20 (2)), an isomorphism in the
category of irreducible schemes over `S` and dominant `S`-rational maps,
`AlgebraicGeometry.Scheme.DominantBirationalOver`. It is identified with Mathlib's
`AlgebraicGeometry.Scheme.BirationalOver` by
`AlgebraicGeometry.Scheme.dominantBirationalOver_iff_birationalOver`; that notion is equivalent
to (2) by `AlgebraicGeometry.birationalOver_iff_exists_nonempty_open_iso` and to (3) by
`AlgebraicGeometry.birationalOver_iff_generic_residueField_iso`.

In (3), an isomorphism of residue fields is required to commute with the two maps from the
residue field of the common image in `S`, after transport along the equality of the images.

## References

* [Stacks Project, Tag 0552](https://stacks.math.columbia.edu/tag/0552)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **Stacks 0552.** Let `X` and `Y` be integral schemes locally of finite type over `S`, with
generic points `x` and `y`. The following are equivalent: (1) `X` and `Y` are `S`-birational,
that is, isomorphic in the category of irreducible schemes over `S` and dominant `S`-rational
maps; (2) there are nonempty opens of `X` and `Y` which are `S`-isomorphic; (3) `x` and `y` map
to the same point `s` of `S` and `κ(x) ≅ κ(y)` as extensions of `κ(s)`. -/
@[stacks 0552]
theorem tfae_dominantBirationalOver_residueField_genericPoint
    {S X Y : Scheme.{u}} [X.Over S] [Y.Over S]
    [IsIntegral X] [IsIntegral Y]
    [LocallyOfFiniteType (X ↘ S)] [LocallyOfFiniteType (Y ↘ S)] :
    List.TFAE
      [Scheme.DominantBirationalOver S X Y,
        ∃ (U : X.Opens) (V : Y.Opens),
          (U : Set X).Nonempty ∧ (V : Set Y).Nonempty ∧
            ∃ e : U.toScheme ≅ V.toScheme, e.hom ≫ V.ι ≫ Y ↘ S = U.ι ≫ X ↘ S,
        ∃ (h : (X ↘ S) (genericPoint X) = (Y ↘ S) (genericPoint Y))
          (e : X.residueField (genericPoint X) ≅ Y.residueField (genericPoint Y)),
          h ▸ ((X ↘ S).residueFieldMap (genericPoint X) ≫ e.hom) =
            (Y ↘ S).residueFieldMap (genericPoint Y)] := by
  tfae_have 1 ↔ 2 := Scheme.dominantBirationalOver_iff_birationalOver.trans
    (birationalOver_iff_exists_nonempty_open_iso (X ↘ S) (Y ↘ S))
  tfae_have 1 ↔ 3 := Scheme.dominantBirationalOver_iff_birationalOver.trans
    (birationalOver_iff_generic_residueField_iso (X ↘ S) (Y ↘ S))
  tfae_finish

end AlgebraicGeometry

end
