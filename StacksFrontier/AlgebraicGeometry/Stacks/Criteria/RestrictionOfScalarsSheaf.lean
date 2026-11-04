module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeMorphismSheaf
public import StacksFrontier.AlgebraicGeometry.Stacks.Criteria.RestrictionOfScalarsCartesian

/-!
# The restriction of scalars is an fppf sheaf

Let `S` be a scheme contained in a big fppf site `B` and let `x : X ⟶ Z` and `z : Z ⟶ Q` be
morphisms of algebraic spaces over `S` — the source writes the base `Q` as `B`, a name that here
belongs to the site. The restriction of scalars `Res_{Z/Q}(X)` of Stacks 05YA is a sheaf on the
big fppf site of `S`. This is part (1) of **Stacks 05YB**; part (2), the description of the
morphisms into it from an algebraic space, is
`AlgebraicGeometry.Space.restrictionOfScalarsHomEquiv`.

## Main results

* `AlgebraicGeometry.Space.isSheaf_restrictionOfScalars`: **Stacks 05YB**, part (1).

## Implementation notes

The source descends a pair `(a, b)` along an fppf covering: the first component descends by
fppf descent of morphisms of algebraic spaces, and then so does the second, the base change
`T ×_{a, Q} Z` of the descended first component being covered by its fibre products with the
members of the covering. That argument is already carried out for the pairs of Stacks 05Y1, and
its conclusion is part (1) of Stacks 05Y3, `AlgebraicGeometry.Space.isSheaf_relativeHom`.

Nothing of it has to be repeated here, because a pair of Stacks 05Y9 is a pair of Stacks 05Y1
whose second component lies over `Z`, and that condition is cut out by a cartesian square: the
restriction of scalars is the fibre product of `Mor_Q(Z, X)` and `Q` over `Mor_Q(Z, Z)`, which is
Stacks 05YE (`AlgebraicGeometry.Space.isPullback_restrictionOfScalars_relativeHomData`). The
three other corners are sheaves — the two relative morphism functors by Stacks 05Y3 and `Q`
because it is an algebraic space — and a fibre product of sheaves of types, computed in
presheaves, is a sheaf.

## References

* [Stacks Project, Tag 05YB](https://stacks.math.columbia.edu/tag/05YB)
* [Stacks Project, Tag 05Y3](https://stacks.math.columbia.edu/tag/05Y3)
* [Stacks Project, Tag 05YE](https://stacks.math.columbia.edu/tag/05YE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Stacks 05YB**, part (1). For morphisms `x : X ⟶ Z` and `z : Z ⟶ Q` of algebraic spaces
over `S`, the restriction of scalars `Res_{Z/Q}(X)` of Stacks 05YA is a sheaf on the big fppf
site of `S`.

A pair `(a, b)` of Stacks 05Y9 is a pair of Stacks 05Y1 whose second component lies over `Z`,
and the cartesian square of Stacks 05YE presents `Res_{Z/Q}(X)` as the fibre product of
`Mor_Q(Z, X)` and `Q` over `Mor_Q(Z, Z)`. The descent of pairs the source carries out is
therefore already done: it is part (1) of Stacks 05Y3 for the two relative morphism functors,
and the fibre product of sheaves of types is a sheaf. -/
@[stacks 05YB "part (1): `Res_{Z/B}(X)` is a sheaf on the big fppf site of `S`"]
theorem isSheaf_restrictionOfScalars {X Z Q : AlgebraicSpaces B S hS} (x : X ⟶ Z) (z : Z ⟶ Q) :
    Presheaf.IsSheaf (BigFppfOver.topology B S hS)
      (restrictionOfScalars B S hS x z).presheaf :=
  (Presheaf.isSheaf_of_iso_iff
      (isPullback_restrictionOfScalars_relativeHomData x z).isoPullback).mpr
    (Presheaf.isSheaf_pullback _ _ _
      (isSheaf_relativeHom B S hS Z.obj X.obj Q.obj z.hom (x.hom ≫ z.hom) Z.property X.property
        Q.property)
      Q.property.isSheaf
      (isSheaf_relativeHom B S hS Z.obj Z.obj Q.obj z.hom z.hom Z.property Z.property
        Q.property))

end AlgebraicGeometry.Space

end
