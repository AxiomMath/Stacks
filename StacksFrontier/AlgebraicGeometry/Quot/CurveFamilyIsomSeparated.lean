module

public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyAutomorphisms
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeMorphismDiagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedQuasiFiniteEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants

/-!
# `Isom_U(Y, X)` of two families of curves is separated over `U`

The separation clause in the proof of Stacks 0DSQ: for families of curves `Y` and `X` over a
scheme `U`, the functor `Isom_U(Y, X)` is separated over `U`. It is a subfunctor of
`Mor_U(Y, X)` (Stacks 0DPP), which is separated over `U` (Stacks 0DPN, from Stacks 0DPM), and a
monomorphism followed by a separated morphism is separated (Stacks 03KQ).

## Main results

* `AlgebraicGeometry.CurveFamily.isSeparated_isomFunctorProjection`: `Isom_U(Y, X) ⟶ U` is
  separated.
* `AlgebraicGeometry.CurveFamily.isQuasiSeparated_isomFunctorProjection`: hence quasi-separated
  (Stacks 03KK).

## References

* [Stacks Project, Tag 0DSQ](https://stacks.math.columbia.edu/tag/0DSQ)
* [Stacks Project, Tag 0DPN](https://stacks.math.columbia.edu/tag/0DPN)
* [Stacks Project, Tag 0DPP](https://stacks.math.columbia.edu/tag/0DPP)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.CurveFamily

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- **`Isom_U(Y, X)` is separated over `U`.** For a family of curves `F` over `U` and a family
`G` whose total space is given a proper morphism `x` of finite presentation to `U`, the
projection `Isom_U(F, G) ⟶ U` is separated: the inclusion into `Mor_U(F, G)` is a monomorphism,
and `Mor_U(F, G) ⟶ U` is separated by Stacks 0DPN (its diagonal is a closed immersion, Stacks
0DPM). -/
theorem isSeparated_isomFunctorProjection (F G : CurveFamily B hZ)
    (x : G.total.obj ⟶ (schemeSpace F.base).obj)
    (hxproper : Space.IsProper B integerBase hZ x)
    (hxfp : Space.IsFinitePresentation B integerBase hZ x) :
    Space.IsSeparated B integerBase hZ (isomFunctorProjection F G x) :=
  Space.isSeparated_comp B integerBase hZ _ _
    (Space.isSeparated_of_mono B integerBase hZ _ inferInstance)
    (Space.isSeparated_relativeHomProjection F.total.property G.total.property
      (schemeSpace F.base).property hxproper.1 hxfp F.finitePresentation F.flat F.proper)

/-- **`Isom_U(Y, X)` is quasi-separated over `U`**, being separated (Stacks 03KK). -/
theorem isQuasiSeparated_isomFunctorProjection (F G : CurveFamily B hZ)
    (x : G.total.obj ⟶ (schemeSpace F.base).obj)
    (hxproper : Space.IsProper B integerBase hZ x)
    (hxfp : Space.IsFinitePresentation B integerBase hZ x) :
    Space.IsQuasiSeparated B integerBase hZ (isomFunctorProjection F G x) :=
  Space.isQuasiSeparated_of_isSeparated B integerBase hZ
    (isSeparated_isomFunctorProjection F G x hxproper hxfp)

end AlgebraicGeometry.CurveFamily

end
