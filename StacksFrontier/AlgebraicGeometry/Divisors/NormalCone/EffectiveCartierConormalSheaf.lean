module

public import StacksFrontier.AlgebraicGeometry.Conormal.DegreeOne
public import StacksFrontier.AlgebraicGeometry.Divisors.DivisorPicardClass
public import StacksFrontier.AlgebraicGeometry.Divisors.NormalCone.NormalBundle

/-!
# The conormal sheaf of an effective Cartier divisor, as the degree-one piece of the conormal
algebra

Let `X` be a scheme and `D ⊆ X` an effective Cartier divisor. That the conormal sheaf
`𝒞_{D/X}` is then an invertible `𝒪_D`-module is already proved, as
`Stacks.Divisors.isInvertible_immersionConormalSheaf`: it is the restriction `ℐ_D|_D` of the
ideal sheaf by [Stacks, Tag 0B3P], and the pullback of an invertible module is invertible.

That statement is about `Stacks.Thickenings.immersionConormalSheaf`, the conormal sheaf built as
the pullback of the defining ideal along `i.liftCoborder`. This file transports it to the *other*
conormal sheaf of the development, `Stacks.Conormal.conormalSheafDegreeOne`, the degree-one piece
`𝒞_{D/X,1}` of the conormal algebra of [Stacks, Tag 0630] — and to the spelling of invertibility
that the Chow and Gysin machinery consumes.

Both moves are needed and neither is cosmetic:

* `Stacks.Conormal.conormalSheafDegreeOne` is the sheaf the normal cone and the normal bundle of
  [Stacks, Tag 0636] are built from (`Stacks.Conormal.normalBundle` is the vector bundle of
  *this* sheaf), so it is the one an argument about `C_DX` has to know is invertible. The two
  conormal sheaves are different objects, compared by
  `Stacks.Conormal.conormalDegreeOneIso` ([Stacks, Tag 0632] in degree one).
* `Stacks.Divisors.isInvertible_immersionConormalSheaf` is stated for
  `Stacks.SheafOfModules.IsInvertible`, while `Stacks.Divisors.IsEffectiveCartierDivisor`,
  `Stacks.LineBundle.Situation` and every Gysin and bivariant declaration are stated for
  `AlgebraicGeometry.SheafOfModules.IsInvertible`. The two classes are moved across by the
  canonical bridge of `StacksFrontier.AlgebraicGeometry.InvertibleBridge.Basic`.

## Main results

* `Stacks.Conormal.isInvertible_conormalSheafDegreeOne_of_isEffectiveCartierDivisor`:
  **the degree-one piece of the conormal algebra of an effective Cartier divisor is an invertible
  module**, in the spelling the Chow machinery consumes.

## Implementation notes

No Stacks attribute is placed here. The mathematical content — `𝒞_{D/X} = ℐ_D|_D` for an
effective Cartier divisor, and invertibility of a pullback — is [Stacks, Tag 0B3P] and
[Stacks, Tag 0B8L], both already registered on their own carriers
(`Stacks.Divisors.conormalSheafIsoNegativeTwist`,
`RingedSpaceModuleAdjunction.modulePullback_isInvertible`). What is below is the transport of an
already-registered result along an already-registered identification, so a tag on it would mark a
proof step rather than a source statement.

## References

* [Stacks Project, Tag 0B3P](https://stacks.math.columbia.edu/tag/0B3P)
* [Stacks Project, Tag 0632](https://stacks.math.columbia.edu/tag/0632)
* [Stacks Project, Tag 0636](https://stacks.math.columbia.edu/tag/0636)
* [Stacks Project, Tag 0637](https://stacks.math.columbia.edu/tag/0637)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Conormal

/-- **The degree-one piece `𝒞_{D/X,1}` of the conormal algebra of an effective Cartier divisor
is an invertible module on `D`.**

This is `Stacks.Divisors.isInvertible_immersionConormalSheaf` — the conormal sheaf of an
effective Cartier divisor is the restriction of its ideal sheaf, hence invertible — carried along
the degree-one identification `Stacks.Conormal.conormalDegreeOneIso` of [Stacks, Tag 0632] and
across to `AlgebraicGeometry.SheafOfModules.IsInvertible`, the class in which
`Stacks.Divisors.IsEffectiveCartierDivisor` and the Chow machinery are stated. -/
theorem isInvertible_conormalSheafDegreeOne_of_isEffectiveCartierDivisor {X : Scheme.{u}}
    (D : X.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor D] :
    AlgebraicGeometry.SheafOfModules.IsInvertible
      D.subscheme.sheaf.obj D.subscheme.ringCatSheaf.property
      (conormalSheafDegreeOne D.subschemeι) :=
  have : Stacks.SheafOfModules.IsInvertible D.subscheme.sheaf.obj
      D.subscheme.ringCatSheaf.property (conormalSheaf D.subschemeι) :=
    Stacks.Divisors.isInvertible_immersionConormalSheaf D
  @Stacks.InvertibleBridge.algebraicGeometryIsInvertible_of_stacksIsInvertible _ _ _ _ _ _
    (Stacks.SheafOfModules.isInvertible_of_iso _ _ (conormalDegreeOneIso D.subschemeι))

end Stacks.Conormal

end
