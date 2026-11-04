module

public import StacksFrontier.AlgebraicGeometry.Quot.CurvesOpenVersality

/-!
# Both clauses of Stacks 0D59 from the Noetherian clause of Stacks 0D3X

Stacks 0D59 has two clauses: the stack of curves satisfies openness of versality over `Spec ℤ`,
and the base change of that stack to any Noetherian scheme `S` satisfies openness of versality
over `S`. Its proof reads both off the corresponding clauses of Stacks 0D3X for the stack
`Spaces'_{fp, flat, proper}` of finitely presented, flat and proper algebraic spaces.

The two theorems of `StacksFrontier.AlgebraicGeometry.Quot.CurvesOpenVersality` carry the transport
along the comparison functor and take openness of versality for `Spaces'_{fp, flat, proper}` over
the base in question as an argument. This file takes instead the Noetherian clause of
Stacks 0D3X *for every Noetherian base at once*, and derives both clauses of Stacks 0D59 from it:
`Spec ℤ` is Noetherian, so the first clause of Stacks 0D59 needs no separate input.

The converse direction is not available, and this is why the Noetherian clause is the one taken.
Openness of versality over `S` (Stacks 07XQ) quantifies over schemes locally of finite type over
`S`, and a Noetherian `S` need not be locally of finite type over `Spec ℤ` (`Spec ℚ` is not), so
openness of versality over `S` cannot be read off openness of versality over `Spec ℤ` by base
change; the proof of Stacks 0D3X applies Artin's criterion Stacks 0CXU over the locally Noetherian
base `S` itself.

None of these declarations is registered: they are the plumbing by which Stacks 0D59 follows from
Stacks 0D3X, and Stacks 0D59 is to be registered on their instances at the proved Stacks 0D3X.

## Main results

* `AlgebraicGeometry.isNoetherian_integerBase`: `Spec ℤ` is a Noetherian scheme.
* `AlgebraicGeometry.curves_openVersality_specZ_of_noetherianProperFlat`: the first clause of
  Stacks 0D59 from openness of versality for `Spaces'_{fp, flat, proper}` over every Noetherian
  base.
* `AlgebraicGeometry.curves_openVersality_of_noetherianProperFlat`: the second clause of
  Stacks 0D59 from the same input.

## References

* [Stacks Project, Tag 0D59](https://stacks.math.columbia.edu/tag/0D59)
* [Stacks Project, Tag 0D3X](https://stacks.math.columbia.edu/tag/0D3X)
* [Stacks Project, Tag 07XQ](https://stacks.math.columbia.edu/tag/07XQ)
-/

@[expose] public section

attribute [local implicit_reducible] AlgebraicGeometry.curvesProjectionOver

open CategoryTheory Deformation.Artin

universe u

namespace AlgebraicGeometry

/-- `Spec ℤ`, in the form `AlgebraicGeometry.integerBase` the stack of curves is defined over, is a
Noetherian scheme. -/
theorem isNoetherian_integerBase : IsNoetherian integerBase.{u} :=
  have : IsNoetherianRing (ULift.{u} ℤ) :=
    isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
  inferInstance

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- **The first clause of Stacks 0D59 from the Noetherian clause of Stacks 0D3X.** If the stack
`Spaces'_{fp, flat, proper}` satisfies openness of versality over every Noetherian base scheme,
then the stack of curves satisfies openness of versality over `Spec ℤ`: `Spec ℤ` is Noetherian. -/
theorem curves_openVersality_specZ_of_noetherianProperFlat
    (hPF : ∀ (S : Scheme.{u}) [IsNoetherian S] (hS : B.Contains S),
      OpenVersalityOf (cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion)) :
    OpenVersalityOf (curvesProjectionOver B hZ ⋙ Over.post B.inclusion) :=
  have := isNoetherian_integerBase.{u}
  curves_openVersality_specZ_of_properFlatSpaces B hZ (hPF integerBase hZ)

/-- **The second clause of Stacks 0D59 from the Noetherian clause of Stacks 0D3X.** If the stack
`Spaces'_{fp, flat, proper}` satisfies openness of versality over every Noetherian base scheme,
then so does the base change of the stack of curves to any Noetherian scheme `S`. -/
theorem curves_openVersality_of_noetherianProperFlat
    (hPF : ∀ (S : Scheme.{u}) [IsNoetherian S] (hS : B.Contains S),
      OpenVersalityOf (cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion))
    (S : Scheme.{u}) [IsNoetherian S] (hS : B.Contains S) :
    OpenVersalityOf
      (CostructuredArrow.pre (AlgebraicGeometry.curvesProjection B hZ)
        (𝟭 B.Schemes) (B.obj hS) ⋙ Over.post B.inclusion) :=
  curves_openVersality_of_properFlatSpaces B hZ S hS (hPF S hS)

end AlgebraicGeometry

end
