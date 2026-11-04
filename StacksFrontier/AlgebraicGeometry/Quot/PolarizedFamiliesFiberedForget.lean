module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedFamiliesForget
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedStackUnconditional
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Comp
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.FactorizationEquivalence
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.SliceProduct

/-!
# Polarized families over the families of algebraic spaces they polarize (Stacks 0D3Z)

Stacks 0D3Z asserts that the category `Polarized` of polarized families of Stacks 0D1M is fibred
in groupoids over the category `Spaces'_{fp, flat, proper}` of finitely presented, flat and proper
families of algebraic spaces of Stacks 0D1E, through the functor
`AlgebraicGeometry.forgetPolarization` of Stacks 0D3Y that forgets the polarization.

The lift of a family `Y ⟶ T` of algebraic spaces along `forgetPolarization` is the base change of
the polarized family along `T ⟶ S`, whose total space is the fibre product of *schemes*. The
source makes this a lift by saying that `X ×_S S'` "is a scheme again"; formally it is only
*isomorphic* to the given family of algebraic spaces, over the identity of the base scheme, which
is weaker than the equality of objects that `CategoryTheory.Functor.IsFiberedInGroupoids` demands.
The statement is therefore recorded for the vertical iso-comma category `XPrime` of Stacks 06N7:
an object of `AlgebraicGeometry.PolarizedSpaces` is a polarized family together with a family of
algebraic spaces and a vertical isomorphism between the two, and
`AlgebraicGeometry.polarizedSpacesEquiv` identifies it with `Polarized` by an equivalence over the
big fppf site which carries the second projection to `AlgebraicGeometry.forgetPolarization`.

## Main definitions

* `AlgebraicGeometry.polarizedFamiliesProperFlatProjection`: the projection of the finitely
  presented, flat and proper families of algebraic spaces to the big fppf site itself, rather than
  to its slice over the terminal scheme.
* `AlgebraicGeometry.PolarizedSpaces`: polarized families with the family of algebraic spaces
  they polarize carried as data.
* `AlgebraicGeometry.polarizedSpacesForget` and `AlgebraicGeometry.toPolarizedSpaces`: the second
  projection and the comparison functor from `Polarized`.

## Main results

* `AlgebraicGeometry.polarizedSpacesForget_isFiberedInGroupoids`: **Stacks 0D3Z**, polarized
  families are fibred in groupoids over the finitely presented, flat and proper families of
  algebraic spaces.
* `AlgebraicGeometry.polarizedSpacesEquiv`,
  `AlgebraicGeometry.polarizedSpaces_isEquivalenceOver` and
  `AlgebraicGeometry.toPolarizedSpaces_comp_polarizedSpacesForget`: the equivalence over the big
  fppf site identifying `AlgebraicGeometry.PolarizedSpaces` with `Polarized`, under which the
  second projection becomes `AlgebraicGeometry.forgetPolarization`.

## References

* [Stacks Project, Tag 0D3Z](https://stacks.math.columbia.edu/tag/0D3Z)
* [Stacks Project, Tag 06N7](https://stacks.math.columbia.edu/tag/06N7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor.IsFiberedInGroupoids.Factorization

namespace AlgebraicGeometry

universe u

variable (B : BigFppfSite.{u})

/-! ### The families of algebraic spaces as a category over the site -/

/-- The projection taking a finitely presented, flat and proper family of algebraic spaces over
the terminal scheme to its base scheme in the big fppf site. -/
abbrev polarizedFamiliesProperFlatProjection :
    CartesianProperFlatSpaces B integerBase B.contains_integerBase ⥤ B.Schemes :=
  cartesianProperFlatProjection B integerBase B.contains_integerBase ⋙
    BigFppfOver.forget B integerBase B.contains_integerBase

/-- **Stacks 0D1E** over the big fppf site itself: finitely presented, flat and proper families
of algebraic spaces over the terminal scheme are fibred in groupoids over the site, because the
slice over the terminal scheme is fibred in groupoids over the site and composites of functors
fibred in groupoids are fibred in groupoids (Stacks 09WW). -/
theorem polarizedFamiliesProperFlatProjection_isFiberedInGroupoids :
    (polarizedFamiliesProperFlatProjection B).IsFiberedInGroupoids :=
  Functor.IsFiberedInGroupoids.comp _ _
    (cartesianProperFlatProjection_isFiberedInGroupoids B integerBase B.contains_integerBase)
    (Functor.IsFiberedInGroupoids.over_forget _)

/-- Forgetting the polarization keeps the base scheme, so `AlgebraicGeometry.forgetPolarization`
is a 1-morphism over the big fppf site. -/
theorem forgetPolarization_comp_polarizedFamiliesProperFlatProjection :
    forgetPolarization B ⋙ polarizedFamiliesProperFlatProjection B = polarizedProjection B := rfl

/-! ### Polarized families with their family of algebraic spaces -/

/-- A polarized family together with the family of algebraic spaces it polarizes: an object is a
polarized family `x`, a finitely presented, flat and proper family `y` of algebraic spaces over
the terminal scheme, and an isomorphism between the family underlying `x` and `y` lying over an
identity of the big fppf site. -/
abbrev PolarizedSpaces := XPrime (polarizedFamiliesProperFlatProjection B) (forgetPolarization B)

/-- The projection of `AlgebraicGeometry.PolarizedSpaces` to the family of algebraic spaces. -/
abbrev polarizedSpacesForget :
    PolarizedSpaces B ⥤ CartesianProperFlatSpaces B integerBase B.contains_integerBase :=
  XPrime.toRight (polarizedFamiliesProperFlatProjection B) (forgetPolarization B)

/-- The projection of `AlgebraicGeometry.PolarizedSpaces` to the big fppf site, recording the
base scheme of the polarized family. -/
abbrev polarizedSpacesProjection : PolarizedSpaces B ⥤ B.Schemes :=
  XPrime.structureFunctor (polarizedProjection B) (polarizedFamiliesProperFlatProjection B)
    (forgetPolarization B)

/-- The comparison functor, sending a polarized family to itself together with the family of
algebraic spaces it polarizes and the identity isomorphism. -/
abbrev toPolarizedSpaces : PolarizedFamily B ⥤ PolarizedSpaces B :=
  XPrime.fromLeft (polarizedFamiliesProperFlatProjection B) (forgetPolarization B)

/-- **Stacks 0D3Z.** Polarized families are fibred in groupoids over the finitely presented, flat
and proper families of algebraic spaces of Stacks 0D1E.

Condition (a) of Stacks 003S is base change of the polarized family along the base scheme of the
given family of algebraic spaces, and condition (b) holds because the base morphism the fill-in
must lie over is forced by the two comparison isomorphisms, so the fill-in is the one
`AlgebraicGeometry.polarizedProjection_uniqueLift` provides over the site. -/
@[stacks 0D3Z "fibred in groupoids over the stack of finitely presented, flat and proper families"]
theorem polarizedSpacesForget_isFiberedInGroupoids :
    (polarizedSpacesForget B).IsFiberedInGroupoids :=
  XPrime.toRight_isFiberedInGroupoids (polarizedProjection B)
    (polarizedFamiliesProperFlatProjection B) (forgetPolarization B)
    polarizedProjection_isFiberedInGroupoids_unconditional
    (polarizedFamiliesProperFlatProjection_isFiberedInGroupoids B)
    (forgetPolarization_comp_polarizedFamiliesProperFlatProjection B)

/-- The equivalence of categories identifying `AlgebraicGeometry.PolarizedSpaces` with the
category of polarized families. -/
def polarizedSpacesEquiv : PolarizedFamily B ≌ PolarizedSpaces B :=
  XPrime.equivalence (polarizedFamiliesProperFlatProjection B) (forgetPolarization B)

/-- The comparison functor is an equivalence over the big fppf site: its quasi-inverse commutes
strictly with the two projections to the site, and the unit and counit isomorphisms lie over
identities. -/
def polarizedSpaces_isEquivalenceOver :
    Functor.IsEquivalenceOver (polarizedProjection B) (polarizedSpacesProjection B)
      (toPolarizedSpaces B) :=
  XPrime.isEquivalenceOver (polarizedProjection B) (polarizedFamiliesProperFlatProjection B)
    (forgetPolarization B)

/-- **Stacks 0D3Z.** The comparison equivalence carries the projection of
`AlgebraicGeometry.PolarizedSpaces` to the family of algebraic spaces back to the forgetful
functor of Stacks 0D3Y, so `AlgebraicGeometry.polarizedSpacesForget_isFiberedInGroupoids` is the
assertion of the tag for `AlgebraicGeometry.forgetPolarization`. -/
@[stacks 0D3Z "identification of the replacement category with the polarized families"]
theorem toPolarizedSpaces_comp_polarizedSpacesForget :
    toPolarizedSpaces B ⋙ polarizedSpacesForget B = forgetPolarization B :=
  XPrime.fromLeft_comp_toRight (polarizedFamiliesProperFlatProjection B) (forgetPolarization B)

/-- The comparison functor commutes with the projections to the big fppf site. -/
theorem toPolarizedSpaces_comp_polarizedSpacesProjection :
    toPolarizedSpaces B ⋙ polarizedSpacesProjection B = polarizedProjection B :=
  XPrime.fromLeft_comp_structureFunctor (polarizedProjection B)
    (polarizedFamiliesProperFlatProjection B) (forgetPolarization B)

/-- The projection of `AlgebraicGeometry.PolarizedSpaces` to the family of algebraic spaces is a
1-morphism over the big fppf site. -/
theorem polarizedSpacesForget_comp_polarizedFamiliesProperFlatProjection :
    polarizedSpacesForget B ⋙ polarizedFamiliesProperFlatProjection B =
      polarizedSpacesProjection B :=
  XPrime.toRight_comp_eq (polarizedProjection B) (polarizedFamiliesProperFlatProjection B)
    (forgetPolarization B) (forgetPolarization_comp_polarizedFamiliesProperFlatProjection B)

/-- `AlgebraicGeometry.PolarizedSpaces` is fibred in groupoids over the big fppf site, which is
the assertion of Stacks 0D3Z for the big fppf site transported along
`AlgebraicGeometry.polarizedSpacesEquiv`. -/
theorem polarizedSpacesProjection_isFiberedInGroupoids :
    (polarizedSpacesProjection B).IsFiberedInGroupoids :=
  XPrime.structureFunctor_isFiberedInGroupoids (polarizedProjection B)
    (polarizedFamiliesProperFlatProjection B) (forgetPolarization B)
    polarizedProjection_isFiberedInGroupoids_unconditional
    (polarizedFamiliesProperFlatProjection_isFiberedInGroupoids B)
    (forgetPolarization_comp_polarizedFamiliesProperFlatProjection B)

end AlgebraicGeometry

end
