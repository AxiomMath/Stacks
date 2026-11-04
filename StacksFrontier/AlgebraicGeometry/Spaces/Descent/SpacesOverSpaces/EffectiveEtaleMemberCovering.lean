module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.SpacesOverSpaces.DescentDataQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.SpacesOverSpaces.EffectiveOneMemberCovering

/-!
# Every descent datum along a covering with a surjective étale member is effective

Let `{X i ⟶ T}` be an fppf covering of algebraic spaces one member of which is surjective and
étale.  `StacksFrontier.AlgebraicGeometry.Spaces.Descent.SpacesOverSpaces.EffectiveOneMemberCovering`
proves, with no grant, that the descent datum `fibreDescentData F` of a sheaf `F` over `T` with
algebraic-space fibres is then effective.  Essential surjectivity of the fibre descent functor,
`AlgebraicGeometry.Space.Descent.essSurj_fibreDescentFunctor` of
`StacksFrontier.AlgebraicGeometry.Spaces.Descent.SpacesOverSpaces.DescentDataQuotient`, presents
every descent datum in that form, so every descent datum relative to such a covering is
effective, and its quotient sheaf is an algebraic space.

## Main results

* `AlgebraicGeometry.Space.Descent.isEffective_of_isEtale`: **every** descent datum relative
  to such a covering is effective, not only those of the form `fibreDescentData F`, and
  `AlgebraicGeometry.Space.Descent.isAlgebraicSpace_descentQuotient_of_isEtale`: the quotient
  sheaf of a descent datum relative to such a covering is an algebraic space. Together these
  are a constructor of an algebraic space from glueing data.

## Implementation notes

An étale covering is an fppf covering, so this is a special case of Stacks 0ADV; the
hypotheses that make it unconditional, surjectivity and étaleness of the chosen member, are
visible in the binders as `hsurj` and `hetale`. Stacks 0ADV itself, which drops them, is not
proved here and is not used.

## References

* [Stacks Project, Tag 0ADT](https://stacks.math.columbia.edu/tag/0ADT)
* [Stacks Project, Tag 0ADV](https://stacks.math.columbia.edu/tag/0ADV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space.Descent

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

variable {ι : Type v} {X : ι → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

variable (f : ∀ i, X i ⟶ T) (hT : IsAlgebraicSpace B S hS T)
    (hX : ∀ i, IsAlgebraicSpace B S hS (X i))

/-- **Every descent datum relative to an fppf covering one member of which is surjective and
étale is effective**, with no grant.

This is `AlgebraicGeometry.Space.Descent.isEffective_fibreDescentData_of_isEtale` for an
arbitrary descent datum rather than one of the form
`AlgebraicGeometry.Space.Descent.fibreDescentData F`: essential surjectivity of the fibre
descent functor, `AlgebraicGeometry.Space.Descent.essSurj_fibreDescentFunctor`, presents
every descent datum as the descent datum of its quotient sheaf
`AlgebraicGeometry.Space.Descent.descentQuotient`, and effectivity transports along that
identification.

An étale covering is an fppf covering, so this is a special case of Stacks 0ADV; the
hypotheses that make it unconditional, surjectivity and étaleness of the chosen member, are
visible in the binders as `hsurj` and `hetale`. Stacks 0ADV itself, which drops them, is not
proved here and is not used. -/
theorem isEffective_of_isEtale (hcov : IsFppfCovering B S hS X f) (D : DescentData f hT hX)
    (i : ι) (hsurj : IsSurjective B S hS (f i)) (hetale : IsEtale B S hS (f i)) :
    DescentData.IsEffective D :=
  CategoryTheory.Functor.essImage.ofIso (descentQuotientIso f hT hX D).symm
    (isEffective_fibreDescentData_of_isEtale f hT hX hcov
      (descentQuotient f hT hX D) i hsurj hetale)

/-- **An algebraic space from a descent datum, with no grant.** For an fppf covering of
algebraic spaces one member of which is surjective and étale, the quotient sheaf of a descent
datum relative to the covering is an algebraic space, and the `i`-th component of the datum is
its fibre product with the `i`-th member of the covering, by
`AlgebraicGeometry.Space.Descent.isPullback_toDescentQuotient`.

Together with `AlgebraicGeometry.Space.Descent.isEffective_of_isEtale` this is a constructor
of an algebraic space from glueing data, whose only hypotheses beyond the datum itself are
that the family is an fppf covering of algebraic spaces and that one of its members is
surjective and étale. -/
theorem isAlgebraicSpace_descentQuotient_of_isEtale (hcov : IsFppfCovering B S hS X f)
    (D : DescentData f hT hX) (i : ι) (hsurj : IsSurjective B S hS (f i))
    (hetale : IsEtale B S hS (f i)) :
    IsAlgebraicSpace B S hS (descentQuotient f hT hX D).obj.left :=
  isAlgebraicSpace_descentQuotient f hT hX hcov D
    (isEffective_of_isEtale f hT hX hcov D i hsurj hetale)

end AlgebraicGeometry.Space.Descent

end
