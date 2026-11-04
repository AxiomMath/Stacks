module

public import StacksFrontier.AlgebraicGeometry.Descent.SmallAffineRingedTopos
public import StacksFrontier.CategoryTheory.Sites.DenseSubsite.NatIsoTransport

/-!
# From the affine étale charts to all étale charts, for sheaf-valued functors

[Stacks Project, Tag 04HR] says that the small affine étale site of a scheme is a dense subsite of
its small étale site; in this development that is
`AlgebraicGeometry.SmallAffineEtale.inclusion_isSpecialCocontinuous`, whose dense-subsite half is
the standing instance `AlgebraicGeometry.SmallAffineEtale.inclusion_isDenseSubsite`.

This file records the consequence that the existence half of [Stacks Project, Tag 04I6] uses: a
natural isomorphism between two functors whose *values* are sheaves on the small étale site of `S`
may be given on the affine charts alone.

Note which direction this is.  It is **not** that a functor *indexed* by the étale charts is
determined by its restriction to the affine ones — that is false without a descent argument, since
the inclusion of the affine subsite is not essentially surjective.  It is that a functor *valued*
in sheaves on the étale site is determined by its composite with restriction to the affine subsite,
restriction being fully faithful.  See the module documentation of
`StacksFrontier/CategoryTheory/Sites/DenseSubsite/NatIsoTransport.lean`.

## Main definitions

* `AlgebraicGeometry.SmallAffineEtale.restriction` — restriction of sheaves from the small étale
  site to the small affine étale site.

## Main results

* `AlgebraicGeometry.SmallAffineEtale.natIsoOfRestriction` — a natural isomorphism of
  sheaf-valued functors, given on the affine étale charts, extends to all of `S_étale`.
* `AlgebraicGeometry.SmallAffineEtale.natTrans_injective_of_restriction` — a natural
  transformation of sheaf-valued functors is determined by its restriction.

## References

* [Stacks Project, Tag 04HR](https://stacks.math.columbia.edu/tag/04HR)
* [Stacks Project, Tag 04I6](https://stacks.math.columbia.edu/tag/04I6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v' u' u

namespace AlgebraicGeometry.SmallAffineEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (A : Type u') [Category.{v'} A]

/-- **Restriction of sheaves from the small étale site of `S` to its small affine étale site.**
This is `CategoryTheory.Functor.sheafPushforwardContinuous` of the inclusion of the affine
subsite, which is continuous because the inclusion is a dense subsite by [Stacks Project,
Tag 04HR]. -/
abbrev restriction :
    Sheaf (SmallEtale.topology B S hS) A ⥤ Sheaf (topology B S hS) A :=
  (inclusion B S hS).sheafPushforwardContinuous A (topology B S hS)
    (SmallEtale.topology B S hS)

variable {E : Type*} [Category* E]
  {F₁ F₂ : E ⥤ Sheaf (SmallEtale.topology B S hS) A}

/-- **A natural isomorphism of sheaf-valued functors given on the affine étale charts extends to
all étale charts.**  This is
`CategoryTheory.Functor.IsDenseSubsite.natIsoOfRestriction` at the inclusion of the small affine
étale site, [Stacks Project, Tag 04HR].

It is the transport the existence half of [Stacks Project, Tag 04I6] needs: the comparison of the
direct images `g_*` and `f_{small,*}`, both of which are functors valued in sheaves on `S_étale`,
is produced from the affine charts of `S`, where a standard presentation is available. -/
def natIsoOfRestriction (i : F₁ ⋙ restriction B S hS A ≅ F₂ ⋙ restriction B S hS A) :
    F₁ ≅ F₂ :=
  Functor.IsDenseSubsite.natIsoOfRestriction (topology B S hS)
    (SmallEtale.topology B S hS) (inclusion B S hS) A i

/-- **A natural transformation of sheaf-valued functors is determined by its restriction to the
affine étale charts.** -/
theorem natTrans_injective_of_restriction {α β : F₁ ⟶ F₂}
    (h : Functor.whiskerRight α (restriction B S hS A) =
      Functor.whiskerRight β (restriction B S hS A)) :
    α = β :=
  Functor.IsDenseSubsite.natTrans_injective_of_restriction (topology B S hS)
    (SmallEtale.topology B S hS) (inclusion B S hS) A h

end AlgebraicGeometry.SmallAffineEtale

end
