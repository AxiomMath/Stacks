module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Generator.Presheaf
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.PuncturedSpectrumCompletedSections
public import StacksFrontier.Homology.CompositeCollapse
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.MittagLefflerAcyclic

/-!
# The higher derived limits of a Mittag--Leffler inverse system vanish

The category `ℕᵒᵖ ⥤ Ab` of inverse systems of abelian groups is a Grothendieck abelian category
and therefore has enough injectives, so Mathlib's `ℕ`-indexed right derived functors
`R ⁿ lim` of the inverse-limit functor are defined. This file records those instances and uses
them to put the acyclicity of a Mittag--Leffler system into the `ℕ`-indexed form: for a
Mittag--Leffler inverse system `A`,

`R ⁿ lim (A) = 0` for every `n > 0`.

## Main results

* `Rlim.enoughInjectives_invSystemAb`: the category of inverse systems of abelian groups has
  enough injectives.
* `Rlim.isZero_rightDerived_lim_of_isMittagLeffler`: **`R ⁿ lim (A) = 0` for `n > 0` and `A`
  Mittag--Leffler**, in Mathlib's `ℕ`-indexed `CategoryTheory.Functor.rightDerived`.
* `Rlim.acyclic_lim_of_isMittagLeffler`: the same, packaged as
  `Stacks.RightDerivedComp.acyclic lim A`, which is the hypothesis that
  `Stacks.RightDerivedComp.objIsoOfAcyclicImage` consumes.

## Implementation notes

The acyclicity itself is `Rlim.rightAcyclic_lim_of_isMittagLeffler`, which is [Stacks, Tag 05T8]
for the class of Mittag--Leffler systems, and the passage between the two indexings is
`Stacks.RightDerivedComp.rightAcyclic_iff_acyclic`, which is part (2) of [Stacks, Tag 015C].

The statements of the two main results mention no derived category and no chosen right derived
functor: `CategoryTheory.Functor.rightDerived` is computed from an injective resolution. For the
*unbounded* derived functor of `lim`, see `Rlim.lim_hasRightDerivedFunctor_and_computations`
([Stacks, Tag 07KW]).

## References

* [Stacks Project, Tag 05T8](https://stacks.math.columbia.edu/tag/05T8)
* [Stacks Project, Tag 015C](https://stacks.math.columbia.edu/tag/015C)
* [Stacks Project, Tag 079B](https://stacks.math.columbia.edu/tag/079B)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Rlim

universe u

/-- **Filtered colimits of inverse systems of abelian groups are exact.**  Colimits in a functor
category are computed pointwise, so this reduces to the exactness of filtered colimits
of abelian groups. -/
instance ab5OfSize_invSystemAb : AB5OfSize.{u, u} (Rlim.InvSystemAb.{u}) where
  ofShape _ _ _ := inferInstance

/-- **The category of inverse systems of abelian groups is a Grothendieck abelian category**
([Stacks, Tag 079B]).  It is locally small, has exact filtered colimits by
`Rlim.ab5OfSize_invSystemAb`, and has a separator because a presheaf category over a category
with a separator does. -/
instance isGrothendieckAbelian_invSystemAb :
    IsGrothendieckAbelian.{u} (Rlim.InvSystemAb.{u}) where

/-- **The category of inverse systems of abelian groups has enough injectives**, by Grothendieck's
theorem applied to `Rlim.isGrothendieckAbelian_invSystemAb`.  This is what makes Mathlib's
`ℕ`-indexed right derived functors of the inverse-limit functor defined. -/
instance enoughInjectives_invSystemAb : EnoughInjectives (Rlim.InvSystemAb.{u}) :=
  IsGrothendieckAbelian.enoughInjectives.{u}

/- The inverse-limit functor on inverse systems of abelian groups is additive, so that its right
derived functors are defined: `Stacks.Algebraization.limAdditiveOnInvSystemAb`, a local instance
where it is declared, is made an instance here because the statements below mention the right
derived functors of `lim`. -/
attribute [instance] Stacks.Algebraization.limAdditiveOnInvSystemAb

section Vanishing

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- **The higher derived limits of a Mittag--Leffler inverse system of abelian groups vanish**:
`R ⁿ lim (A) = 0` for every `n > 0`, in Mathlib's `ℕ`-indexed
`CategoryTheory.Functor.rightDerived`.

The statement mentions no derived category and no choice of right derived functor. -/
theorem isZero_rightDerived_lim_of_isMittagLeffler (A : Rlim.InvSystemAb.{u})
    (hA : (A ⋙ forget Ab.{u}).IsMittagLeffler) (n : ℕ) (hn : 0 < n) :
    IsZero (((lim : Rlim.InvSystemAb.{u} ⥤ Ab.{u}).rightDerived n).obj A) :=
  (Stacks.RightDerivedComp.rightAcyclic_iff_acyclic
    (lim : Rlim.InvSystemAb.{u} ⥤ Ab.{u}) A).1
      (rightAcyclic_lim_of_isMittagLeffler A hA) n hn

end Vanishing

/-- **A Mittag--Leffler inverse system of abelian groups is `lim`-acyclic** in the sense of
`Stacks.RightDerivedComp.acyclic`. -/
theorem acyclic_lim_of_isMittagLeffler (A : Rlim.InvSystemAb.{u})
    (hA : (A ⋙ forget Ab.{u}).IsMittagLeffler) :
    Stacks.RightDerivedComp.acyclic (lim : Rlim.InvSystemAb.{u} ⥤ Ab.{u}) A :=
  isZero_rightDerived_lim_of_isMittagLeffler A hA

end Rlim

end
