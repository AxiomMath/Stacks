module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStack
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.ChangeOfBigSites
public import StacksFrontier.CategoryTheory.Limits.Finite.Nonempty
public import StacksFrontier.CategoryTheory.Sites.Stack.Functoriality.PullbackFibred

/-!
# The quotient prestack of a groupoid in algebraic spaces after enlarging the big site

Let `B` be a big fppf site contained in a larger one `B'`, let `S` be a scheme of `B`, and let
`G` be a groupoid in algebraic spaces over an algebraic space over `S` for `B` (Stacks 043W).
Write `u : (Sch/S)_fppf ⥤ (Sch'/S)_fppf` for the localized inclusion of Stacks 022K and `f` for
the morphism of sites it determines.

This file constructs `f⁻¹[U/R]`, the pullback of the quotient stack `[U/R]` of Stacks 044Q along
the morphism of sites, as a category over the enlarged localized big fppf site: following
Stacks 04WJ, it is the stackification (Stacks 02ZN) of `u_p [U/R]`, which is a fibred category by
Stacks 04WG. It is the right-hand side of Stacks 04WX.

## Main results

* `AlgebraicGeometry.hasNonemptyFiniteLimits_bigFppfOver`: a localized big fppf site has all
  nonempty finite limits, in the form `CategoryTheory.Limits.HasNonemptyFiniteLimits`.
* `AlgebraicGeometry.inclusionOver_preservesLimitsOfShape_of_nonempty`: the localized inclusion
  preserves limits of every nonempty finite shape.
* `AlgebraicGeometry.Stack.isFibered_pullbackProj_quotientPrestack` and
  `AlgebraicGeometry.Stack.isFibered_pullbackProj_quotientStack`: **Stacks 04WG** for the
  pointwise groupoid fibration, and for the quotient stack itself, along the localized inclusion
  of big fppf sites.
* `AlgebraicGeometry.Stack.isStack_pullbackQuotientStack`: `f⁻¹[U/R]` is a stack for the fppf
  topology of the enlarged localized big site.

## Main definitions

* `AlgebraicGeometry.Stack.pullbackQuotientStack`: **`f⁻¹[U/R]`**, the right-hand side of
  Stacks 04WX.
* `AlgebraicGeometry.Stack.toPullbackQuotientStack`: the canonical 1-morphism
  `u_p [U/R] ⥤ f⁻¹[U/R]` exhibiting it as the stackification.

## References

* [Stacks Project, Tag 022K](https://stacks.math.columbia.edu/tag/022K)
* [Stacks Project, Tag 043W](https://stacks.math.columbia.edu/tag/043W)
* [Stacks Project, Tag 044Q](https://stacks.math.columbia.edu/tag/044Q)
* [Stacks Project, Tag 04WF](https://stacks.math.columbia.edu/tag/04WF)
* [Stacks Project, Tag 04WG](https://stacks.math.columbia.edu/tag/04WG)
* [Stacks Project, Tag 04WJ](https://stacks.math.columbia.edu/tag/04WJ)
* [Stacks Project, Tag 04WR](https://stacks.math.columbia.edu/tag/04WR)
* [Stacks Project, Tag 04WX](https://stacks.math.columbia.edu/tag/04WX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

variable {B B' : BigFppfSite.{u}} (h : IsContained (τ := .fppf) B B') (S : Scheme.{u})
  (hS : B.Contains S)

/-- A localized big fppf site has all limits of nonempty finite shape. -/
theorem hasNonemptyFiniteLimits_bigFppfOver :
    HasNonemptyFiniteLimits (BigFppfOver B S hS) :=
  have : HasFiniteLimits B.Schemes := hasFiniteLimits_siteCategory (τ := .fppf) B
  ⟨fun _ => inferInstance⟩

/-- The localized inclusion of a big fppf site into a larger one preserves limits of every
nonempty finite shape. -/
theorem inclusionOver_preservesLimitsOfShape_of_nonempty :
    ∀ (J : Type) [SmallCategory J] [FinCategory J] [Nonempty J],
      PreservesLimitsOfShape J (inclusionOver h S hS) :=
  fun J _ _ _ =>
    (inclusionOver_preservesFiniteLimits (τ := .fppf) B B' h S hS).preservesFiniteLimits J

namespace Stack

variable {Bs : AlgebraicSpaces B S hS}

/-- **Stacks 04WG** for the pointwise groupoid fibration of a groupoid in algebraic spaces along
the localized inclusion of big fppf sites: `u_p [U/_p R]` is a fibred category over the enlarged
localized big fppf site, where `[U/_p R]` is the pointwise groupoid fibration whose
stackification is the quotient stack `[U/R]` of Stacks 044Q. -/
theorem isFibered_pullbackProj_quotientPrestack (G : GroupoidInAlgebraicSpaces B S hS Bs) :
    (Comma.pullbackProj (quotientPrestack G).p (inclusionOver h S hS)).IsFibered :=
  have : HasNonemptyFiniteLimits (BigFppfOver B S hS) :=
    hasNonemptyFiniteLimits_bigFppfOver S hS
  Comma.isFibered_pullbackProj _ _ (inclusionOver_preservesLimitsOfShape_of_nonempty h S hS)

/-- **Stacks 04WG** for the quotient *stack* of a groupoid in algebraic spaces along the
localized inclusion of big fppf sites: `u_p [U/R]` is a fibred category over the enlarged
localized big fppf site. -/
theorem isFibered_pullbackProj_quotientStack (G : GroupoidInAlgebraicSpaces B S hS Bs) :
    (Comma.pullbackProj (quotientStack G).p (inclusionOver h S hS)).IsFibered :=
  have : HasNonemptyFiniteLimits (BigFppfOver B S hS) :=
    hasNonemptyFiniteLimits_bigFppfOver S hS
  Comma.isFibered_pullbackProj _ _ (inclusionOver_preservesLimitsOfShape_of_nonempty h S hS)

/-- The structure functor of `u_p [U/R]`, with its codomain written as the enlarged localized big
fppf site rather than as the `CategoryTheory.Over` category that site unfolds to. -/
noncomputable def pullbackQuotientStackProj (G : GroupoidInAlgebraicSpaces B S hS Bs) :
    Comma.pullbackLocalization (quotientStack G).p (inclusionOver h S hS) ⥤
      BigFppfOver B' S (largerContains h hS) :=
  Comma.pullbackProj (quotientStack G).p (inclusionOver h S hS)

/-- **Stacks 04WG**, restated for `AlgebraicGeometry.Stack.pullbackQuotientStackProj`. -/
instance isFibered_pullbackQuotientStackProj (G : GroupoidInAlgebraicSpaces B S hS Bs) :
    (pullbackQuotientStackProj h S hS G).IsFibered :=
  isFibered_pullbackProj_quotientStack h S hS G

/-- **`f⁻¹[U/R]`, the pullback of the quotient stack along the morphism of sites `f`**: the
stackification (`CategoryTheory.Functor.stageThreeProj`, Stacks 02ZN) of `u_p [U/R]` over the
enlarged localized big fppf site, as in Stacks 04WJ. -/
noncomputable def pullbackQuotientStack (G : GroupoidInAlgebraicSpaces B S hS Bs) :
    BasedCategory (BigFppfOver B' S (largerContains h hS)) :=
  BasedCategory.ofFunctor ((pullbackQuotientStackProj h S hS G).stageThreeProj
    (BigFppfOver.topology B' S (largerContains h hS)))

/-- `f⁻¹[U/R]` satisfies descent for the fppf topology of the enlarged localized big site. -/
theorem isStack_pullbackQuotientStack (G : GroupoidInAlgebraicSpaces B S hS Bs) :
    (pullbackQuotientStack h S hS G).p.IsStack
      (BigFppfOver.topology B' S (largerContains h hS)) :=
  Functor.isStack_stageThreeProj.{u, u, u + 1, u + 1} _ _

/-- The canonical 1-morphism `u_p [U/R] ⥤ f⁻¹[U/R]` into the stackification. -/
noncomputable def toPullbackQuotientStack (G : GroupoidInAlgebraicSpaces B S hS Bs) :
    Comma.pullbackLocalization (quotientStack G).p (inclusionOver h S hS) ⥤
      (pullbackQuotientStack h S hS G).obj :=
  (pullbackQuotientStackProj h S hS G).toStageThree
    (BigFppfOver.topology B' S (largerContains h hS))

/-- The canonical 1-morphism into `f⁻¹[U/R]` is *strictly* over the enlarged localized big fppf
site. -/
theorem isFibredOneMorphism_toPullbackQuotientStack
    (G : GroupoidInAlgebraicSpaces B S hS Bs) :
    (pullbackQuotientStackProj h S hS G).IsFibredOneMorphism
      (pullbackQuotientStack h S hS G).p (toPullbackQuotientStack h S hS G) :=
  Functor.isFibredOneMorphism_toStageThree _ _

end Stack

end AlgebraicGeometry

end
