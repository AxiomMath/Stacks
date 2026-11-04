module

public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CategoryHomology.EvaluationToDerivedColimit
public import StacksCore.Tactic.StacksAttribute

/-!
# Derived lower shriek along a functor of chaotic sites

Let `u : C' ⥤ C` be a functor between small categories carrying their chaotic topologies and
let `B` be a ring. The inverse image of the induced morphism of ringed topoi is restriction
along `u`, so lower shriek is its left adjoint, the left Kan extension along `u.op`. On a
chaotic site a module over the constant sheaf of rings is a diagram of `B`-modules, and such
diagrams have enough projectives, so lower shriek has a total left derived functor and that
functor is left adjoint to the degreewise derived inverse image.

## Main definitions

* `Stacks.ChaoticSite.lowerShriekAlongAFunctor`: lower shriek `g_!`, the left Kan extension
  along `u.op`, with `Stacks.ChaoticSite.lowerShriekAlongAFunctorAdjunction` exhibiting it as
  left adjoint to restriction.
* `Stacks.ChaoticSite.derivedLowerShriekAlongAFunctor`: the total left derived functor `Lg_!`.

## Main results

* `Stacks.ChaoticSite.derivedLowerShriekAlongAFunctorAdjunction`: `Lg_! ⊣ g^{-1}`, with no
  acyclicity hypothesis.
* `Stacks.ChaoticSite.derivedLowerShriekAlongAFunctor_isTriangulated`: it is an exact functor
  of triangulated categories.

## Implementation notes

The two sites and the module sections live in one universe, as in
`StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedLowerShriek`: the projective
resolutions of diagrams of modules that supply enough projectives are indexed by the site, so
their universe is that of the modules.

## References

* [Stacks Project, Tag 07AC](https://stacks.math.columbia.edu/tag/07AC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.ChaoticSite

universe u w

attribute [local instance] HasDerivedCategory.standard

section Definitions

variable (C C' : Type u) [SmallCategory C] [SmallCategory C']
  (u : C' ⥤ C) (B : Type w) [Ring B]

/-- Restriction of diagrams of `B`-modules along a functor of chaotic sites: the inverse image
`g^{-1}` of the induced morphism of ringed topoi. -/
def inverseImageAlongAFunctor :
    (Cᵒᵖ ⥤ ModuleCat.{max u w} B) ⥤ (C'ᵒᵖ ⥤ ModuleCat.{max u w} B) :=
  (Functor.whiskeringLeft _ _ _).obj u.op

/-- Lower shriek `g_!` along a functor of chaotic sites: the left Kan extension of diagrams of
`B`-modules along `u.op`. -/
def lowerShriekAlongAFunctor :
    (C'ᵒᵖ ⥤ ModuleCat.{max u w} B) ⥤ (Cᵒᵖ ⥤ ModuleCat.{max u w} B) :=
  u.op.lan

/-- **Lower shriek is left adjoint to inverse image.** -/
def lowerShriekAlongAFunctorAdjunction :
    lowerShriekAlongAFunctor C C' u B ⊣ inverseImageAlongAFunctor C C' u B :=
  u.op.lanAdjunction _

/-- Inverse image is additive, being computed pointwise. -/
instance inverseImageAlongAFunctor_additive :
    (inverseImageAlongAFunctor C C' u B).Additive :=
  inferInstanceAs ((Functor.whiskeringLeft _ _ _).obj u.op).Additive

/-- Inverse image preserves limits, being a right adjoint. -/
instance inverseImageAlongAFunctor_preservesLimits :
    Limits.PreservesLimitsOfSize.{max u w, max u w} (inverseImageAlongAFunctor C C' u B) :=
  (u.op.lanAdjunction (ModuleCat.{max u w} B)).rightAdjoint_preservesLimits

/-- Inverse image preserves finite limits. -/
instance inverseImageAlongAFunctor_preservesFiniteLimits :
    Limits.PreservesFiniteLimits (inverseImageAlongAFunctor C C' u B) :=
  have : Limits.PreservesLimitsOfSize.{0, 0} (inverseImageAlongAFunctor C C' u B) :=
    Limits.preservesLimitsOfSize_shrink _
  inferInstance

/-- Inverse image preserves colimits, being computed pointwise. -/
instance inverseImageAlongAFunctor_preservesColimits :
    Limits.PreservesColimitsOfSize.{max u w, max u w} (inverseImageAlongAFunctor C C' u B) :=
  inferInstanceAs
    (Limits.PreservesColimitsOfSize.{max u w, max u w}
      ((Functor.whiskeringLeft _ _ _).obj u.op))

/-- Inverse image preserves finite colimits. -/
instance inverseImageAlongAFunctor_preservesFiniteColimits :
    Limits.PreservesFiniteColimits (inverseImageAlongAFunctor C C' u B) :=
  have : Limits.PreservesColimitsOfSize.{0, 0} (inverseImageAlongAFunctor C C' u B) :=
    Limits.preservesColimitsOfSize_shrink _
  inferInstance

/-- Lower shriek is a left adjoint. -/
instance lowerShriekAlongAFunctor_isLeftAdjoint :
    (lowerShriekAlongAFunctor C C' u B).IsLeftAdjoint :=
  (lowerShriekAlongAFunctorAdjunction C C' u B).isLeftAdjoint

/-- Lower shriek is additive, being a left adjoint between abelian categories. -/
instance lowerShriekAlongAFunctor_additive :
    (lowerShriekAlongAFunctor C C' u B).Additive :=
  have := Limits.preservesBinaryBiproducts_of_preservesBinaryCoproducts
    (lowerShriekAlongAFunctor C C' u B)
  Functor.additive_of_preservesBinaryBiproducts _

end Definitions

section Derived

variable {C C' : Type u} [SmallCategory C] [SmallCategory C']
  (u : C' ⥤ C) (B : Type w) [Ring B]

/-- **Lower shriek along a functor of chaotic sites has a total left derived functor.** -/
theorem lowerShriekAlongAFunctor_hasPointwiseLeftDerivedFunctor :
    ((lowerShriekAlongAFunctor C C' u B).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
      (HomotopyCategory.quasiIso (C'ᵒᵖ ⥤ ModuleCat.{max u w} B) (ComplexShape.up ℤ)) :=
  CategoryHomology.hasPointwiseLeftDerivedFunctor_of_enoughProjectives
    (lowerShriekAlongAFunctor C C' u B)

/-- **Stacks 07AC for chaotic sites.** The total left derived functor `Lg_!` of lower shriek
along a functor of chaotic sites, with coefficients a constant sheaf of rings. -/
def derivedLowerShriekAlongAFunctor :
    DerivedCategory (C'ᵒᵖ ⥤ ModuleCat.{max u w} B) ⥤
      DerivedCategory (Cᵒᵖ ⥤ ModuleCat.{max u w} B) :=
  have := lowerShriekAlongAFunctor_hasPointwiseLeftDerivedFunctor u B
  ((lowerShriekAlongAFunctor C C' u B).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).totalLeftDerived DerivedCategory.Qh
      (HomotopyCategory.quasiIso (C'ᵒᵖ ⥤ ModuleCat.{max u w} B) (ComplexShape.up ℤ))

/-- The comparison transformation exhibiting `derivedLowerShriekAlongAFunctor` as a left
derived functor of lower shriek. -/
def derivedLowerShriekAlongAFunctorCounit :
    DerivedCategory.Qh ⋙ derivedLowerShriekAlongAFunctor u B ⟶
      (lowerShriekAlongAFunctor C C' u B).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh :=
  have := lowerShriekAlongAFunctor_hasPointwiseLeftDerivedFunctor u B
  ((lowerShriekAlongAFunctor C C' u B).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).totalLeftDerivedCounit DerivedCategory.Qh
      (HomotopyCategory.quasiIso (C'ᵒᵖ ⥤ ModuleCat.{max u w} B) (ComplexShape.up ℤ))

/-- The comparison transformation does exhibit `derivedLowerShriekAlongAFunctor` as a left
derived functor of lower shriek. -/
theorem derivedLowerShriekAlongAFunctor_isLeftDerivedFunctor :
    (derivedLowerShriekAlongAFunctor u B).IsLeftDerivedFunctor
      (derivedLowerShriekAlongAFunctorCounit u B)
      (HomotopyCategory.quasiIso (C'ᵒᵖ ⥤ ModuleCat.{max u w} B) (ComplexShape.up ℤ)) := by
  have := lowerShriekAlongAFunctor_hasPointwiseLeftDerivedFunctor u B
  dsimp [derivedLowerShriekAlongAFunctor, derivedLowerShriekAlongAFunctorCounit]
  infer_instance

/-- **Stacks 07AC for chaotic sites, with no acyclicity hypothesis.** Derived lower shriek
along a functor of chaotic sites is left adjoint to the derived inverse image. -/
def derivedLowerShriekAlongAFunctorAdjunction :
    derivedLowerShriekAlongAFunctor u B ⊣
      (inverseImageAlongAFunctor C C' u B).mapDerivedCategory :=
  have := lowerShriekAlongAFunctor_hasPointwiseLeftDerivedFunctor u B
  have := derivedLowerShriekAlongAFunctor_isLeftDerivedFunctor u B
  CategoryHomology.derivedAdjunctionOfEnoughProjectives
    (lowerShriekAlongAFunctorAdjunction C C' u B)
    (derivedLowerShriekAlongAFunctor u B) (derivedLowerShriekAlongAFunctorCounit u B)

/-- Derived lower shriek along a functor of chaotic sites commutes with the shift, being a left
adjoint of a functor that does. -/
instance derivedLowerShriekAlongAFunctor_commShift :
    (derivedLowerShriekAlongAFunctor u B).CommShift ℤ :=
  (derivedLowerShriekAlongAFunctorAdjunction u B).leftAdjointCommShift ℤ

/-- **Derived lower shriek along a functor of chaotic sites is exact.** -/
instance derivedLowerShriekAlongAFunctor_isTriangulated :
    (derivedLowerShriekAlongAFunctor u B).IsTriangulated :=
  have : (derivedLowerShriekAlongAFunctorAdjunction u B).CommShift ℤ :=
    (derivedLowerShriekAlongAFunctorAdjunction u B).commShift_of_rightAdjoint ℤ
  (derivedLowerShriekAlongAFunctorAdjunction u B).isTriangulated_leftAdjoint

end Derived

end Stacks.ChaoticSite

end
