module

import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CohomologicalDescent.AdjunctionBoundedBelowDescent
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CohomologicalDescent.BoundedBelowDescent
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.BoundednessOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.PullbackInvertsQuasiIsoOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Modules.FlatMorphisms.RingedTopoi
public import StacksFrontier.CategoryTheory.Sites.RingedLocalization.FlatPullbackExact
public import StacksFrontier.CategoryTheory.Sites.RingedLocalization.RingedToposHomModulesComparison
public import StacksFrontier.CategoryTheory.Sites.RingedLocalization.RingedToposHomModulesComparisonPullback

/-!
# Cohomological descent for bounded below complexes along a morphism of ringed topoi

Stacks 0D7T and 0D7S for an arbitrary flat morphism of ringed topoi
`f : (Sh(C), O_X) ⟶ (Sh(D), O_Y)`, given as an `AlgebraicGeometry.RingedToposHom`, with the
derived adjunction `Lf^* ⊣ Rf_*` of Stacks 07A6
(`Stacks.Cohomology.DerivedPushforward.derivedPullbackPushforwardAdjunctionOfToposHom`). For a
bounded below object `K`:

* if `H^q(K) ⟶ Rf_*Lf^*H^q(K)` is an isomorphism for every `q`, then so is `K ⟶ Rf_*Lf^*K`;
* if `Lf^*Rf_*H^q(K) ⟶ H^q(K)` is an isomorphism for every `q`, then so is `Lf^*Rf_*K ⟶ K`.

These are `isIso_unit_app_of_isIso_homology_adjunctionBoundedBelowDescent` and
`isIso_counit_app_of_isIso_homology_adjunctionBoundedBelowDescent` (in the namespace
`Stacks.Cohomology.CohomologicalDescent`) at this adjunction. Flatness of `f` makes the pullback of
modules exact (Stacks 04JC, `Stacks.Sheaves.RingedToposModules.pullbackModules_exact_of_isFlatMap`,
read through
`AlgebraicGeometry.RingedToposHom.pullbackModules_eq_pullbackModules_toRingedToposModulesHom`), so
`Lf^*` is the functor induced by `f^*` and preserves boundedness below; `Rf_*` preserves it being
right adjoint to a functor preserving boundedness above.

## Main results

* `Stacks.Cohomology.CohomologicalDescent.OfRingedToposHom.preservesFiniteLimits_pullbackModules`:
  pullback of modules along a flat morphism of ringed topoi is left exact.
* `Stacks.Cohomology.CohomologicalDescent.OfRingedToposHom.derivedPullbackNatIso`: along a morphism
  whose pullback of modules is exact, `Lf^*` is the functor induced by `f^*`.
* `Stacks.Cohomology.CohomologicalDescent.OfRingedToposHom.isIso_derivedUnit_app_of_isIso_homology`
  (Stacks 0D7T) and `isIso_derivedCounit_app_of_isIso_homology` (Stacks 0D7S).

## References

* [Stacks Project, Tag 0D7T](https://stacks.math.columbia.edu/tag/0D7T)
* [Stacks Project, Tag 0D7S](https://stacks.math.columbia.edu/tag/0D7S)
* [Stacks Project, Tag 04JC](https://stacks.math.columbia.edu/tag/04JC)
* [Stacks Project, Tag 07A6](https://stacks.math.columbia.edu/tag/07A6)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPushforward

namespace Stacks.Cohomology.CohomologicalDescent.OfRingedToposHom

universe w

attribute [local instance] HasDerivedCategory.standard

variable {X Y : RingedTopos.{w, w, w}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (f : RingedToposHom X Y)

omit [HasSheafify Y.J AddCommGrpCat] [Y.J.WEqualsLocallyBijective AddCommGrpCat] in
/-- **Stacks 04JC for the pullback of modules of a morphism of ringed topoi**: along a flat
morphism the pullback of sheaves of modules is left exact. -/
theorem preservesFiniteLimits_pullbackModules
    (hf : f.IsFlat) :
    PreservesFiniteLimits f.toModulesHom.pullbackModules := by
  rw [RingedToposHom.pullbackModules_eq_pullbackModules_toRingedToposModulesHom]
  exact ((exactFunctor_iff _).mp
    (Stacks.Sheaves.RingedToposModules.pullbackModules_exact_of_isFlatMap f hf)).1

section Exact

variable [PreservesFiniteLimits f.toModulesHom.pullbackModules]

/-- **For a morphism along which pullback of modules is exact, the derived pullback is the
functor induced on derived categories by the pullback of modules**, naturally: both are left
derived functors of degreewise pullback followed by localization, the second because an exact
functor inverts the quasi-isomorphisms. -/
def derivedPullbackNatIso :
    DerivedPullbackOfToposHom.derivedPullback f ≅
      (letI := RingedToposHom.pullbackModules_preservesFiniteColimits f
       f.toModulesHom.pullbackModules.mapDerivedCategory) :=
  letI := RingedToposHom.pullbackModules_preservesFiniteColimits f
  haveI : f.toModulesHom.pullbackModules.mapDerivedCategory.IsLeftDerivedFunctor
      f.toModulesHom.pullbackModules.mapDerivedCategoryFactorsh.hom
      (DerivedPullbackOfToposHom.quasiIsoTarget (Y := Y)) :=
    Functor.isLeftDerivedFunctor_of_inverts
      (DerivedPullbackOfToposHom.quasiIsoTarget (Y := Y)) _
      f.toModulesHom.pullbackModules.mapDerivedCategoryFactorsh
  Functor.leftDerivedNatIso (DerivedPullbackOfToposHom.derivedPullback f)
    f.toModulesHom.pullbackModules.mapDerivedCategory
    (DerivedPullbackOfToposHom.derivedPullbackComparison f)
    f.toModulesHom.pullbackModules.mapDerivedCategoryFactorsh.hom
    (DerivedPullbackOfToposHom.quasiIsoTarget (Y := Y)) (Iso.refl _)

/-- `Lf^*` preserves boundedness below along a morphism whose pullback of modules is exact. -/
theorem isGE_derivedPullback_obj
    (K : DerivedCategory (SheafOfModules.{w}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O)))) (n : ℤ)
    (hK : K.IsGE n) : ((DerivedPullbackOfToposHom.derivedPullback f).obj K).IsGE n :=
  let := RingedToposHom.pullbackModules_preservesFiniteColimits f
  isGE_obj_of_iso_adjunctionBoundedBelowDescent f.toModulesHom.pullbackModules
    (derivedPullbackNatIso f) K n hK

end Exact

variable (hf : f.IsFlat)

include hf

/-- **Stacks 0D7T for a morphism of ringed topoi.** Let `f` be a flat morphism of ringed topoi
and let `K` be a bounded below object of `D(O_Y)`. If the unit `H^q(K) ⟶ Rf_*Lf^*H^q(K)` is an
isomorphism for every `q`, with each cohomology object placed in degree zero, then the unit
`K ⟶ Rf_*Lf^*K` is an isomorphism. -/
theorem isIso_derivedUnit_app_of_isIso_homology
    (K : DerivedCategory (SheafOfModules.{w}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))))
    (hK : DerivedCategory.TStructure.t.plus K)
    (hH : ∀ q : ℤ, IsIso ((derivedPullbackPushforwardAdjunctionOfToposHom f).unit.app
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))) 0).obj
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{w}
            ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))) q).obj K)))) :
    IsIso ((derivedPullbackPushforwardAdjunctionOfToposHom f).unit.app K) :=
  have := preservesFiniteLimits_pullbackModules f hf
  have := DerivedPullbackOfToposHom.derivedPullback_isTriangulated_general f
  isIso_unit_app_of_isIso_homology_adjunctionBoundedBelowDescent
    (derivedPullbackPushforwardAdjunctionOfToposHom f)
    (isGE_derivedPullback_obj f)
    f.isGE_derivedPushforward_obj_unconditional_boundednessOfToposHom K hK hH

/-- **Stacks 0D7S for a morphism of ringed topoi.** Let `f` be a flat morphism of ringed topoi
and let `K` be a bounded below object of `D(O_X)`. If the counit `Lf^*Rf_*H^q(K) ⟶ H^q(K)` is an
isomorphism for every `q`, with each cohomology object placed in degree zero, then the counit
`Lf^*Rf_*K ⟶ K` is an isomorphism. -/
theorem isIso_derivedCounit_app_of_isIso_homology
    (K : DerivedCategory (SheafOfModules.{w}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))))
    (hK : DerivedCategory.TStructure.t.plus K)
    (hH : ∀ q : ℤ, IsIso ((derivedPullbackPushforwardAdjunctionOfToposHom f).counit.app
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))) 0).obj
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{w}
            ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))) q).obj K)))) :
    IsIso ((derivedPullbackPushforwardAdjunctionOfToposHom f).counit.app K) :=
  have := preservesFiniteLimits_pullbackModules f hf
  have := DerivedPullbackOfToposHom.derivedPullback_isTriangulated_general f
  isIso_counit_app_of_isIso_homology_adjunctionBoundedBelowDescent
    (derivedPullbackPushforwardAdjunctionOfToposHom f)
    (isGE_derivedPullback_obj f)
    f.isGE_derivedPushforward_obj_unconditional_boundednessOfToposHom K hK hH

end Stacks.Cohomology.CohomologicalDescent.OfRingedToposHom

end
