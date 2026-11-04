module

import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CohomologicalDescent.AdjunctionBoundedBelowEquivalence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CohomologicalDescent.BoundedBelowDescentOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CohomologicalDescent.BoundedBelowEquivalence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedLimit.RightAdjointBoundedCohomologicalDimension
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.PullbackInvertsQuasiIsoOfToposHom

/-!
# Derived pullback along a morphism of ringed topoi as an equivalence of bounded below derived
categories

Stacks 0D7U for an arbitrary flat morphism of ringed topoi
`f : (Sh(C), 𝒪) ⟶ (Sh(C'), 𝒪')`, given as an `AlgebraicGeometry.RingedToposHom`. Let
`𝒜 ⊂ Mod(𝒪)` and `𝒜' ⊂ Mod(𝒪')` be weak Serre subcategories such that `f^*` induces an
equivalence `𝒜' ⟶ 𝒜` and `ℱ' ⟶ Rf_*f^*ℱ'` is an isomorphism for every `ℱ'` of `𝒜'`. Then
`Lf^* : D⁺_{𝒜'}(𝒪') ⟶ D⁺_𝒜(𝒪)` is an equivalence with quasi-inverse `Rf_*`.

This is
`Stacks.Cohomology.CohomologicalDescent.equivalenceBoundedBelowAdjunctionBoundedBelowEquivalence`
at the derived adjunction `Lf^* ⊣ Rf_*` of Stacks 07A6, whose left adjoint is identified with the
functor induced by the exact functor `f^*` in
`Stacks.Cohomology.CohomologicalDescent.OfRingedToposHom.derivedPullbackNatIso`.

## Main definitions

* `Stacks.Cohomology.CohomologicalDescent.OfRingedToposHom.derivedPullbackEquivalence`: the
  equivalence, with `derivedPullbackEquivalence_functor` and `derivedPullbackEquivalence_inverse`
  identifying its two functors with the restrictions of `Lf^*` and of `Rf_*`.

## References

* [Stacks Project, Tag 0D7U](https://stacks.math.columbia.edu/tag/0D7U)
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
  (hf : f.IsFlat)
  (A : ObjectProperty
    (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))))
  (A' : ObjectProperty
    (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))))
  [A.IsWeakSerreClass] [A'.IsWeakSerreClass]
  (hA : ∀ M, A' M → A (f.toModulesHom.pullbackModules.obj M))

include hf hA in
omit [A'.IsWeakSerreClass] in
/-- **Stacks 0D7U for a morphism of ringed topoi**, the assertion that derived pullback
restricts: for a flat `f` with `f^*𝒜' ⊂ 𝒜`, `Lf^*` carries `D⁺_{𝒜'}(𝒪')` into `D⁺_𝒜(𝒪)`. -/
theorem derivedCategoryBPlus_derivedPullback_obj
    (K : DerivedCategory
      (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))))
    (hK : DerivedCategoryB.derivedCategoryBPlus A' K) :
    DerivedCategoryB.derivedCategoryBPlus A
      ((DerivedPullbackOfToposHom.derivedPullback f).obj K) :=
  have := preservesFiniteLimits_pullbackModules f hf
  have := RingedToposHom.pullbackModules_preservesFiniteColimits f
  derivedCategoryBPlus_obj_of_iso_adjunctionBoundedBelowEquivalence f.toModulesHom.pullbackModules
    (derivedPullbackNatIso f) A A' hA K hK

variable
  (hEquiv : (A.lift (A'.ι ⋙ f.toModulesHom.pullbackModules)
    (fun N ↦ hA N.obj N.property)).IsEquivalence)
  (hUnit : ∀ M, A' M → IsIso ((derivedPullbackPushforwardAdjunctionOfToposHom f).unit.app
    ((DerivedCategory.singleFunctor
      (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))) 0).obj M)))

include hf hA hEquiv hUnit in
omit [A.IsWeakSerreClass] in
/-- **Stacks 0D7U for a morphism of ringed topoi**, the assertion that derived pushforward
restricts: under the hypotheses of the source, `Rf_*` carries `D⁺_𝒜(𝒪)` into `D⁺_{𝒜'}(𝒪')`. -/
theorem derivedCategoryBPlus_derivedPushforward_obj
    (K : DerivedCategory
      (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))))
    (hK : DerivedCategoryB.derivedCategoryBPlus A K) :
    DerivedCategoryB.derivedCategoryBPlus A'
      ((derivedPushforward (X := X) (Y := Y) f).obj K) :=
  have := preservesFiniteLimits_pullbackModules f hf
  have := RingedToposHom.pullbackModules_preservesFiniteColimits f
  have := DerivedPullbackOfToposHom.derivedPullback_isTriangulated_general f
  derivedCategoryBPlus_rightAdjoint_obj_of_iso_adjunctionBoundedBelowEquivalence
    f.toModulesHom.pullbackModules
    (derivedPullbackPushforwardAdjunctionOfToposHom f) (derivedPullbackNatIso f) A A' hA hEquiv
    hUnit K hK

/-- **Stacks 0D7U for a morphism of ringed topoi.** For a flat morphism of ringed topoi `f` and
weak Serre subcategories `𝒜 ⊂ Mod(𝒪)`, `𝒜' ⊂ Mod(𝒪')` such that `f^*` induces an equivalence
`𝒜' ⟶ 𝒜` and the unit `ℱ' ⟶ Rf_*f^*ℱ'` is invertible for every `ℱ'` of `𝒜'`, the derived pullback
is an **equivalence** `D⁺_{𝒜'}(𝒪') ≌ D⁺_𝒜(𝒪)`. -/
def derivedPullbackEquivalence :
    (DerivedCategoryB.derivedCategoryBPlus A').FullSubcategory ≌
      (DerivedCategoryB.derivedCategoryBPlus A).FullSubcategory :=
  haveI := preservesFiniteLimits_pullbackModules f hf
  haveI := RingedToposHom.pullbackModules_preservesFiniteColimits f
  haveI := DerivedPullbackOfToposHom.derivedPullback_isTriangulated_general f
  equivalenceBoundedBelowAdjunctionBoundedBelowEquivalence f.toModulesHom.pullbackModules
    (derivedPullbackPushforwardAdjunctionOfToposHom f)
    (derivedPullbackNatIso f) A A' hA hEquiv hUnit

/-- **Stacks 0D7U for a morphism of ringed topoi**, the identification of the forward functor of
the equivalence with the restriction of the derived pullback. -/
theorem derivedPullbackEquivalence_functor :
    (derivedPullbackEquivalence f hf A A' hA hEquiv hUnit).functor =
      (DerivedCategoryB.derivedCategoryBPlus A).lift
        ((DerivedCategoryB.derivedCategoryBPlus A').ι ⋙
          DerivedPullbackOfToposHom.derivedPullback f)
        (fun K ↦ derivedCategoryBPlus_derivedPullback_obj f hf A A' hA K.obj K.property) :=
  rfl

/-- **Stacks 0D7U for a morphism of ringed topoi**, the identification of the quasi-inverse of
the equivalence with the restriction of the derived pushforward. -/
theorem derivedPullbackEquivalence_inverse :
    (derivedPullbackEquivalence f hf A A' hA hEquiv hUnit).inverse =
      (DerivedCategoryB.derivedCategoryBPlus A').lift
        ((DerivedCategoryB.derivedCategoryBPlus A).ι ⋙ derivedPushforward (X := X) (Y := Y) f)
        (fun K ↦ derivedCategoryBPlus_derivedPushforward_obj f hf A A' hA hEquiv hUnit
          K.obj K.property) :=
  rfl

end Stacks.Cohomology.CohomologicalDescent.OfRingedToposHom

end
