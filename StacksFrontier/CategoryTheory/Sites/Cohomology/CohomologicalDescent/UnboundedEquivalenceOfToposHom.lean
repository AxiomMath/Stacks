module

import StacksCore.Tactic.StacksAttribute
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.CohomologicalDescent.AdjunctionUnboundedEquivalence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CohomologicalDescent.BoundedBelowEquivalenceOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CohomologicalDescent.UnboundedEquivalence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.PullbackInvertsQuasiIsoOfToposHom

/-!
# Derived pullback along a morphism of ringed topoi as an equivalence of unbounded derived
categories

Stacks 0D7V for an arbitrary flat morphism of ringed topoi
`f : (Sh(C), 𝒪) ⟶ (Sh(C'), 𝒪')`, given as an `AlgebraicGeometry.RingedToposHom`. Let
`𝒜 ⊂ Mod(𝒪)` and `𝒜' ⊂ Mod(𝒪')` be weak Serre subcategories such that `f^*` induces an
equivalence `𝒜' ⟶ 𝒜`, `ℱ' ⟶ Rf_*f^*ℱ'` is an isomorphism for every `ℱ'` of `𝒜'`, and
`C, 𝒪, 𝒜` and `C', 𝒪', 𝒜'` both satisfy the standing hypothesis of Tag 0D6R. Then
`Lf^* : D_{𝒜'}(𝒪') ⟶ D_𝒜(𝒪)` is an equivalence with quasi-inverse `Rf_*`.

This is
`Stacks.Cohomology.CohomologicalDescent.equivalenceUnboundedAdjunctionUnboundedEquivalence` at the
derived adjunction `Lf^* ⊣ Rf_*` of Stacks 07A6. As for a morphism presented by sites, the
Olsson--Laszlo hypotheses are carried as loose data on the two sites.

## Main definitions

* `Stacks.Cohomology.CohomologicalDescent.OfRingedToposHom.derivedPullbackEquivalenceUnbounded`:
  the equivalence, with `derivedPullbackEquivalenceUnbounded_functor` and
  `derivedPullbackEquivalenceUnbounded_inverse` identifying its two functors with the restrictions
  of `Lf^*` and of `Rf_*`.

## References

* [Stacks Project, Tag 0D7V](https://stacks.math.columbia.edu/tag/0D7V)
* [Stacks Project, Tag 0D6R](https://stacks.math.columbia.edu/tag/0D6R)
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
  [EnoughInjectives (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O)))]
  [EnoughInjectives (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O)))]
  (f : RingedToposHom X Y)
  (hf : f.IsFlat)
  (A : ObjectProperty
    (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))))
  (A' : ObjectProperty
    (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))))
  [A.IsWeakSerreClass] [A'.IsWeakSerreClass]
  (hA : ∀ M, A' M → A (f.toModulesHom.pullbackModules.obj M))

include hf hA in
omit
  [EnoughInjectives (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O)))]
  [EnoughInjectives (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O)))]
  [A'.IsWeakSerreClass] in
/-- **Stacks 0D7V for a morphism of ringed topoi**, the assertion that derived pullback
restricts: for a flat `f` with `f^*𝒜' ⊂ 𝒜`, `Lf^*` carries `D_{𝒜'}(𝒪')` into `D_𝒜(𝒪)`. -/
theorem derivedCategoryB_derivedPullback_obj
    (K : DerivedCategory
      (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))))
    (hK : DerivedCategoryB.derivedCategoryB A' K) :
    DerivedCategoryB.derivedCategoryB A ((DerivedPullbackOfToposHom.derivedPullback f).obj K) :=
  have := preservesFiniteLimits_pullbackModules f hf
  have := RingedToposHom.pullbackModules_preservesFiniteColimits f
  derivedCategoryB_obj_of_iso_adjunctionUnboundedEquivalence f.toModulesHom.pullbackModules
    (derivedPullbackNatIso f) A A' hA K hK

variable
  (hEquiv :
    (A.lift (A'.ι ⋙ f.toModulesHom.pullbackModules) (fun N ↦ hA N.obj N.property)).IsEquivalence)
  (hUnit : ∀ M, A' M → IsIso ((derivedPullbackPushforwardAdjunctionOfToposHom f).unit.app
    ((DerivedCategory.singleFunctor
      (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))) 0).obj M)))
  (B : Set X.C)
  (basisCover : ∀ U : X.C, ∃ 𝒰 : PreZeroHypercover.{w} U,
    𝒰.sieve₀ ∈ X.J U ∧ ∀ i, B (𝒰.X i))
  (degreeBound : ∀ V : X.C, B V → ℤ)
  (coverings : ∀ V : X.C, B V → Stacks.Cohomology.CofinalCoveringSystem X.J V)
  (vanishing : ∀ (V : X.C) (hV : B V) (𝒰 : PreZeroHypercover.{w} V),
    (coverings V hV).cov 𝒰 → ∀ (i : 𝒰.I₀) (p : ℕ), degreeBound V hV < (p : ℤ) →
      ∀ F : SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O)), A F →
        IsZero (Stacks.Cohomology.moduleCohomology
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O)) (𝒰.X i) p F))
  (B' : Set Y.C)
  (basisCover' : ∀ U : Y.C, ∃ 𝒰 : PreZeroHypercover.{w} U,
    𝒰.sieve₀ ∈ Y.J U ∧ ∀ i, B' (𝒰.X i))
  (degreeBound' : ∀ V : Y.C, B' V → ℤ)
  (coverings' : ∀ V : Y.C, B' V → Stacks.Cohomology.CofinalCoveringSystem Y.J V)
  (vanishing' : ∀ (V : Y.C) (hV : B' V) (𝒰 : PreZeroHypercover.{w} V),
    (coverings' V hV).cov 𝒰 → ∀ (i : 𝒰.I₀) (p : ℕ), degreeBound' V hV < (p : ℤ) →
      ∀ F : SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O)), A' F →
        IsZero (Stacks.Cohomology.moduleCohomology
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O)) (𝒰.X i) p F))

include hf hA hEquiv hUnit basisCover vanishing basisCover' vanishing' in
/-- **Stacks 0D7V for a morphism of ringed topoi**, the assertion that derived pushforward
restricts: under the hypotheses of the source, `Rf_*` carries `D_𝒜(𝒪)` into `D_{𝒜'}(𝒪')`. -/
theorem derivedCategoryB_derivedPushforward_obj :
    ∀ K : DerivedCategory
        (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))),
      DerivedCategoryB.derivedCategoryB A K →
        DerivedCategoryB.derivedCategoryB A' ((derivedPushforward (X := X) (Y := Y) f).obj K) :=
  fun K hK ↦
  have := preservesFiniteLimits_pullbackModules f hf
  have := RingedToposHom.pullbackModules_preservesFiniteColimits f
  have := DerivedPullbackOfToposHom.derivedPullback_isTriangulated_general f
  derivedCategoryB_rightAdjoint_obj_of_iso_adjunctionUnboundedEquivalence
    f.toModulesHom.pullbackModules
    (derivedPullbackPushforwardAdjunctionOfToposHom f) (derivedPullbackNatIso f) A A' hA hEquiv
    hUnit B basisCover degreeBound coverings vanishing
    B' basisCover' degreeBound' coverings' vanishing' K hK

/-- **Stacks 0D7V for a morphism of ringed topoi.** Let `f` be a flat morphism of ringed topoi and
let `𝒜 ⊂ Mod(𝒪)`, `𝒜' ⊂ Mod(𝒪')` be weak Serre subcategories such that `f^*` induces an
equivalence `𝒜' ⟶ 𝒜` and the unit `ℱ' ⟶ Rf_*f^*ℱ'` is invertible for every `ℱ'` of `𝒜'`, and
assume that `C, 𝒪, 𝒜` and `C', 𝒪', 𝒜'` both satisfy the standing hypothesis of Tag 0D6R. Then
the derived pullback is an **equivalence** `D_{𝒜'}(𝒪') ≌ D_𝒜(𝒪)`. -/
def derivedPullbackEquivalenceUnbounded :
    (DerivedCategoryB.derivedCategoryB A').FullSubcategory ≌
      (DerivedCategoryB.derivedCategoryB A).FullSubcategory :=
  haveI := preservesFiniteLimits_pullbackModules f hf
  haveI := RingedToposHom.pullbackModules_preservesFiniteColimits f
  haveI := DerivedPullbackOfToposHom.derivedPullback_isTriangulated_general f
  equivalenceUnboundedAdjunctionUnboundedEquivalence f.toModulesHom.pullbackModules
    (derivedPullbackPushforwardAdjunctionOfToposHom f)
    (derivedPullbackNatIso f) A A' hA hEquiv hUnit
    B basisCover degreeBound coverings vanishing
    B' basisCover' degreeBound' coverings' vanishing'

/-- **Stacks 0D7V for a morphism of ringed topoi**, the identification of the forward functor of
the equivalence with the restriction of the derived pullback. -/
theorem derivedPullbackEquivalenceUnbounded_functor :
    (derivedPullbackEquivalenceUnbounded f hf A A' hA hEquiv hUnit
      B basisCover degreeBound coverings vanishing
      B' basisCover' degreeBound' coverings' vanishing').functor =
      (DerivedCategoryB.derivedCategoryB A).lift
        ((DerivedCategoryB.derivedCategoryB A').ι ⋙ DerivedPullbackOfToposHom.derivedPullback f)
        (fun K ↦ derivedCategoryB_derivedPullback_obj f hf A A' hA K.obj K.property) :=
  rfl

/-- **Stacks 0D7V for a morphism of ringed topoi**, the identification of the quasi-inverse of
the equivalence with the restriction of the derived pushforward. -/
theorem derivedPullbackEquivalenceUnbounded_inverse :
    (derivedPullbackEquivalenceUnbounded f hf A A' hA hEquiv hUnit
      B basisCover degreeBound coverings vanishing
      B' basisCover' degreeBound' coverings' vanishing').inverse =
      (DerivedCategoryB.derivedCategoryB A').lift
        ((DerivedCategoryB.derivedCategoryB A).ι ⋙ derivedPushforward (X := X) (Y := Y) f)
        (fun K ↦ derivedCategoryB_derivedPushforward_obj f hf A A' hA hEquiv hUnit
          B basisCover degreeBound coverings vanishing
          B' basisCover' degreeBound' coverings' vanishing' K.obj K.property) :=
  rfl

end Stacks.Cohomology.CohomologicalDescent.OfRingedToposHom

end
