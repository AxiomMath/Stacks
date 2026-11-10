module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.HomComplexResolution
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringObjectDerivedPushforwardFreeYoneda

/-!
# Stacks 0D8L from the quasi-isomorphism on the base site, in chain form

The module
`StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringObjectDerivedPushforwardFreeYoneda`
reduces Stacks 0D8L for a hypercovering to the statement that the extension by zero `a_!` carries
the augmentation of the resolution of Stacks 0D78 of `a^{-1}ℤ_V^♯` to a quasi-isomorphism, stated
on `CategoryTheory.SimplicialSiteSituation.Augmentation.resolutionCochainAugmentation`: the
`ℤ`-indexed cochain form of the resolution, with the `ℕ`-indexed chain complex placed in
non-positive degrees and `a_!` applied after that placement.

This module states the same reductions with the hypothesis on
`CategoryTheory.SimplicialSiteSituation.Augmentation.resolutionChainAugmentation`, the
`ℕ`-indexed chain complex itself, which like the complex of Stacks 01GE is
`AlgebraicTopology.alternatingFaceMapComplex` of a simplicial object. The two hypotheses are
related by `CochainComplex.quasiIso_map_resolutionCochainAugmentation`: an additive functor
carries the cochain form of a resolution to a quasi-isomorphism as soon as it carries the
resolution itself to one.

## Main results

All names are in the namespace `CategoryTheory.SimplicialSemiRepresentable`.

* `inverseImageComputesDerivedPushforward_of_quasiIso_freeYoneda_chain`: the simplicial-site
  situation statement.
* `isIso_derivedAugmentationUnitOver_of_quasiIso_freeYoneda_chain` and
  `isIso_derivedAugmentationUnitOver_app_of_isHypercovering_of_quasiIso_freeYoneda_chain`:
  Stacks 0D8L over an object and for a hypercovering, under the chain hypothesis.

## References

* [Stacks Project, Tag 0D8L](https://stacks.math.columbia.edu/tag/0D8L)
* [Stacks Project, Tag 0D8G](https://stacks.math.columbia.edu/tag/0D8G)
* [Stacks Project, Tag 0D78](https://stacks.math.columbia.edu/tag/0D78)
* [Stacks Project, Tag 01GE](https://stacks.math.columbia.edu/tag/01GE)
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.SimplicialSiteSituation
open Stacks.Cohomology.CohomologyPresheaf

universe u

namespace CategoryTheory.SimplicialSemiRepresentable

attribute [local instance] HasDerivedCategory.standard additive_abelianTotalPushforwardOver
  additive_abelianTotalInverseImageOver preservesFiniteColimits_abelianTotalInverseImageOver
  hasPointwiseRightDerivedFunctor_homotopyAbelianTotalPushforwardOver
  hasRightDerivedFunctor_homotopyAbelianTotalPushforwardOver

section Situation

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  (K : SimplicialObject (FormalCoproduct.{u} C)) [J.toCoverage.HasPullbacks]

/-- **`InverseImageComputesDerivedPushforward` for a simplicial semi-representable object, from
the `ℕ`-indexed chain quasi-isomorphism on the base site.** If, for every object `V` of `C`, the
extension by zero `a_!` carries the augmentation of the resolution of Stacks 0D78 of
`a^{-1}ℤ_V^♯` to a quasi-isomorphism, then the inverse image computes the derived pushforward.
This is `inverseImageComputesDerivedPushforward_of_quasiIso_freeYoneda` with the hypothesis on
the resolution itself rather than on its cochain form; Stacks 0D88 is discharged in that
statement. -/
theorem inverseImageComputesDerivedPushforward_of_quasiIso_freeYoneda_chain
    (h : ∀ V : C, QuasiIso
      (((augmentationAbelianLowerShriek J K).mapHomologicalComplex (ComplexShape.down ℕ)).map
        (Augmentation.resolutionChainAugmentation (situation J K) (Cat.of C) J
          (situationAugmentation J K) (freeYonedaSheaf J V)))) :
    Augmentation.InverseImageComputesDerivedPushforward (situation J K) (Cat.of C) J
      (situationAugmentation J K) :=
  inverseImageComputesDerivedPushforward_of_quasiIso_freeYoneda J K fun V =>
    CochainComplex.quasiIso_map_resolutionCochainAugmentation _ _ _
      (augmentationAbelianLowerShriek J K) (h V)

end Situation

section Over

variable {C : Type u} [SmallCategory C] [HasPullbacks C] (J : GrothendieckTopology C) (X : C)
  (K : SimplicialObject (FormalCoproduct.{u} (Over X)))

/-- **Stacks 0D8L over an object, from the `ℕ`-indexed chain quasi-isomorphism on the base
site.** This is `isIso_derivedAugmentationUnitOver_of_quasiIso_freeYoneda` with the second
hypothesis stated on the resolution of Stacks 0D78 itself rather than on its cochain form. -/
theorem isIso_derivedAugmentationUnitOver_of_quasiIso_freeYoneda_chain
    (hunit : IsIso (abelianTotalAdjunctionOver J X K).unit)
    (h : ∀ V : Over X, QuasiIso
      (((augmentationAbelianLowerShriek (J.over X) K).mapHomologicalComplex
          (ComplexShape.down ℕ)).map
        (Augmentation.resolutionChainAugmentation (situation (J.over X) K) (Cat.of (Over X))
          (J.over X) (situationAugmentation (J.over X) K)
          (freeYonedaSheaf (J.over X) V)))) :
    IsIso (derivedAugmentationUnitOver J X K) :=
  isIso_derivedAugmentationUnitOver_of_quasiIso_freeYoneda J X K hunit fun V =>
    CochainComplex.quasiIso_map_resolutionCochainAugmentation _ _ _
      (augmentationAbelianLowerShriek (J.over X) K) (h V)

end Over

section OverHypercovering

variable {C : Type u} [SmallCategory C] [HasPullbacks C] (P : Pretopology C) {X : C}
  (K : SimplicialObject (FormalCoproduct.{u} (Over X)))

/-- **Stacks 0D8L for a hypercovering, from the `ℕ`-indexed chain quasi-isomorphism on the base
site.** This is
`isIso_derivedAugmentationUnitOver_app_of_isHypercovering_of_quasiIso_freeYoneda` with the
quasi-isomorphism hypothesis stated on the resolution of Stacks 0D78 itself rather than on its
cochain form. The object `E` of the derived category is arbitrary, with no boundedness
assumption. -/
theorem isIso_derivedAugmentationUnitOver_app_of_isHypercovering_of_quasiIso_freeYoneda_chain
    (hK : Stacks.CategoryTheory.Hypercovering.IsHypercovering P K)
    (h : ∀ V : Over X, QuasiIso
      (((augmentationAbelianLowerShriek (P.toGrothendieck.over X) K).mapHomologicalComplex
          (ComplexShape.down ℕ)).map
        (Augmentation.resolutionChainAugmentation (situation (P.toGrothendieck.over X) K)
          (Cat.of (Over X)) (P.toGrothendieck.over X)
          (situationAugmentation (P.toGrothendieck.over X) K)
          (freeYonedaSheaf (P.toGrothendieck.over X) V))))
    (E : DerivedCategory (AbelianSheavesOver P.toGrothendieck X)) :
    IsIso ((derivedAugmentationUnitOver P.toGrothendieck X K).app E) :=
  isIso_derivedAugmentationUnitOver_app_of_isHypercovering_of_quasiIso_freeYoneda P K hK
    (fun V => CochainComplex.quasiIso_map_resolutionCochainAugmentation _ _ _
      (augmentationAbelianLowerShriek (P.toGrothendieck.over X) K) (h V)) E

end OverHypercovering

end CategoryTheory.SimplicialSemiRepresentable

end
