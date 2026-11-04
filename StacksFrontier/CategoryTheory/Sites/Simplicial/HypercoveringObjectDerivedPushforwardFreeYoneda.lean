module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringObjectDerivedPushforwardSituation
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringSituationComponentKInjective

/-!
# Derived pushforward along a hypercovering from a quasi-isomorphism of free abelian sheaves

Let `(C, J)` be a site with fibre products, `X` an object of `C` and `K` a simplicial object of
`SR(C, X) = FormalCoproduct (Over X)`, with augmentation `a`. This module shows that the canonical
map `E ⟶ Ra_* a^{-1} E` on `D(C/X)` is invertible provided the extension by zero `a_!` carries the
augmentation of the resolution of Stacks 0D78 of `a^{-1}ℤ_V^♯` to a quasi-isomorphism for every
object `V` of `C/X`.

## Main results

* `CategoryTheory.SimplicialSemiRepresentable`
  `.isIso_derivedAugmentationUnitOver_of_quasiIso_freeYoneda`: `E ⟶ Ra_* a^{-1} E` is invertible
  if the underived augmentation unit on abelian sheaves is invertible and the quasi-isomorphism
  condition above holds.
* `CategoryTheory.SimplicialSemiRepresentable`
  `.isIso_derivedAugmentationUnitOver_app_of_isHypercovering_of_quasiIso_freeYoneda`: the same for
  a hypercovering `K`, assuming only the quasi-isomorphism condition.

## Implementation notes

The abelian sheaves on the total site are spelled as the general apparatus spells them and never
by the abbreviation `CategoryTheory.SimplicialSemiRepresentable.TotalAbelianSheavesOver`: a
declaration containing two comparisons of the two spellings exceeds the elaboration budget (see
`HypercoveringObjectDerivedPushforwardSituation.lean`).

No `@[stacks 0D8L]` attribute is placed here: the results carry a hypothesis that Stacks 0D8L
does not.

## References

* [Stacks Project, Tag 0D8L](https://stacks.math.columbia.edu/tag/0D8L)
* [Stacks Project, Tag 0D8G](https://stacks.math.columbia.edu/tag/0D8G)
* [Stacks Project, Tag 0D88](https://stacks.math.columbia.edu/tag/0D88)
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

section Over

variable {C : Type u} [SmallCategory C] [HasPullbacks C] (J : GrothendieckTopology C) (X : C)
  (K : SimplicialObject (FormalCoproduct.{u} (Over X)))

/-- The canonical map `E ⟶ Ra_* a^{-1} E` on `D(C/X)` is invertible as soon as the augmentation
unit `F ⟶ a_* a^{-1} F` on abelian sheaves is invertible and the extension by zero `a_!` carries
the augmentation of the resolution of Stacks 0D78 of `a^{-1}ℤ_V^♯` to a quasi-isomorphism for
every object `V` of `C/X`. -/
theorem isIso_derivedAugmentationUnitOver_of_quasiIso_freeYoneda
    (hunit : IsIso (abelianTotalAdjunctionOver J X K).unit)
    (h : ∀ V : Over X, QuasiIso
      (((augmentationAbelianLowerShriek (J.over X) K).mapHomologicalComplex
          (ComplexShape.up ℤ)).map
        (Augmentation.resolutionCochainAug (situation (J.over X) K) (Cat.of (Over X)) (J.over X)
          (situationAugmentation (J.over X) K) (freeYonedaSheaf (J.over X) V)))) :
    IsIso (derivedAugmentationUnitOver J X K) :=
  isIso_derivedAugmentationUnitOver_of_situation J X K hunit
    (inverseImageComputesDerivedPushforward_of_quasiIso_freeYoneda (J.over X) K h)

end Over

section OverHypercovering

variable {C : Type u} [SmallCategory C] [HasPullbacks C] (P : Pretopology C) {X : C}
  (K : SimplicialObject (FormalCoproduct.{u} (Over X)))

/-- For a site `C` with fibre products, an object `X` of `C` and a hypercovering `K` of `X` by
semi-representable objects, the canonical map `E ⟶ Ra_* a^{-1} E` is an isomorphism for every
object `E` of the unbounded derived category of abelian sheaves on `C/X`, provided the extension
by zero `a_!` carries the augmentation of the resolution of Stacks 0D78 of `a^{-1}ℤ_V^♯` to a
quasi-isomorphism for every object `V` of `C/X`. -/
theorem isIso_derivedAugmentationUnitOver_app_of_isHypercovering_of_quasiIso_freeYoneda
    (hK : Stacks.CategoryTheory.Hypercovering.IsHypercovering P K)
    (h : ∀ V : Over X, QuasiIso
      (((augmentationAbelianLowerShriek (P.toGrothendieck.over X) K).mapHomologicalComplex
          (ComplexShape.up ℤ)).map
        (Augmentation.resolutionCochainAug (situation (P.toGrothendieck.over X) K)
          (Cat.of (Over X)) (P.toGrothendieck.over X)
          (situationAugmentation (P.toGrothendieck.over X) K)
          (freeYonedaSheaf (P.toGrothendieck.over X) V))))
    (E : DerivedCategory (AbelianSheavesOver P.toGrothendieck X)) :
    IsIso ((derivedAugmentationUnitOver P.toGrothendieck X K).app E) :=
  have := isIso_derivedAugmentationUnitOver_of_quasiIso_freeYoneda P.toGrothendieck X K
    (isIso_abelianUnit_over P K hK) h
  NatIso.isIso_app_of_isIso _ E

end OverHypercovering

end CategoryTheory.SimplicialSemiRepresentable

end
