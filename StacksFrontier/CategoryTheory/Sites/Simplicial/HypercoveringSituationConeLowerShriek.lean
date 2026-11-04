module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationResolutionConeLowerShriek
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringSituationDescentAb
public import StacksFrontier.CategoryTheory.Sites.Simplicial.SimplicialSemiRepresentableLowerShriek

/-!
# The vanishing on the base site for a simplicial semi-representable object

Let `C` be a small site and `K` a simplicial semi-representable object of `C`, with
`a : Sh((C/K)_total) ⟶ Sh(C)` the augmentation of Stacks 0D8B. The inverse image `a⁻¹` on abelian
sheaves is restriction along the localization functor `j_total` of the total site — that is
`CategoryTheory.SimplicialSemiRepresentable.situationTotalInverseImageAbIso` — and restriction
along a continuous functor has a left adjoint, so here `a_!` exists on abelian sheaves: it is
Stacks 09WM, part (2).

Feeding that adjunction to
`CategoryTheory.SimplicialSiteSituation.Augmentation`
`.inverseImageAcyclicAgainstResolutionCone_of_quasiIso_lowerShriek` discharges the hypothesis of
`CategoryTheory.SimplicialSiteSituation.Augmentation`
`.inverseImageComputesDerivedPushforward_of_vanishing` from one statement about complexes of
abelian sheaves on `(C, J)` alone:

**`a_!` carries the augmentation of the resolution of Stacks 0D78 to a quasi-isomorphism**,

which is exactness of `… ⟶ a_{1!}a_1⁻¹𝒢 ⟶ a_{0!}a_0⁻¹𝒢 ⟶ a_!a⁻¹𝒢 ⟶ 0`, the Čech resolution of
the hypercovering, i.e. Stacks 01GE with coefficients. No K-injective complex and no Hom complex
on the total site appear in it.

## Main definitions

* `CategoryTheory.SimplicialSemiRepresentable.situationAbelianLowerShriekAdjunction`: the
  adjunction `a_! ⊣ a⁻¹` of Stacks 09WM, part (2), with its right adjoint spelled as the abelian
  inverse image `totalInverseImageAb` of the morphism of topoi of Stacks 0D70.

## Main results

* `CategoryTheory.SimplicialSemiRepresentable`
  `.inverseImageAcyclicAgainstResolutionCone_of_quasiIso_lowerShriek`: the vanishing of
  `InverseImageAcyclicAgainstResolutionCone` from that one quasi-isomorphism.
* `CategoryTheory.SimplicialSemiRepresentable`
  `.inverseImageComputesDerivedPushforward_of_quasiIso_lowerShriek`: and hence
  `InverseImageComputesDerivedPushforward`, granted also that the component inverse images of a
  K-injective complex restrict to K-injective complexes (Stacks 0D88).

## References

* [Stacks Project, Tag 0D8G](https://stacks.math.columbia.edu/tag/0D8G)
* [Stacks Project, Tag 09WM](https://stacks.math.columbia.edu/tag/09WM)
* [Stacks Project, Tag 0D8B](https://stacks.math.columbia.edu/tag/0D8B)
* [Stacks Project, Tag 0D78](https://stacks.math.columbia.edu/tag/0D78)
* [Stacks Project, Tag 0D88](https://stacks.math.columbia.edu/tag/0D88)
* [Stacks Project, Tag 01GE](https://stacks.math.columbia.edu/tag/01GE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.SimplicialSiteSituation

universe u

namespace CategoryTheory.SimplicialSemiRepresentable

attribute [local instance] HasDerivedCategory.standard

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  (K : SimplicialObject (FormalCoproduct.{u} C)) [J.toCoverage.HasPullbacks]

/-- **Stacks 09WM, part (2), against the inverse image of Stacks 0D70.** The extension by zero
`a_!` on abelian sheaves is left adjoint to the abelian inverse image of the morphism of topoi
which Stacks 0D70 attaches to the augmentation: that inverse image is restriction along `j_total`
by `situationTotalInverseImageAbIso`, and `a_!` is left adjoint to that restriction. -/
def situationAbelianLowerShriekAdjunction :
    augmentationAbelianLowerShriek J K ⊣
      Augmentation.totalInverseImageAb (situation J K) (Cat.of C) J (situationAugmentation J K) :=
  (augmentationAbelianLowerShriekAdjunction J K).ofNatIsoRight
    (situationTotalInverseImageAbIso J K).symm

/-- The extension by zero `a_!` on abelian sheaves is additive, being a left adjoint of the
additive functor `a⁻¹`. -/
instance additive_augmentationAbelianLowerShriek :
    (augmentationAbelianLowerShriek J K).Additive :=
  haveI := Augmentation.additive_totalInverseImageAb (situation J K) (Cat.of C) J
    (situationAugmentation J K)
  (situationAbelianLowerShriekAdjunction J K).left_adjoint_additive

/-- **The vanishing on the base site from one quasi-isomorphism on it.** For a simplicial
semi-representable object the statement
`CategoryTheory.SimplicialSiteSituation.Augmentation.InverseImageAcyclicAgainstResolutionCone`
follows from the single statement that the extension by zero `a_!` carries the augmentation of
the resolution of Stacks 0D78 to a quasi-isomorphism, that is that the Čech resolution

`… ⟶ a_{1!}a_1⁻¹𝒢 ⟶ a_{0!}a_0⁻¹𝒢 ⟶ a_!a⁻¹𝒢 ⟶ 0`

of abelian sheaves on `(C, J)` is exact — Stacks 01GE with coefficients. -/
theorem inverseImageAcyclicAgainstResolutionCone_of_quasiIso_lowerShriek
    (h : ∀ G : Sheaf J Ab.{u}, QuasiIso
      (((augmentationAbelianLowerShriek J K).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (Augmentation.resolutionCochainAug (situation J K) (Cat.of C) J
          (situationAugmentation J K) G))) :
    Augmentation.InverseImageAcyclicAgainstResolutionCone (situation J K) (Cat.of C) J
      (situationAugmentation J K) :=
  Augmentation.inverseImageAcyclicAgainstResolutionCone_of_quasiIso_lowerShriek _ _ _ _
    (situationAbelianLowerShriekAdjunction J K) h

/-- **`InverseImageComputesDerivedPushforward` for a simplicial semi-representable object, from
one quasi-isomorphism on the base site.** The hypothesis `hrestr` is Stacks 0D88 — the component
inverse images of a K-injective complex restrict to K-injective complexes — and `h` is exactness
of the Čech resolution, Stacks 01GE with coefficients. -/
theorem inverseImageComputesDerivedPushforward_of_quasiIso_lowerShriek
    (hrestr : ∀ (p : SimplexCategory) (I : CochainComplex (Sheaf J Ab.{u}) ℤ),
      I.IsKInjective → CochainComplex.IsKInjective
        (((SimplicialSiteSituation.restrictAb (situation J K) p).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj
          (((Augmentation.totalInverseImageAb (situation J K) (Cat.of C) J
            (situationAugmentation J K)).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)))
    (h : ∀ G : Sheaf J Ab.{u}, QuasiIso
      (((augmentationAbelianLowerShriek J K).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (Augmentation.resolutionCochainAug (situation J K) (Cat.of C) J
          (situationAugmentation J K) G))) :
    Augmentation.InverseImageComputesDerivedPushforward (situation J K) (Cat.of C) J
      (situationAugmentation J K) :=
  Augmentation.inverseImageComputesDerivedPushforward_of_vanishing _ _ _ _ hrestr
    (inverseImageAcyclicAgainstResolutionCone_of_quasiIso_lowerShriek J K h)

end CategoryTheory.SimplicialSemiRepresentable

end
