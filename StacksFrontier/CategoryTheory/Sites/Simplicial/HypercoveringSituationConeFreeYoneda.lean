module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationResolutionConeFreeYoneda
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringSituationConeLowerShriek

/-!
# The vanishing on the base site for a simplicial semi-representable object, at the free abelian
sheaves on the representables

Let `C` be a small site and `K` a simplicial semi-representable object of `C`, with
`a : Sh((C/K)_total) ⟶ Sh(C)` the augmentation of Stacks 0D8B.
`StacksFrontier/CategoryTheory/Sites/Simplicial/HypercoveringSituationConeLowerShriek.lean` reduces
`CategoryTheory.SimplicialSiteSituation.Augmentation.InverseImageComputesDerivedPushforward` for
this situation to the statement that `a_!` carries the augmentation of the resolution of
Stacks 0D78 of `a⁻¹𝒢` to a quasi-isomorphism — for *every* abelian sheaf `𝒢` on `(C, J)`.

That quantifier is not needed.
`StacksFrontier/CategoryTheory/Sites/Simplicial/AugmentationResolutionConeFreeYoneda.lean` re-runs
the reduction with `𝒢` restricted to the free abelian sheaves `ℤ_V^♯` on the representables,
which already detect acyclicity; this module reads that restricted reduction at the simplicial
semi-representable situation, where the left adjoint `a_!` is the extension by zero
`CategoryTheory.SimplicialSemiRepresentable.augmentationAbelianLowerShriek` of Stacks 09WM,
part (2).

The point of the restriction is that `ℤ_V^♯` is the one coefficient case in which the terms of
the resolution are again free abelian sheaves on presheaves of *sets*: by
`CategoryTheory.SimplicialSemiRepresentable.augmentationComponentFreeYonedaIso`, the degree-`p`
term `a_! g_{p!} j_p^{-1} ℤ_V^♯` is the free abelian sheaf on `h_V × F(K_p)`. So the
quasi-isomorphism asked for here is Stacks 01GE base-changed along `h_V`, which is
`Stacks.CategoryTheory.Hypercovering.quasiIso_freeAbelianSheafResolutionAugmentation_prodConst`,
rather than Stacks 01GE with general coefficients.

## Main results

* `CategoryTheory.SimplicialSemiRepresentable`
  `.inverseImageAcyclicAgainstResolutionConeFreeYoneda_of_quasiIso_lowerShriek`: the restricted
  vanishing `InverseImageAcyclicAgainstResolutionConeFreeYoneda` from one quasi-isomorphism per
  object of `C`.
* `CategoryTheory.SimplicialSemiRepresentable`
  `.inverseImageComputesDerivedPushforward_of_quasiIso_lowerShriek_freeYoneda`: and hence
  `InverseImageComputesDerivedPushforward`, granted also Stacks 0D88.

## Implementation notes

This is the exact analogue of `CategoryTheory.SimplicialSemiRepresentable`
`.inverseImageAcyclicAgainstResolutionCone_of_quasiIso_lowerShriek` and
`.inverseImageComputesDerivedPushforward_of_quasiIso_lowerShriek`, with the quantifier over all
abelian sheaves `𝒢` replaced by one over the objects `V` of `C`. The adjunction fed in is the
same one, `situationAbelianLowerShriekAdjunction`.

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
open Stacks.Cohomology.CohomologyPresheaf

universe u

namespace CategoryTheory.SimplicialSemiRepresentable

attribute [local instance] HasDerivedCategory.standard

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  (K : SimplicialObject (FormalCoproduct.{u} C)) [J.toCoverage.HasPullbacks]

/-- **The restricted vanishing on the base site from one quasi-isomorphism per object of the
site.** For a simplicial semi-representable object the statement
`Augmentation.InverseImageAcyclicAgainstResolutionConeFreeYoneda` follows from the statement that
for every object `V` of `C` the extension by zero `a_!` carries the augmentation of the resolution
of Stacks 0D78 of `a⁻¹ℤ_V^♯` to a quasi-isomorphism, that is that the Čech resolution

`… ⟶ a_{1!}a_1⁻¹ℤ_V^♯ ⟶ a_{0!}a_0⁻¹ℤ_V^♯ ⟶ a_!a⁻¹ℤ_V^♯ ⟶ 0`

of abelian sheaves on `(C, J)` is exact.

By `augmentationComponentFreeYonedaIso` the terms of that complex are the free abelian sheaves on
the presheaves `h_V × F(K_p)`, so this is Stacks 01GE base-changed along `h_V` and not
Stacks 01GE with general coefficients. -/
theorem inverseImageAcyclicAgainstResolutionConeFreeYoneda_of_quasiIso_lowerShriek
    (h : ∀ V : C, QuasiIso
      (((augmentationAbelianLowerShriek J K).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (Augmentation.resolutionCochainAug (situation J K) (Cat.of C) J
          (situationAugmentation J K) (freeYonedaSheaf J V)))) :
    Augmentation.InverseImageAcyclicAgainstResolutionConeFreeYoneda (situation J K) (Cat.of C) J
      (situationAugmentation J K) :=
  Augmentation.inverseImageAcyclicAgainstResolutionConeFreeYoneda_of_quasiIso_lowerShriek
    _ _ _ _ (situationAbelianLowerShriekAdjunction J K) h

/-- **`InverseImageComputesDerivedPushforward` for a simplicial semi-representable object, from
one quasi-isomorphism per object of the base site.** The hypothesis `hrestr` is Stacks 0D88 — the
component inverse images of a K-injective complex restrict to K-injective complexes — and `h` is
exactness of the Čech resolution of `a⁻¹ℤ_V^♯`.

This is `inverseImageComputesDerivedPushforward_of_quasiIso_lowerShriek` with the quantifier
over abelian sheaves replaced by one over the objects of `C`. -/
theorem inverseImageComputesDerivedPushforward_of_quasiIso_lowerShriek_freeYoneda
    (hrestr : ∀ (p : SimplexCategory) (I : CochainComplex (Sheaf J Ab.{u}) ℤ),
      I.IsKInjective → CochainComplex.IsKInjective
        (((SimplicialSiteSituation.restrictAb (situation J K) p).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj
          (((Augmentation.totalInverseImageAb (situation J K) (Cat.of C) J
            (situationAugmentation J K)).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)))
    (h : ∀ V : C, QuasiIso
      (((augmentationAbelianLowerShriek J K).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (Augmentation.resolutionCochainAug (situation J K) (Cat.of C) J
          (situationAugmentation J K) (freeYonedaSheaf J V)))) :
    Augmentation.InverseImageComputesDerivedPushforward (situation J K) (Cat.of C) J
      (situationAugmentation J K) :=
  Augmentation.inverseImageComputesDerivedPushforward_of_vanishing_freeYoneda _ _ _ _ hrestr
    (inverseImageAcyclicAgainstResolutionConeFreeYoneda_of_quasiIso_lowerShriek J K h)

/-- **The restricted vanishing on the base site from one quasi-isomorphism of `ℕ`-indexed chain
complexes per object of the site.** This is
`CategoryTheory.SimplicialSemiRepresentable`
`.inverseImageAcyclicAgainstResolutionConeFreeYoneda_of_quasiIso_lowerShriek` with the hypothesis
moved off the cochain form of the resolution of Stacks 0D78 and onto the resolution itself.

The augmentation of that resolution is a morphism of `ℕ`-indexed chain complexes, while the
complex whose exactness the criterion tests is formed in `ℤ`-indexed cochain complexes, with the
chain complex placed in non-positive degrees and `a_!` applied *after* that placement. The
transfer is `CochainComplex.quasiIso_map_resolutionCochainAugmentation`. -/
theorem inverseImageAcyclicAgainstResolutionConeFreeYoneda_of_quasiIso_lowerShriek_chain
    (h : ∀ V : C, QuasiIso
      (((augmentationAbelianLowerShriek J K).mapHomologicalComplex (ComplexShape.down ℕ)).map
        (Augmentation.resolutionChainAugmentation (situation J K) (Cat.of C) J
          (situationAugmentation J K) (freeYonedaSheaf J V)))) :
    Augmentation.InverseImageAcyclicAgainstResolutionConeFreeYoneda (situation J K) (Cat.of C) J
      (situationAugmentation J K) :=
  inverseImageAcyclicAgainstResolutionConeFreeYoneda_of_quasiIso_lowerShriek J K
    fun V => CochainComplex.quasiIso_map_resolutionCochainAugmentation _ _ _
      (augmentationAbelianLowerShriek J K) (h V)

/-- **`InverseImageComputesDerivedPushforward` for a simplicial semi-representable object, from one
quasi-isomorphism of `ℕ`-indexed chain complexes per object of the base site.** This is
`CategoryTheory.SimplicialSemiRepresentable`
`.inverseImageComputesDerivedPushforward_of_quasiIso_lowerShriek_freeYoneda` with the second
hypothesis stated on the augmentation of the resolution of Stacks 0D78 itself rather than on its
cochain form. -/
theorem inverseImageComputesDerivedPushforward_of_quasiIso_lowerShriek_freeYoneda_chain
    (hrestr : ∀ (p : SimplexCategory) (I : CochainComplex (Sheaf J Ab.{u}) ℤ),
      I.IsKInjective → CochainComplex.IsKInjective
        (((SimplicialSiteSituation.restrictAb (situation J K) p).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj
          (((Augmentation.totalInverseImageAb (situation J K) (Cat.of C) J
            (situationAugmentation J K)).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)))
    (h : ∀ V : C, QuasiIso
      (((augmentationAbelianLowerShriek J K).mapHomologicalComplex (ComplexShape.down ℕ)).map
        (Augmentation.resolutionChainAugmentation (situation J K) (Cat.of C) J
          (situationAugmentation J K) (freeYonedaSheaf J V)))) :
    Augmentation.InverseImageComputesDerivedPushforward (situation J K) (Cat.of C) J
      (situationAugmentation J K) :=
  Augmentation.inverseImageComputesDerivedPushforward_of_vanishing_freeYoneda _ _ _ _ hrestr
    (inverseImageAcyclicAgainstResolutionConeFreeYoneda_of_quasiIso_lowerShriek_chain J K h)

end CategoryTheory.SimplicialSemiRepresentable

end
