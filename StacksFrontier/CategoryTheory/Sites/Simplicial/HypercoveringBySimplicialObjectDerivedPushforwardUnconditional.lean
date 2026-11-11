module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringBySimplicialObject
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringObjectDerivedPushforward
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.CohomologyOnAnOpenSubspace
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringBySimplicialObjectDerivedPushforward

/-!
# The derived direct image along a hypercovering by a simplicial object of the site

Let `C` be a site with fibre products given by a pretopology `P`, let `X` be an object of `C`,
let `U` be a simplicial object of `C` and let `a : U ⟶ X` be an augmentation which is a
hypercovering of `X` in `C` in the sense of Stacks 09X8, that is, which satisfies the three
covering conditions of
`Stacks.CategoryTheory.Hypercovering.IsHypercoveringAugmentation`. Such an augmentation
determines the one-summand simplicial semi-representable object `n ↦ {U_n ⟶ X}` over `X`, its
total site `(C/U)_total`, and the augmentation of topoi `a : Sh((C/U)_total) ⟶ Sh(C/X)`.

Stacks 0D8N asserts that for every `E` of the unbounded derived category `D(C/X)` of abelian
sheaves on `C/X` the canonical map

`E ⟶ Ra_* a^{-1} E`

is an isomorphism; the source deduces it as a special case of Stacks 0D8L, the same assertion
for an arbitrary hypercovering of `X` by semi-representable objects. This file discharges the
first input of Stacks 0D8L, the underived augmentation unit, from the hypercovering conditions
alone, and states the results with the second input, the `Ra_*`-acyclicity of `a^{-1}` of a
K-injective complex, as an explicit hypothesis. That acyclicity is proved later in the import
order, in `HypercoveringObjectDerivedPushforwardUnconditional.lean`, where Stacks 0D8N is
`isIso_derivedAugmentationUnitAugmented_app_unconditional`.

## Main results

All names below are in the namespace `CategoryTheory.SimplicialSemiRepresentable`.

* `isIso_homotopyAugmentationUnitOver_of_isHypercovering`: the first input of Stacks 0D8L holds
  for a hypercovering of `X` by semi-representable objects.
* `isIso_derivedAugmentationUnitOver_app_of_isHypercovering` and
  `isIso_derivedAugmentationUnitAugmented_app'`: the canonical map `E ⟶ Ra_* a^{-1} E` is an
  isomorphism, for a hypercovering of `X` by semi-representable objects and for a hypercovering
  by a simplicial object of the site respectively, given the `Ra_*`-acyclicity of `a^{-1}` of a
  K-injective complex.

## Implementation notes

The first input of Stacks 0D8L is the underived unit `F ⟶ a_* a^{-1} F` of Stacks 0DA8 (2),
`CategoryTheory.SimplicialSemiRepresentable.isIso_abelianUnit_over` and
`Stacks.CategoryTheory.Hypercovering.isIso_abelianUnit_augmented'`, which the hypercovering
conditions give through cover density and local fullness of `j_total`. The acyclicity
hypothesis is asked only at the K-injective complexes; the reduction of the unbounded statement
to those complexes is `Stacks.Cohomology.Localization.natTrans_isIso_of_kInjectives`. The
acyclicity itself is `inverseImageComputesDerivedPushforward_over_of_isHypercovering`.

The derived categories are the standard ones, `CategoryTheory.HasDerivedCategory.standard`,
installed as a local instance as in the neighbouring files, and the additivity, exactness and
derived-functor-existence facts of Stacks 0D8L are re-installed as local instances here for the
same reason: no choice of model or of resolution leaks out of this module.

## References

* [Stacks Project, Tag 0D8N](https://stacks.math.columbia.edu/tag/0D8N)
* [Stacks Project, Tag 0D8L](https://stacks.math.columbia.edu/tag/0D8L)
* [Stacks Project, Tag 0DA8](https://stacks.math.columbia.edu/tag/0DA8)
* [Stacks Project, Tag 0D8E](https://stacks.math.columbia.edu/tag/0D8E)
* [Stacks Project, Tag 0D8B](https://stacks.math.columbia.edu/tag/0D8B)
* [Stacks Project, Tag 0D7A](https://stacks.math.columbia.edu/tag/0D7A)
* [Stacks Project, Tag 0D79](https://stacks.math.columbia.edu/tag/0D79)
* [Stacks Project, Tag 0D78](https://stacks.math.columbia.edu/tag/0D78)
* [Stacks Project, Tag 09X8](https://stacks.math.columbia.edu/tag/09X8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CategoryTheory

/-! ### Invertible natural transformations on complexes -/

end CategoryTheory

namespace CategoryTheory.SimplicialSemiRepresentable

open Stacks.CategoryTheory.Hypercovering

attribute [local instance] HasDerivedCategory.standard additive_abelianTotalPushforwardOver
  additive_abelianTotalInverseImageOver preservesFiniteColimits_abelianTotalInverseImageOver
  hasPointwiseRightDerivedFunctor_homotopyAbelianTotalPushforwardOver
  hasRightDerivedFunctor_homotopyAbelianTotalPushforwardOver

/-! ### The first input of Stacks 0D8L from the underived augmentation unit -/

/-! ### The first input of Stacks 0D8L discharged for a hypercovering -/

section OverHypercovering

variable {C : Type u} [SmallCategory C] [HasPullbacks C] (P : Pretopology C) {X : C}
  (K : SimplicialObject (FormalCoproduct.{u} (Over X)))

/-- **The first input of Stacks 0D8L, for a hypercovering of `X` by semi-representable objects.**
The augmentation unit of Stacks 0D8L read on unbounded homotopy categories is invertible, with
nothing carried, as soon as `K` is a hypercovering of `X`.

This is the `hunit` hypothesis of
`CategoryTheory.SimplicialSemiRepresentable.isIso_derivedAugmentationUnitOver_app`: its component
at a complex `M` is `NatIso.isIso_app_of_isIso` of this. What supplies it is the degree-zero
identification `M = a_* a^{-1} M` of Stacks 0D8K (2),
`CategoryTheory.SimplicialSemiRepresentable.isIso_abelianUnit_over`, which the hypercovering
conditions on `K` give through cover density and local fullness of `j_total`; passing from it to
the homotopy categories is `isIso_homotopyAugmentationUnitOver`.

The hypercovering hypothesis is what is doing the work and cannot be dropped: for an arbitrary
simplicial semi-representable object `K` over `X` the inverse image `a^{-1}` is not fully
faithful and this unit is not invertible. -/
theorem isIso_homotopyAugmentationUnitOver_of_isHypercovering (hK : IsHypercovering P K) :
    IsIso (homotopyAugmentationUnitOver P.toGrothendieck X K) :=
  isIso_homotopyAugmentationUnitOver P.toGrothendieck X K (isIso_abelianUnit_over P K hK)

/-- For a site `C` with fibre products, an object `X` of `C` and a hypercovering `K` of `X` by
semi-representable objects, the canonical map `E ⟶ Ra_* a^{-1} E` is an isomorphism for every
object `E` of the unbounded derived category of abelian sheaves on `C/X`, given that the direct
image of `a^{-1}` of a K-injective complex needs no derivation (`hacyclic`).

The degree-zero identification `M = a_* a^{-1} M` of Stacks 0D8K (2) is supplied here from the
hypercovering conditions by `isIso_abelianUnit_over`. The hypothesis `hacyclic` is itself proved
for a hypercovering, by `CategoryTheory.SimplicialSemiRepresentable`
`.inverseImageComputesDerivedPushforward_over_of_isHypercovering`, and Stacks 0D8L with no
hypothesis beyond the hypercovering conditions is `CategoryTheory.SimplicialSemiRepresentable`
`.isIso_derivedAugmentationUnitOver_app_of_isHypercovering_unconditional`, both in
`HypercoveringObjectDerivedPushforwardUnconditional.lean`. -/
theorem isIso_derivedAugmentationUnitOver_app_of_isHypercovering (hK : IsHypercovering P K)
    (hacyclic : ∀ I : CochainComplex (AbelianSheavesOver P.toGrothendieck X) ℤ,
      I.IsKInjective →
        IsIso ((derivedAbelianTotalPushforwardOverUnit P.toGrothendieck X K).app
          (((abelianTotalInverseImageOver P.toGrothendieck X K).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj
              ((HomotopyCategory.quotient (AbelianSheavesOver P.toGrothendieck X)
                (ComplexShape.up ℤ)).obj I))))
    (E : DerivedCategory (AbelianSheavesOver P.toGrothendieck X)) :
    IsIso ((derivedAugmentationUnitOver P.toGrothendieck X K).app E) :=
  have := isIso_derivedAugmentationUnitOver_of_isIso_unit P.toGrothendieck X K
    (isIso_abelianUnit_over P K hK) hacyclic
  NatIso.isIso_app_of_isIso _ E

end OverHypercovering

/-! ### Stacks 0D8N, given the acyclicity of `a⁻¹` of a K-injective complex -/

section Augmented

variable {C : Type u} [SmallCategory C] [HasPullbacks C] (P : Pretopology C) {X : C}
  (U : SimplicialObject C) (a : U ⟶ (SimplicialObject.const C).obj X)

/-- For a site `C` with fibre products, an object `X` of `C` and a hypercovering `a : U ⟶ X` of
`X` in `C` by a simplicial object `U` of `C`, the canonical map `E ⟶ Ra_* a^{-1} E` is an
isomorphism for every object `E` of the unbounded derived category of abelian sheaves on `C/X`,
given that the direct image of `a^{-1}` of a K-injective complex needs no derivation.

This is the deduction of Stacks 0D8N from Stacks 0D8L for the associated simplicial
semi-representable object over `X`, with the first input of Stacks 0D8L discharged from the
hypercovering conditions by `isIso_abelianUnit_augmented'`. The acyclicity hypothesis
`hacyclic` is discharged, and Stacks 0D8N proved with no further hypothesis, by
`isIso_derivedAugmentationUnitAugmented_app_unconditional`. -/
theorem isIso_derivedAugmentationUnitAugmented_app'
    (h : IsHypercoveringAugmentation P U a)
    (hacyclic : ∀ I : CochainComplex (AbelianSheavesOver P.toGrothendieck X) ℤ,
      I.IsKInjective →
        IsIso ((derivedAbelianTotalPushforwardOverUnit P.toGrothendieck X
          (associatedSimplicialObject.{u} U a)).app
            (((abelianTotalInverseImageOver P.toGrothendieck X
              (associatedSimplicialObject.{u} U a)).mapHomotopyCategory
                (ComplexShape.up ℤ)).obj
                  ((HomotopyCategory.quotient (AbelianSheavesOver P.toGrothendieck X)
                    (ComplexShape.up ℤ)).obj I))))
    (E : DerivedCategory (AbelianSheavesOver P.toGrothendieck X)) :
    IsIso ((derivedAugmentationUnitAugmented P U a).app E) :=
  have := isIso_derivedAugmentationUnitOver_of_isIso_unit P.toGrothendieck X
    (associatedSimplicialObject.{u} U a) (isIso_abelianUnit_augmented' P U a h) hacyclic
  NatIso.isIso_app_of_isIso _ E

end Augmented

end CategoryTheory.SimplicialSemiRepresentable

end
