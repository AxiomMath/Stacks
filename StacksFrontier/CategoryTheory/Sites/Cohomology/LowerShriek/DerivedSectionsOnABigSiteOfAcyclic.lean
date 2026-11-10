module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.AbelianAcyclicityFromContinuity
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.DerivedSectionsOnABigSite

/-!
# Derived sections over an object of a big site, with the counit input discharged

`Stacks.Cohomology.DerivedLowerShriek.BigSite.derivedAbelianSectionsRestrictionIso` is
**Stacks 0DD8, part (1)**, on sites that need not be small, with one hypothesis `hgen`: the
invertibility of the derived lower-shriek counit at the single complex on `j_{U!} ℤ_U`. That
hypothesis is proved here, from the acyclicity statement of Stacks 0794 for lower shriek, which
is the same input from which `Lg_!^{Ab}` itself is built.

## Main results

* `Stacks.Cohomology.DerivedLowerShriek.BigSite.derivedAbelianSectionsRestrictionIso_of_acyclic`:
  the same with the counit input proved rather than assumed, leaving the acyclicity statement of
  Stacks 0794 for lower shriek as the only hypothesis — the same statement from which
  `Lg_!^{Ab}` itself is built. On a small site that statement is derived from continuity, which
  is why the registrations carrying the tag at the source's hypotheses are the small-site ones
  of `DerivedSectionsAlongAContinuousFunctor.lean`.

## Implementation notes

The counit input is
`Stacks.Cohomology.DerivedLowerShriek.isIso_derivedAbelianLowerShriekComparison_app_of_acyclic`
of `StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.AbelianAcyclicityFromContinuity`; it
is kept out of
`StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.DerivedSectionsOnABigSite`
so that file keeps its own import closure.

## References

* [Stacks Project, Tag 0DD8](https://stacks.math.columbia.edu/tag/0DD8)
* [Stacks Project, Tag 0794](https://stacks.math.columbia.edu/tag/0794)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u₁

namespace Stacks.Cohomology.DerivedLowerShriek.BigSite

section Abelian

variable {C D : Type u₁} [Category.{v} C] [Category.{v} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (f : C ⥤ D) [f.IsContinuous J K] [f.IsCocontinuous J K] (U : C)

attribute [local instance] HasDerivedCategory.standard

variable [HasSheafify J AddCommGrpCat.{max u₁ v w}] [HasSheafify K AddCommGrpCat.{max u₁ v w}]
  [(f.sheafPushforwardContinuous AddCommGrpCat.{max u₁ v w} J K).IsRightAdjoint]
  [∀ F : Cᵒᵖ ⥤ AddCommGrpCat.{max u₁ v w}, f.op.HasPointwiseRightKanExtension F]
  [(abelianLowerShriekOnHomotopy.{max u₁ v w} J K f ⋙
    DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
    (HomotopyCategory.quasiIso (Sheaf J AddCommGrpCat.{max u₁ v w}) (ComplexShape.up ℤ))]
  [IsGrothendieckAbelian.{max u₁ v w} (Sheaf K AddCommGrpCat.{max u₁ v w})]
  [(derivedAbelianLowerShriek.{max u₁ v w} J K f ⋙
    derivedAbelianRestriction.{max u₁ v w} J K f).IsLeftDerivedFunctor
    ((Functor.associator DerivedCategory.Qh (derivedAbelianLowerShriek.{max u₁ v w} J K f)
      (derivedAbelianRestriction.{max u₁ v w} J K f)).inv ≫
      Functor.whiskerRight (derivedAbelianLowerShriekComparison.{max u₁ v w} J K f)
        (derivedAbelianRestriction.{max u₁ v w} J K f))
    (HomotopyCategory.quasiIso (Sheaf J AddCommGrpCat.{max u₁ v w}) (ComplexShape.up ℤ))]

variable [IsGrothendieckAbelian.{max u₁ v w} (Sheaf J AddCommGrpCat.{max u₁ v w})]

/-- **Stacks 0DD8, part (1), on sites that need not be small, with the counit input
discharged.** Let `u : C ⥤ D` be a continuous and cocontinuous functor of sites and let
`g : Sh(C) ⟶ Sh(D)` be the corresponding morphism of topoi. For every object `U` of `C` and
every `K` in the unbounded derived category of abelian sheaves on `D`,
`RΓ(U, g⁻¹K) = RΓ(u(U), K)`, naturally in `K`.

This is `derivedAbelianSectionsRestrictionIso` with its hypothesis `hgen` proved rather than
assumed. The invertibility of the derived lower-shriek counit at the single complex on
`j_{U!} ℤ_U` is
`Stacks.Cohomology.DerivedLowerShriek.isIso_derivedAbelianLowerShriekComparison_app_of_acyclic`,
which holds because that complex is cellular for the class with which `Lg_!^{Ab}` is built; the
one input left is `hFP`, the acyclicity statement of Stacks 0794 for lower shriek, which is the
same input from which `Lg_!^{Ab}` itself exists and which the source derives from continuity. On
a small site that derivation is
`Stacks.Cohomology.DerivedLowerShriek.abelianLowerShriekAcyclic_of_continuous`. -/
def derivedAbelianSectionsRestrictionIso_of_acyclic [Small.{max u₁ v w} C]
    (hFP : AbelianLowerShriekAcyclic.{max u₁ v w} J K f) :
    derivedAbelianRestriction.{max u₁ v w} J K f ⋙ derivedAbelianSections.{w} J U ≅
      derivedAbelianSections.{w} K (f.obj U) :=
  derivedAbelianSectionsRestrictionIso.{w} J K f U
    (isIso_derivedAbelianLowerShriekComparison_app_of_acyclic.{u₁, v, max u₁ v w} J K f hFP _
      (isSumOfExtensionByZeroUnitsAb_single.{u₁, v, max u₁ v w} J U))

end Abelian

end Stacks.Cohomology.DerivedLowerShriek.BigSite

end
