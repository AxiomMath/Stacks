module

public import Mathlib.CategoryTheory.Sites.GlobalSections
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.LerayForUnboundedSections
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringCohomologicalDescent
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringObjectDerivedPushforwardUnconditional
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringSituationGlobalSections
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringUnit
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringDerivedGlobalSections

/-!
# Derived global sections along the augmentation of a hypercovering

Let `C` be a site with equalizers and fibre products, let `K` be a hypercovering of it and let
`a` be the augmentation of Stacks 0D8B from the total site `(C/K)_total` to `C`. Stacks 0D8H
asserts that

`RΓ(C, E) = RΓ((C/K)_total, a⁻¹E)`

for every object `E` of the *unbounded* derived category of abelian sheaves on `C`. The source
deduces it from Stacks 0D8G, that `E ⟶ R a_* a⁻¹ E` is an isomorphism, together with the
factorisation `RΓ((C/K)_total, -) = RΓ(C, -) ∘ R a_*` of Cohomology on Sites, Remark 21.14.4,
which is Stacks 08J6.

Both steps are carried out here. Global sections are Mathlib's `CategoryTheory.Sheaf.Γ`, the
right adjoint of the constant-sheaf functor, so that no terminal object of the site is needed,
and `RΓ` is its total right derived functor on the unbounded derived category.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.Augmentation.derivedGlobalSectionsBase` and
  `.derivedGlobalSectionsTotal`: `RΓ(C, -)` and `RΓ((C/K)_total, -)` on the unbounded derived
  categories of abelian sheaves.
* `CategoryTheory.SimplicialSiteSituation.Augmentation.derivedGlobalSectionsPushforwardIso`:
  **the derived half of Stacks 08J6 for the total augmentation**, the factorisation
  `R a_* ⋙ RΓ(C, -) ≅ RΓ((C/K)_total, -)`.
* `CategoryTheory.SimplicialSiteSituation.Augmentation.derivedGlobalSectionsInverseImageIso`:
  the isomorphism `RΓ(C, -) ≅ a⁻¹ ⋙ RΓ((C/K)_total, -)` for a general augmentation.
* `Stacks.CategoryTheory.Hypercovering.derivedGlobalSectionsInverseImageIsoOfHypercovering`:
  the same for the augmentation of Stacks 0D8B attached to a hypercovering, which is
  Stacks 0D8H.

## Main results

* `CategoryTheory.SimplicialSiteSituation.Augmentation.isKInjective_abelianTotalPushforward`:
  **Stacks 093Y for the total augmentation** — degreewise `a_*` carries K-injective complexes of
  abelian sheaves to K-injective complexes. This is the one input of the derived factorisation
  that is not formal, and it is proved rather than assumed: `a_*` is the right adjoint of the
  exact functor `a⁻¹`.

## The inputs of Stacks 0D8H for a hypercovering

The general
`CategoryTheory.SimplicialSiteSituation.Augmentation.derivedGlobalSectionsInverseImageIso`
takes three inputs, and for the augmentation of a hypercovering all three are proved, so
`Stacks.CategoryTheory.Hypercovering.derivedGlobalSectionsInverseImageIsoOfHypercovering` carries
no hypothesis beyond the hypercovering conditions on `K`.

* `hunit` and `hacyclic` are the two inputs of Stacks 0D8G. The first is Stacks 0D8E in its
  abelian form,
  `CategoryTheory.SimplicialSemiRepresentable.isIso_situationAbelianTotalAdjunctionUnit`;
  the second is the `R a_*`-acyclicity of `a⁻¹` of a K-injective complex,
  `inverseImageComputesDerivedPushforward_of_hypercoveringOfTerminal` in the namespace
  `CategoryTheory.SimplicialSemiRepresentable`.
* `hΓ` is the **underived** identity `Γ(C, a_*F) = Γ((C/K)_total, F)` on which Stacks 08J6 rests,
  `CategoryTheory.SimplicialSemiRepresentable.abelianTotalPushforwardGammaIso`.

What is *not* assumed is the derived content: the factorisation
`R a_* ⋙ RΓ(C, -) ≅ RΓ((C/K)_total, -)` is proved from `hΓ` by
`Stacks.Cohomology.LerayUnbounded.derivedCompIso`, whose hypothesis — that degreewise `a_*`
preserves K-injectivity — is discharged here. The library's own Stacks 08J6,
`Stacks.Cohomology.Leray.derivedGlobalSectionsPushforwardIso`, cannot be used instead: it is
about sheaves of *modules* on *ringed* topoi and only on the bounded below derived category,
whereas Stacks 0D8H is about abelian sheaves and makes no boundedness assumption.

## Implementation notes

`RΓ` is `Stacks.DerivedFunctor.totalRightDerived` of `CategoryTheory.Sheaf.Γ`, the same
shape as the derived direct image of
`StacksFrontier/CategoryTheory/Sites/Simplicial/HypercoveringCohomologicalDescent.lean`; in
particular `CategoryTheory.SimplicialSiteSituation.Augmentation.derivedTotalPushforward` *is*
`Stacks.DerivedFunctor.totalRightDerived` of the degreewise direct image, which is what lets
`derivedCompIso` be applied to the pair `(a_*, Γ(C, -))` with no comparison of two models of
`R a_*`.

Global sections are additive because they are a right adjoint, hence preserve binary products.
A global-sections functor exists for every site here because `Ab` has limits of the shape of the
site, which is `CategoryTheory.hasGlobalSectionsFunctor_of_hasLimitsOfShape`; no terminal object
is involved, which matters because the site of a hypercovering need not have one.

The conclusion is an isomorphism of *functors* on the unbounded derived category, so it holds at
every object `E` of `D(C)` with no boundedness assumption, which is the form the source states.

## References

* [Stacks Project, Tag 0D8H](https://stacks.math.columbia.edu/tag/0D8H)
* [Stacks Project, Tag 0D8G](https://stacks.math.columbia.edu/tag/0D8G)
* [Stacks Project, Tag 0D8E](https://stacks.math.columbia.edu/tag/0D8E)
* [Stacks Project, Tag 0D8B](https://stacks.math.columbia.edu/tag/0D8B)
* [Stacks Project, Tag 08J6](https://stacks.math.columbia.edu/tag/08J6)
* [Stacks Project, Tag 093Y](https://stacks.math.columbia.edu/tag/093Y)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.SimplicialSiteSituation.Augmentation

attribute [local instance] HasDerivedCategory.standard

variable (S : SimplicialSiteSituation.{u}) (D : Cat.{u, u}) (K : GrothendieckTopology D)
  (a : Augmentation S D K)

/-! ### Derived global sections on the two sites -/

/-! ### The derived factorisation of Stacks 08J6 -/

/-! ### Derived global sections are unchanged by the inverse image -/

end CategoryTheory.SimplicialSiteSituation.Augmentation

namespace Stacks.CategoryTheory.Hypercovering

open CategoryTheory CategoryTheory.SimplicialSiteSituation

attribute [local instance] HasDerivedCategory.standard

variable {C : Type u} [SmallCategory C] [HasEqualizers C] [HasPullbacks C] (J : Pretopology C)
  (H : HypercoveringOfTerminal.{u, u} J)

/-- **Stacks 0D8H.** For a site `C` with equalizers
and fibre products, a hypercovering `K` of it, and the augmentation
`a : Sh((C/K)_total) ⟶ Sh(C)` of Stacks 0D8B, derived global sections on `C` are derived global
sections on the total site of the inverse image:

`RΓ(C, E) = RΓ((C/K)_total, a⁻¹E)`.

The statement is an isomorphism of functors on the *unbounded* derived category of abelian
sheaves on `C`, so it holds at every object `E` with no boundedness assumption, which is the form
the source states.

No hypothesis beyond the hypercovering conditions on `K` is carried. The `R a_*`-acyclicity of
`a⁻¹` of a K-injective complex, which is the one remaining input of Stacks 0D8G, is
`CategoryTheory.SimplicialSemiRepresentable`
`.inverseImageComputesDerivedPushforward_of_hypercoveringOfTerminal`. The other input of
Stacks 0D8G, that the underived unit `F ⟶ a_*a⁻¹F` is an isomorphism, is Stacks 0D8E in its
abelian form, which
`CategoryTheory.SimplicialSemiRepresentable.isIso_situationAbelianTotalAdjunctionUnit` proves for
this augmentation. The underived identity `Γ(C, a_*F) = Γ((C/K)_total, F)` on which the
factorisation of Stacks 08J6 rests is
`CategoryTheory.SimplicialSemiRepresentable.abelianTotalPushforwardGammaIso`. The derived content
of Stacks 08J6 is *not* assumed: see the module docstring. -/
@[stacks 0D8H]
def derivedGlobalSectionsInverseImageIsoOfHypercovering' :
    Augmentation.derivedGlobalSectionsBase (Cat.of C) J.toGrothendieck ≅
      Augmentation.derivedTotalInverseImage (hypercoveringSituation J H) (Cat.of C)
          J.toGrothendieck (hypercoveringAugmentation J H) ⋙
        Augmentation.derivedGlobalSectionsTotal (hypercoveringSituation J H) :=
  Augmentation.derivedGlobalSectionsInverseImageIso (hypercoveringSituation J H) (Cat.of C)
    J.toGrothendieck (hypercoveringAugmentation J H)
    (CategoryTheory.SimplicialSemiRepresentable.isIso_situationAbelianTotalAdjunctionUnit J H)
    (SimplicialSemiRepresentable.inverseImageComputesDerivedPushforward_of_hypercoveringOfTerminal
      J H)
    (SimplicialSemiRepresentable.abelianTotalPushforwardGammaIso J.toGrothendieck
      H.toSimplicialObject)

end Stacks.CategoryTheory.Hypercovering

end
