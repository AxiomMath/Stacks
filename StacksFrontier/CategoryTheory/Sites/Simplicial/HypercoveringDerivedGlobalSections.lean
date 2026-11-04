module

public import Mathlib.CategoryTheory.Sites.GlobalSections
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.LerayForUnboundedSections
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringCohomologicalDescent
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringObjectDerivedPushforwardUnconditional
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringSituationGlobalSections
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringUnit

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

The general `CategoryTheory.SimplicialSiteSituation.Augmentation.derivedGlobalSectionsInverseImageIso`
takes three inputs, and for the augmentation of a hypercovering all three are proved, so
`Stacks.CategoryTheory.Hypercovering.derivedGlobalSectionsInverseImageIsoOfHypercovering` carries
no hypothesis beyond the hypercovering conditions on `K`.

* `hunit` and `hacyclic` are the two inputs of Stacks 0D8G. The first is Stacks 0D8E in its
  abelian form, `CategoryTheory.SimplicialSemiRepresentable.isIso_situationAbelianTotalAdjunctionUnit`;
  the second is the `R a_*`-acyclicity of `a⁻¹` of a K-injective complex,
  `CategoryTheory.SimplicialSemiRepresentable.inverseImageComputesDerivedPushforward_of_hypercoveringOfTerminal`.
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

/-- Global sections of abelian sheaves on the total site are additive, being a right adjoint and
therefore preserving binary products. -/
instance additive_globalSectionsTotal :
    (Sheaf.Γ S.totalTopology AddCommGrpCat.{u}).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Global sections of abelian sheaves on the augmentation site are additive. -/
instance additive_globalSectionsBase : (Sheaf.Γ K AddCommGrpCat.{u}).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- `RΓ((C/K)_total, -)`: the total right derived functor of global sections of abelian sheaves
on the total site, on the unbounded derived category. -/
abbrev derivedGlobalSectionsTotal :
    DerivedCategory (Sheaf S.totalTopology AddCommGrpCat.{u}) ⥤
      DerivedCategory AddCommGrpCat.{u} :=
  Stacks.DerivedFunctor.totalRightDerived (Sheaf.Γ S.totalTopology AddCommGrpCat.{u})

/-- `RΓ(C, -)`: the total right derived functor of global sections of abelian sheaves on the
augmentation site, on the unbounded derived category. -/
abbrev derivedGlobalSectionsBase :
    DerivedCategory (Sheaf K AddCommGrpCat.{u}) ⥤ DerivedCategory AddCommGrpCat.{u} :=
  Stacks.DerivedFunctor.totalRightDerived (Sheaf.Γ K AddCommGrpCat.{u})

/-! ### The derived factorisation of Stacks 08J6 -/

/-- **Stacks 093Y for the total augmentation.** Degreewise direct image along the total
augmentation carries a K-injective complex of abelian sheaves on the total site to a K-injective
complex of abelian sheaves on the augmentation site, because `a_*` is the right adjoint of the
exact functor `a⁻¹`. -/
theorem isKInjective_abelianTotalPushforward
    (I : CochainComplex (Sheaf S.totalTopology AddCommGrpCat.{u}) ℤ) (hI : I.IsKInjective) :
    CochainComplex.IsKInjective
      (((abelianTotalPushforward S D K a).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
  (Stacks.Cohomology.isKInjectiveHomotopyCategory_iff_isKInjective _).mp
    (_root_.rightAdjoint_preserves_isKInjective _ _ (abelianTotalAdjunction S D K a) I
      ((Stacks.Cohomology.isKInjectiveHomotopyCategory_iff_isKInjective I).mpr hI))

/-- **The derived half of Stacks 08J6 for the total augmentation:** granted the underived
identity `Γ(C, a_*F) = Γ((C/K)_total, F)`, the composition `R a_* ⋙ RΓ(C, -)` is
`RΓ((C/K)_total, -)`.

Both sides are total right derived functors of one and the same functor on the unbounded homotopy
category of abelian sheaves on the total site, so they agree by uniqueness of right derived
functors; the input that makes the left hand side a right derived functor at all is
`isKInjective_abelianTotalPushforward`. Only the underived identity is assumed. -/
def derivedGlobalSectionsPushforwardIso
    (hΓ : abelianTotalPushforward S D K a ⋙ Sheaf.Γ K AddCommGrpCat.{u} ≅
      Sheaf.Γ S.totalTopology AddCommGrpCat.{u}) :
    derivedTotalPushforward S D K a ⋙ derivedGlobalSectionsBase D K ≅
      derivedGlobalSectionsTotal S :=
  Stacks.Cohomology.LerayUnbounded.derivedCompIso _ _ _ hΓ
    (isKInjective_abelianTotalPushforward S D K a)

/-! ### Derived global sections are unchanged by the inverse image -/

/-- **`RΓ(C, E) = RΓ((C/K)_total, a⁻¹E)` for a general augmentation**, granted the two inputs of
Stacks 0D8G and the underived identity `Γ(C, a_*F) = Γ((C/K)_total, F)`.

The isomorphism is the canonical map `E ⟶ R a_* a⁻¹ E`, which `hunit` and `hacyclic` make
invertible, followed by the factorisation `R a_* ⋙ RΓ(C, -) ≅ RΓ((C/K)_total, -)`. It is an
isomorphism of functors on the unbounded derived category, so no boundedness is assumed of
`E`. -/
def derivedGlobalSectionsInverseImageIso
    (hunit : IsIso (abelianTotalAdjunction S D K a).unit)
    (hacyclic : InverseImageComputesDerivedPushforward S D K a)
    (hΓ : abelianTotalPushforward S D K a ⋙ Sheaf.Γ K AddCommGrpCat.{u} ≅
      Sheaf.Γ S.totalTopology AddCommGrpCat.{u}) :
    derivedGlobalSectionsBase D K ≅
      derivedTotalInverseImage S D K a ⋙ derivedGlobalSectionsTotal S :=
  have := isIso_derivedAugmentationUnit S D K a hunit hacyclic
  (Functor.leftUnitor (derivedGlobalSectionsBase D K)).symm ≪≫
    Functor.isoWhiskerRight (asIso (derivedAugmentationUnit S D K a))
      (derivedGlobalSectionsBase D K) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (derivedTotalInverseImage S D K a)
      (derivedGlobalSectionsPushforwardIso S D K a hΓ)

end CategoryTheory.SimplicialSiteSituation.Augmentation

namespace Stacks.CategoryTheory.Hypercovering

open CategoryTheory CategoryTheory.SimplicialSiteSituation

attribute [local instance] HasDerivedCategory.standard

variable {C : Type u} [SmallCategory C] [HasEqualizers C] [HasPullbacks C] (J : Pretopology C)
  (H : HypercoveringOfTerminal.{u, u} J)

/-- **Stacks 0D8H.** For a site `C` with equalizers and fibre products, a hypercovering `K` of
it, and the augmentation `a : Sh((C/K)_total) ⟶ Sh(C)` of Stacks 0D8B, derived global sections on
`C` are derived global sections on the total site of the inverse image:

`RΓ(C, E) = RΓ((C/K)_total, a⁻¹E)`.

The statement is an isomorphism of functors on the *unbounded* derived category of abelian
sheaves on `C`, so it holds at every object `E` with no boundedness assumption, which is the form
the source states.

No hypothesis beyond the hypercovering conditions on `K` is carried: the three inputs of the
general `CategoryTheory.SimplicialSiteSituation.Augmentation.derivedGlobalSectionsInverseImageIso`
are proved for this augmentation. The underived unit `F ⟶ a_*a⁻¹F` is invertible by
`CategoryTheory.SimplicialSemiRepresentable.isIso_situationAbelianTotalAdjunctionUnit` (Stacks
0D8E in its abelian form), `a⁻¹` of a K-injective complex computes `R a_*` by
`CategoryTheory.SimplicialSemiRepresentable.inverseImageComputesDerivedPushforward_of_hypercoveringOfTerminal`,
and the underived identity `Γ(C, a_*F) = Γ((C/K)_total, F)` is
`CategoryTheory.SimplicialSemiRepresentable.abelianTotalPushforwardGammaIso`. -/
@[stacks 0D8H "for the augmentation of Tag 0D8B attached to a hypercovering"]
def derivedGlobalSectionsInverseImageIsoOfHypercovering :
    Augmentation.derivedGlobalSectionsBase (Cat.of C) J.toGrothendieck ≅
      Augmentation.derivedTotalInverseImage (hypercoveringSituation J H) (Cat.of C)
          J.toGrothendieck (hypercoveringAugmentation J H) ⋙
        Augmentation.derivedGlobalSectionsTotal (hypercoveringSituation J H) :=
  Augmentation.derivedGlobalSectionsInverseImageIso _ _ _ _
    (SimplicialSemiRepresentable.isIso_situationAbelianTotalAdjunctionUnit J H)
    (SimplicialSemiRepresentable.inverseImageComputesDerivedPushforward_of_hypercoveringOfTerminal
      J H)
    (SimplicialSemiRepresentable.abelianTotalPushforwardGammaIso J.toGrothendieck
      H.toSimplicialObject)

end Stacks.CategoryTheory.Hypercovering

end
