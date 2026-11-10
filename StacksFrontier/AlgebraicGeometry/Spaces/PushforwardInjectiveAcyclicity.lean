module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartCohomologyVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineMorphismCohomologyCollapse
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineMorphismCohomologyIso
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineMorphismHigherDirectImageVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeRestrictionEtalePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.InjectivePushforwardAcyclicity
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleEssentiallySmall
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Acyclicity.TotallyAcyclicAnySite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Acyclicity.TotallyAcyclicGlobalSectionsLargeSite

/-!
# The direct image of an injective module along a morphism of algebraic spaces is acyclic

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf site
`B`, and let `𝓘` be an injective `𝒪_X`-module. This file proves that `f_*𝓘` has no higher
cohomology on `Y`: it is acyclic for the global sections functor of `𝒪_Y`-modules on the small
étale site of `Y`. That is Stacks 072Z read through part (3) of Stacks 0731, and it is exactly
the hypothesis `h072Z` — `AlgebraicGeometry.Space.AcyclicPushforwardOfInjective` — carried by
the library's form of Stacks 0D2U. With it and Stacks 073H, Stacks 0D2U holds
unconditionally.

## Main results

* `AlgebraicGeometry.Space.isTotallyAcyclic_modulePushforward_of_injective`: the abelian sheaf
  underlying `f_*𝓘` is totally acyclic — **Stacks 072Z** for the small étale ringed topoi of
  algebraic spaces.
* `AlgebraicGeometry.Space.acyclicPushforwardOfInjective`: **the hypothesis `h072Z`,
  discharged**, for every morphism of algebraic spaces.
* `AlgebraicGeometry.Space.chartwiseIsZeroHigherDirectImage_of_isQuasicoherent`: **the
  hypothesis `h03DW`, discharged** for an affine morphism and a quasi-coherent module.
* `AlgebraicGeometry.Space.cohomologyCollapseIsoOfIsAffineHomOfIsQuasicoherent`: the collapse
  isomorphism `H^i(X, 𝓕) = H^i(Y, f_*𝓕)` for an affine morphism `f` and a quasi-coherent `𝓕`,
  in every degree, with no hypothesis: `AlgebraicGeometry.Space.cohomologyCollapseIsoOfIsAffineHom`
  with `h03DW` and `h072Z` discharged.

## Implementation notes

*Why the library's general form of Stacks 072Z does not apply.* The small étale site of an algebraic
space over a `Scheme.{u}` has its objects in `Type (u + 1)` and its morphisms, structure sheaf and
modules at `u`. `Stacks.Cohomology.isTotallyAcyclic_pushforwardModules_of_injective` needs a source
ringed topos with all three universes equal, and
`Stacks.Cohomology.isTotallyAcyclic_rightAcyclic_globalSections` needs a small site. Both
obstructions are removed without any universe transport:
`Stacks.Cohomology.isTotallyAcyclic_abelianPushforward_of_injective` is Stacks 072Z for a morphism
of topoi whose source site need not be small, and
`GlobalSectionsLargeSite.isZero_rightDerived_globalSectionsFunctor_of_isTotallyAcyclic`, in the
namespace `Stacks.Cohomology`, is part (3) of Stacks 0731 on such a site.

*The adjunction data.* `AlgebraicGeometry.Space.smallEtaleRingedToposHom` is an
`AlgebraicGeometry.RingedToposHom`, which records the structure map in its direct-image form
only. That is no obstruction: Stacks 072Z uses only the underlying morphism of topoi, with its
inverse image and the adjunction `f⁻¹ ⊣ f_*`, and that morphism of topoi,
`AlgebraicGeometry.Space.smallToposMorphismTypeU`, carries both. The sheaf of sets underlying
`f_*𝓘` is, on the nose, the direct image along it of the sheaf of sets underlying `𝓘`, so the
two abelian sheaves are identified by
`Stacks.Cohomology.abelianSheafNatIsoOfUnderlying` applied to the identity.

*Quasi-coherence.* The acyclicity of `f_*𝓘` holds for every morphism of algebraic spaces and
every injective `𝓘`. Quasi-coherence of `𝓕` enters the collapse isomorphism only through the
vanishing of the higher direct images, Stacks 073H,
`AlgebraicGeometry.Space.isZero_rightDerived_modulePushforward_of_isAffineHom_of_isQuasicoherent`.

## References

* [Stacks Project, Lemma 21.14.1 (Tag 072Z)](https://stacks.math.columbia.edu/tag/072Z)
* [Stacks Project, Lemma 21.14.3 (Tag 0731)](https://stacks.math.columbia.edu/tag/0731)
* [Stacks Project, Lemma 69.6.3 (Tag 0D2U)](https://stacks.math.columbia.edu/tag/0D2U)
* [Stacks Project, Lemma 69.3.3 (Tag 073H)](https://stacks.math.columbia.edu/tag/073H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open Stacks.Cohomology.SiteModules Stacks.Topos.AbelianPushforward

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance] AlgebraicGeometry.Space.enoughInjectives_sheaf_smallEtale
  AlgebraicGeometry.Space.hasExt_sheaf_smallEtale
  AlgebraicGeometry.Space.enoughInjectives_sheaf_smallEtaleRingedSite
  AlgebraicGeometry.Space.hasExt_sheaf_smallEtaleRingedSite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-- The abelian sheaf underlying the direct image of an `𝒪_X`-module along a morphism of
algebraic spaces is the direct image, along the morphism of small étale topoi
`AlgebraicGeometry.Space.smallToposMorphismTypeU`, of the abelian sheaf underlying the module.
The underlying sheaves of sets agree on the nose. -/
def toSheafModulePushforwardIso (f : X ⟶ Y) :
    modulePushforward B S hS f ⋙ SheafOfModules.toSheaf
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)) ≅
      SheafOfModules.toSheaf
          ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)) ⋙
        Stacks.Topos.AbelianPushforward.abelianPushforward (smallEtaleRingedSite B S hS X.1 X.2).J
          (smallToposMorphismTypeU B S hS f) := by
  have := modulePushforward_additive B S hS f
  have : (SheafOfModules.toSheaf
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS Y.1 Y.2).O))).Additive :=
    { map_add := rfl }
  have hF : (modulePushforward B S hS f ⋙ SheafOfModules.toSheaf
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS Y.1 Y.2).O))).Additive :=
    Functor.instAdditiveComp _ _
  have : (SheafOfModules.toSheaf
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O))).Additive :=
    { map_add := rfl }
  have : (Stacks.Topos.AbelianPushforward.abelianPushforward (smallEtaleRingedSite B S hS X.1 X.2).J
      (smallToposMorphismTypeU B S hS f)).Additive :=
    Stacks.Topos.AbelianPushforward.abelianPushforward_additive _ _
  have hG : (SheafOfModules.toSheaf
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)) ⋙
        Stacks.Topos.AbelianPushforward.abelianPushforward (smallEtaleRingedSite B S hS X.1 X.2).J
          (smallToposMorphismTypeU B S hS f)).Additive :=
    Functor.instAdditiveComp _ _
  exact @Stacks.Cohomology.abelianSheafNatIsoOfUnderlying _ _ _ _ _ _
    (smallEtaleRingedSite B S hS Y.1 Y.2).J _ _ hF hG (Iso.refl _)

/-- **The hypothesis `h03DW` of `AlgebraicGeometry.Space.cohomologyCollapseIsoOfIsAffineHom`
and `AlgebraicGeometry.Space.isZero_rightDerived_modulePushforward_of_isAffineHom`, discharged**
for a quasi-coherent module. Let `f : X ⟶ Y` be an affine morphism of algebraic spaces over `S`
and `𝓕` a quasi-coherent `𝒪_X`-module. For every étale scheme chart `V` of `Y`, the base change
`f' : V ×_Y X ⟶ V` has vanishing higher direct images on `𝓕|_{V ×_Y X}` in every positive
degree. -/
theorem chartwiseIsZeroHigherDirectImage_of_isQuasicoherent (f : X ⟶ Y)
    (hf : IsAffineHom B S hS f.hom) (F : Modules.{u, u} B S hS X.1 X.2)
    (hF : F.IsQuasicoherentOnSite) (n : ℕ) (hn : 0 < n) :
    ChartwiseIsZeroHigherDirectImage B S hS f (relativelyRepresentable_of_isAffineHom B S hS f hf)
      F n := fun V =>
  isZero_rightDerived_modulePushforward_of_isAffineHom_of_isQuasicoherent B S hS
    (smallBaseChangeChartMap B S hS f (relativelyRepresentable_of_isAffineHom B S hS f hf) V)
    (IsAffineHom.of_isPullback (AlgebraicSpaces.isPullback_hom _ _ _
      (isPullback_smallBaseChangeChart B S hS f
        (relativelyRepresentable_of_isAffineHom B S hS f hf) V)) hf)
    _ (isQuasicoherentOnSite_etaleModulePullback_chartToSpace B S hS X F hF _) n hn

/-- **The collapse of Stacks 0D2U, with no hypothesis.** Let `f : X ⟶ Y` be an affine morphism
of algebraic spaces over `S` and `𝓕` a quasi-coherent `𝒪_X`-module. Then the cohomology of `𝓕`
on `X` — computed as the derived functor of `Γ(Y, f_* −)` — is the cohomology of `f_*𝓕` on `Y`,
in every degree.

This is `AlgebraicGeometry.Space.cohomologyCollapseIsoOfIsAffineHom` with both of its carried
hypotheses discharged: the vanishing of the higher direct images is Stacks 073H,
`AlgebraicGeometry.Space.isZero_rightDerived_modulePushforward_of_isAffineHom_of_isQuasicoherent`,
and the acyclicity of the direct image of an injective is
`AlgebraicGeometry.Space.acyclicPushforwardOfInjective`. -/
def cohomologyCollapseIsoOfIsAffineHomOfIsQuasicoherent (f : X ⟶ Y)
    (hf : IsAffineHom B S hS f.hom) (F : Modules.{u, u} B S hS X.1 X.2)
    (hF : F.IsQuasicoherentOnSite) (i : ℕ) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    have := enoughInjectives_modules B S hS Y.1 Y.2
    (((modulePushforward B S hS f ⋙ globalSectionsFunctor.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS Y.1 Y.2).O))).rightDerived i).obj F ≅
      ((globalSectionsFunctor.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS Y.1 Y.2).O))).rightDerived i).obj
        ((modulePushforward B S hS f).obj F)) :=
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  have := enoughInjectives_modules B S hS Y.1 Y.2
  have := preservesFiniteLimits_globalSectionsFunctor_structureRingSheaf B S hS Y.1 Y.2
  Stacks.RightDerivedComp.objIsoOfAcyclicImage _ _
    (fun n hn => isZero_rightDerived_modulePushforward_of_isAffineHom_of_isQuasicoherent
      B S hS f hf F hF n hn)
    (acyclicPushforwardOfInjective B S hS f) i

end AlgebraicGeometry.Space
