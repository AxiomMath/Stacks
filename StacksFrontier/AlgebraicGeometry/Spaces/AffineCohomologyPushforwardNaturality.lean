module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineMorphismCohomologyIso
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatAffineCohomologyPullback
public import StacksFrontier.Homology.CompositeCollapseAcyclicImageNaturality

/-!
# The cohomology of a direct image along an affine morphism, naturally and linearly

For an affine morphism `f : X ⟶ Y` of algebraic spaces and a quasi-coherent `𝒪_X`-module `𝓕`,
Stacks 0D2U identifies `H^i(X, 𝓕)` with `H^i(Y, f_*𝓕)`. This file gives that identification as an
isomorphism of `Γ(Y, 𝒪_Y)`-modules (scalars on the left restricted along `Γ(Y, 𝒪_Y) ⟶ Γ(X, 𝒪_X)`),
natural in `𝓕`, with no flatness hypothesis.

## Main definitions

* `AlgebraicGeometry.Space.cohomologyPushforwardLinearIsoOfIsAffineHom`: the isomorphism.

## Main results

* `AlgebraicGeometry.Space.cohomologyCollapseIsoOfChartwise_hom_naturality`: the Leray collapse
  along a representable morphism is natural in the coefficient.
* `AlgebraicGeometry.Space.cohomologyCollapseIsoOfIsAffineHom_hom_comp_map`: the same along an
  affine morphism.
* `AlgebraicGeometry.Space.cohomologyPushforwardLinearIsoOfIsAffineHom_hom_naturality`: the
  isomorphism is natural in the quasi-coherent coefficient.
* `AlgebraicGeometry.Space.cohomologyPushforwardIsoOfIsFlatOfIsAffineHom_hom_naturality`: the
  same for the flat form `AlgebraicGeometry.Space.cohomologyPushforwardIsoOfIsFlatOfIsAffineHom`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.SiteModules
open Stacks.SheafOfModules.Tensor (ringSheaf)

attribute [local instance 5000] SheafOfModules.instAbelian

noncomputable section

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-- **The Leray collapse along a representable morphism is natural in the coefficient.** -/
theorem cohomologyCollapseIsoOfChartwise_hom_naturality (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) {F F' : Modules.{u, u} B S hS X.1 X.2}
    (h03DW : ∀ n, 0 < n → ChartwiseIsZeroHigherDirectImage B S hS f hf F n)
    (h03DW' : ∀ n, 0 < n → ChartwiseIsZeroHigherDirectImage B S hS f hf F' n)
    (h072Z : AcyclicPushforwardOfInjective B S hS f) (g : F ⟶ F') (i : ℕ) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    have := enoughInjectives_modules B S hS Y.1 Y.2
    ((modulePushforward B S hS f ⋙ globalSectionsFunctor.{u + 1, u, u, u}
          (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)).rightDerived i).map g ≫
        (cohomologyCollapseIsoOfChartwise B S hS f hf F' h03DW' h072Z i).hom =
      (cohomologyCollapseIsoOfChartwise B S hS f hf F h03DW h072Z i).hom ≫
        ((globalSectionsFunctor.{u + 1, u, u, u}
          (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)).rightDerived i).map
          ((modulePushforward B S hS f).map g) := by
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  have := enoughInjectives_modules B S hS Y.1 Y.2
  have := preservesFiniteLimits_globalSectionsFunctor_structureRingSheaf B S hS Y.1 Y.2
  exact Stacks.RightDerivedComp.objIsoOfAcyclicImage_naturality_rightDerived _ _
    (fun n hn => isZero_rightDerived_modulePushforward_of_chartwise B S hS f hf F n (h03DW n hn))
    (fun n hn => isZero_rightDerived_modulePushforward_of_chartwise B S hS f hf F' n
      (h03DW' n hn)) h072Z g i

/-- **The Leray collapse along an affine morphism is natural in the coefficient.** -/
theorem cohomologyCollapseIsoOfIsAffineHom_hom_comp_map (f : X ⟶ Y)
    (haff : IsAffineHom B S hS f.hom) {F F' : Modules.{u, u} B S hS X.1 X.2}
    (h03DW : ∀ n, 0 < n → ChartwiseIsZeroHigherDirectImage B S hS f
      (relativelyRepresentable_of_isAffineHom B S hS f haff) F n)
    (h03DW' : ∀ n, 0 < n → ChartwiseIsZeroHigherDirectImage B S hS f
      (relativelyRepresentable_of_isAffineHom B S hS f haff) F' n)
    (h072Z : AcyclicPushforwardOfInjective B S hS f) (g : F ⟶ F') (i : ℕ) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    have := enoughInjectives_modules B S hS Y.1 Y.2
    ((modulePushforward B S hS f ⋙ globalSectionsFunctor.{u + 1, u, u, u}
          (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)).rightDerived i).map g ≫
        (cohomologyCollapseIsoOfIsAffineHom B S hS f haff F' h03DW' h072Z i).hom =
      (cohomologyCollapseIsoOfIsAffineHom B S hS f haff F h03DW h072Z i).hom ≫
        ((globalSectionsFunctor.{u + 1, u, u, u}
          (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)).rightDerived i).map
          ((modulePushforward B S hS f).map g) :=
  cohomologyCollapseIsoOfChartwise_hom_naturality B S hS f
    (relativelyRepresentable_of_isAffineHom B S hS f haff) h03DW h03DW' h072Z g i

/-- **Stacks 0D2U as an isomorphism of `Γ(Y, 𝒪_Y)`-modules.** For an affine `f : X ⟶ Y` and a
quasi-coherent `𝓕`, `H^i(X, 𝓕) ≅ H^i(Y, f_*𝓕)`, the left hand side read over `Γ(Y, 𝒪_Y)`. -/
def cohomologyPushforwardLinearIsoOfIsAffineHom (f : X ⟶ Y) (haff : IsAffineHom B S hS f.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite) (i : ℕ) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    have := enoughInjectives_modules B S hS Y.1 Y.2
    ((globalSectionsRestrictScalars B S hS f).obj
        (((globalSectionsFunctor.{u + 1, u, u, u}
          (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).rightDerived i).obj F) ≅
      ((globalSectionsFunctor.{u + 1, u, u, u}
          (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)).rightDerived i).obj
        ((modulePushforward B S hS f).obj F)) :=
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  have := enoughInjectives_modules B S hS Y.1 Y.2
  ((derivedGlobalSectionsPushforwardIso B S hS f i).app F).symm ≪≫
    cohomologyCollapseIsoOfIsAffineHom B S hS f haff F
      (fun n hn => chartwiseIsZeroHigherDirectImage_of_isAffineHom B S hS f haff
        (relativelyRepresentable_of_isAffineHom B S hS f haff) F hF n hn)
      (acyclicPushforwardOfInjective B S hS f) i

/-- **The isomorphism of Stacks 0D2U is natural in the quasi-coherent coefficient.** -/
theorem cohomologyPushforwardLinearIsoOfIsAffineHom_hom_naturality (f : X ⟶ Y)
    (haff : IsAffineHom B S hS f.hom) {F F' : Modules.{u, u} B S hS X.1 X.2}
    (hF : F.IsQuasicoherentOnSite) (hF' : F'.IsQuasicoherentOnSite) (g : F ⟶ F') (i : ℕ) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    have := enoughInjectives_modules B S hS Y.1 Y.2
    (globalSectionsRestrictScalars B S hS f).map
        (((globalSectionsFunctor.{u + 1, u, u, u}
          (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).rightDerived i).map g) ≫
        (cohomologyPushforwardLinearIsoOfIsAffineHom B S hS f haff F' hF' i).hom =
      (cohomologyPushforwardLinearIsoOfIsAffineHom B S hS f haff F hF i).hom ≫
        ((globalSectionsFunctor.{u + 1, u, u, u}
          (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)).rightDerived i).map
          ((modulePushforward B S hS f).map g) := by
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  have := enoughInjectives_modules B S hS Y.1 Y.2
  have h := chartwiseIsZeroHigherDirectImage_of_isAffineHom B S hS f haff
    (relativelyRepresentable_of_isAffineHom B S hS f haff)
  exact (reassoc_of% (derivedGlobalSectionsPushforwardIso B S hS f i).inv.naturality g) _ |>.trans
    (congrArg (_ ≫ ·) (cohomologyCollapseIsoOfIsAffineHom_hom_comp_map B S hS f haff
      (h F hF) (h F' hF') (acyclicPushforwardOfInjective B S hS f) g i)) |>.trans
    (Category.assoc _ _ _).symm

/-- **The flat form of Stacks 0D2U is natural in the quasi-coherent coefficient.** -/
theorem cohomologyPushforwardIsoOfIsFlatOfIsAffineHom_hom_naturality (f : X ⟶ Y)
    (haff : IsAffineHom B S hS f.hom) (hflat : IsFlat B S hS f.hom)
    {F F' : Modules.{u, u} B S hS X.1 X.2}
    (hF : F.IsQuasicoherentOnSite) (hF' : F'.IsQuasicoherentOnSite) (g : F ⟶ F') (i : ℕ) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    have := enoughInjectives_modules B S hS Y.1 Y.2
    (globalSectionsRestrictScalars B S hS f).map
        (((globalSectionsFunctor.{u + 1, u, u, u}
          (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).rightDerived i).map g) ≫
        (cohomologyPushforwardIsoOfIsFlatOfIsAffineHom B S hS f haff hflat F' hF' i).hom =
      (cohomologyPushforwardIsoOfIsFlatOfIsAffineHom B S hS f haff hflat F hF i).hom ≫
        ((globalSectionsFunctor.{u + 1, u, u, u}
          (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)).rightDerived i).map
          ((modulePushforward B S hS f).map g) :=
  cohomologyPushforwardLinearIsoOfIsAffineHom_hom_naturality B S hS f haff hF hF' g i

end AlgebraicGeometry.Space

end
