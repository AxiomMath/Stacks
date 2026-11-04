module

public import StacksFrontier.AlgebraicGeometry.Spaces.FlatAffineCohomologyCollapse
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSpellingBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.CategoryTheory.Abelian.RightDerivedPostcompose
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.GlobalSectionsAndPushforward
import StacksCore.Tactic.StacksAttribute

/-!
# The pullback map on module cohomology along a flat affine morphism of algebraic spaces

For a flat affine morphism `f : X ⟶ Y` of algebraic spaces and a quasi-coherent `𝒪_Y`-module `𝓖`,
this file constructs the canonical `Γ(Y, 𝒪_Y)`-linear map `H^i(Y, 𝓖) ⟶ H^i(X, f^*𝓖)`: `H^i(Y, −)`
of the unit `𝓖 ⟶ f_*f^*𝓖`, followed by the inverse of the identification of `H^i(X, f^*𝓖)` with
`H^i(Y, f_*f^*𝓖)`. Cohomology is the right derived functor of global sections on the small étale
ringed site.

## Main definitions

* `AlgebraicGeometry.Space.globalSectionsRingHomSite`: the ring map `Γ(Y, 𝒪_Y) ⟶ Γ(X, 𝒪_X)`.
* `AlgebraicGeometry.Space.globalSectionsRestrictScalars`: restriction of scalars along it.
* `AlgebraicGeometry.Space.globalSectionsPushforwardIsoSite`: `Γ(Y, f_*−) ≅ Γ(X, −)`, with
  scalars restricted.
* `AlgebraicGeometry.Space.derivedGlobalSectionsPushforwardIso`: `R^i Γ(Y, f_*−) ≅ R^i Γ(X, −)`,
  with scalars restricted.
* `AlgebraicGeometry.Space.cohomologyPushforwardIsoOfIsFlatOfIsAffineHom`: for a flat affine `f`
  and a quasi-coherent `𝓕`, `H^i(X, 𝓕) ≅ H^i(Y, f_*𝓕)` as `Γ(Y, 𝒪_Y)`-modules.
* `AlgebraicGeometry.Space.cohomologyPullbackMap`: the `Γ(Y, 𝒪_Y)`-linear map
  `H^i(Y, 𝓖) ⟶ H^i(X, f^*𝓖)`.

## Main results

* `AlgebraicGeometry.Space.cohomologyPullbackMap_fac`: followed by the identification of
  `H^i(X, f^*𝓖)` with `H^i(Y, f_*f^*𝓖)`, the pullback map is `H^i(Y, −)` applied to the unit
  `𝓖 ⟶ f_*f^*𝓖`.

## References

* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
* [Stacks Project, Tag 0733](https://stacks.math.columbia.edu/tag/0733)
* [Stacks Project, Tag 0732](https://stacks.math.columbia.edu/tag/0732)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 073E](https://stacks.math.columbia.edu/tag/073E)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cohomology.SiteModules

attribute [local instance 5000] SheafOfModules.instAbelian

noncomputable section

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-- The ring map `Γ(Y, 𝒪_Y) ⟶ Γ(X, 𝒪_X)` attached to a morphism `f : X ⟶ Y` of algebraic
spaces, with source and target the global sections of the structure ring sheaf of the small étale
ringed site. -/
def globalSectionsRingHomSite (f : X ⟶ Y) :
    RingCat.sectionsSubring
        (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O).obj →+*
      RingCat.sectionsSubring
        (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).obj :=
  globalSectionsRingHom (X := smallEtaleRingedTopos B S hS X)
    (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposModulesHom B S hS f)

/-- Restriction of scalars along the ring map `Γ(Y, 𝒪_Y) ⟶ Γ(X, 𝒪_X)` attached to `f`. -/
abbrev globalSectionsRestrictScalars (f : X ⟶ Y) :
    ModuleCat.{u + 1} (RingCat.sectionsSubring
        (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).obj) ⥤
      ModuleCat.{u + 1} (RingCat.sectionsSubring
        (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O).obj) :=
  ModuleCat.restrictScalars (globalSectionsRingHomSite B S hS f)

/-- Restriction of scalars along the ring map `Γ(Y, 𝒪_Y) ⟶ Γ(X, 𝒪_X)` preserves homology. -/
instance preservesHomology_globalSectionsRestrictScalars (f : X ⟶ Y) :
    (globalSectionsRestrictScalars B S hS f).PreservesHomology where
  preservesKernels _ := inferInstance
  preservesCokernels _ := inferInstance

/-- Global sections on `Y` of the direct image along `f : X ⟶ Y` are global sections on `X`, with
scalars restricted along the ring map `Γ(Y, 𝒪_Y) ⟶ Γ(X, 𝒪_X)`. -/
def globalSectionsPushforwardIsoSite (f : X ⟶ Y) :
    modulePushforward B S hS f ⋙ globalSectionsFunctor.{u + 1, u, u, u}
          (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O) ≅
      globalSectionsFunctor.{u + 1, u, u, u}
          (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O) ⋙
        globalSectionsRestrictScalars B S hS f :=
  Functor.isoWhiskerRight (modulePushforwardIso B S hS f).symm _ ≪≫
    globalSectionsPushforwardIso (smallEtaleRingedToposModulesHom B S hS f)

/-- For a morphism `f : X ⟶ Y` of algebraic spaces, `R^i Γ(Y, f_*−) ≅ R^i Γ(X, −)`, with the
scalars of the right-hand side restricted along the ring map `Γ(Y, 𝒪_Y) ⟶ Γ(X, 𝒪_X)`. -/
def derivedGlobalSectionsPushforwardIso (f : X ⟶ Y) (i : ℕ) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    ((modulePushforward B S hS f ⋙ globalSectionsFunctor.{u + 1, u, u, u}
          (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)).rightDerived i ≅
      (globalSectionsFunctor.{u + 1, u, u, u}
          (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).rightDerived i ⋙
        globalSectionsRestrictScalars B S hS f) :=
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  Functor.rightDerivedIsoOfNatIso (globalSectionsPushforwardIsoSite B S hS f) i ≪≫
    @Functor.rightDerivedCompIso _ _ _ _ _ _ _ _ _ _
      (globalSectionsFunctor.{u + 1, u, u, u}
        (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)) _
      (globalSectionsRestrictScalars B S hS f) _ _ i

/-- For a flat affine `f : X ⟶ Y` and a quasi-coherent `𝒪_X`-module `𝓕`, `H^i(X, 𝓕) ≅ H^i(Y, f_*𝓕)`
in every degree, as `Γ(Y, 𝒪_Y)`-modules, the scalars of the left-hand side being restricted along
the ring map `Γ(Y, 𝒪_Y) ⟶ Γ(X, 𝒪_X)`. -/
@[stacks 0733 "part (1), for a flat affine morphism of algebraic spaces on the small étale
  ringed sites, as a chosen isomorphism and with nothing carried"]
def cohomologyPushforwardIsoOfIsFlatOfIsAffineHom (f : X ⟶ Y) (haff : IsAffineHom B S hS f.hom)
    (hflat : IsFlat B S hS f.hom) (F : Modules.{u, u} B S hS X.1 X.2)
    (hF : F.IsQuasicoherentOnSite) (i : ℕ) :
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
    cohomologyCollapseIsoOfIsFlatOfIsAffineHom B S hS f haff hflat F hF i

/-- For a flat affine `f : X ⟶ Y` and a quasi-coherent `𝒪_Y`-module `𝓖`, the `Γ(Y, 𝒪_Y)`-linear
map `H^i(Y, 𝓖) ⟶ H^i(X, f^*𝓖)`: `H^i(Y, −)` of the unit `𝓖 ⟶ f_*f^*𝓖`, followed by the inverse of
the identification of `H^i(X, f^*𝓖)` with `H^i(Y, f_*f^*𝓖)`. -/
def cohomologyPullbackMap (f : X ⟶ Y) (haff : IsAffineHom B S hS f.hom)
    (hflat : IsFlat B S hS f.hom) (G : Modules.{u, u} B S hS Y.1 Y.2)
    (hG : G.IsQuasicoherentOnSite) (i : ℕ) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    have := enoughInjectives_modules B S hS Y.1 Y.2
    (((globalSectionsFunctor.{u + 1, u, u, u}
          (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)).rightDerived i).obj G ⟶
      (globalSectionsRestrictScalars B S hS f).obj
        (((globalSectionsFunctor.{u + 1, u, u, u}
            (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).rightDerived i).obj
          ((modulePullback B S hS f).obj G))) :=
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  have := enoughInjectives_modules B S hS Y.1 Y.2
  ((globalSectionsFunctor.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)).rightDerived i).map
      ((modulePullbackAdjunction B S hS f).unit.app G) ≫
    (cohomologyPushforwardIsoOfIsFlatOfIsAffineHom B S hS f haff hflat
      ((modulePullback B S hS f).obj G)
      (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS f G hG) i).inv

/-- `AlgebraicGeometry.Space.cohomologyPullbackMap` unfolded. -/
theorem cohomologyPullbackMap_eq (f : X ⟶ Y) (haff : IsAffineHom B S hS f.hom)
    (hflat : IsFlat B S hS f.hom) (G : Modules.{u, u} B S hS Y.1 Y.2)
    (hG : G.IsQuasicoherentOnSite) (i : ℕ) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    have := enoughInjectives_modules B S hS Y.1 Y.2
    cohomologyPullbackMap B S hS f haff hflat G hG i =
      ((globalSectionsFunctor.{u + 1, u, u, u}
            (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)).rightDerived i).map
          ((modulePullbackAdjunction B S hS f).unit.app G) ≫
        (cohomologyPushforwardIsoOfIsFlatOfIsAffineHom B S hS f haff hflat
          ((modulePullback B S hS f).obj G)
          (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS f G hG) i).inv :=
  rfl

/-- Followed by the identification of `H^i(X, f^*𝓖)` with `H^i(Y, f_*f^*𝓖)`, the pullback map
`AlgebraicGeometry.Space.cohomologyPullbackMap` is `H^i(Y, −)` applied to the unit
`𝓖 ⟶ f_*f^*𝓖`. -/
theorem cohomologyPullbackMap_fac (f : X ⟶ Y) (haff : IsAffineHom B S hS f.hom)
    (hflat : IsFlat B S hS f.hom) (G : Modules.{u, u} B S hS Y.1 Y.2)
    (hG : G.IsQuasicoherentOnSite) (i : ℕ) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    have := enoughInjectives_modules B S hS Y.1 Y.2
    cohomologyPullbackMap B S hS f haff hflat G hG i ≫
        (cohomologyPushforwardIsoOfIsFlatOfIsAffineHom B S hS f haff hflat
          ((modulePullback B S hS f).obj G)
          (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS f G hG) i).hom =
      ((globalSectionsFunctor.{u + 1, u, u, u}
          (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)).rightDerived i).map
        ((modulePullbackAdjunction B S hS f).unit.app G) := by
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  have := enoughInjectives_modules B S hS Y.1 Y.2
  rw [cohomologyPullbackMap_eq, Category.assoc, Iso.inv_hom_id, Category.comp_id]

end AlgebraicGeometry.Space

end

end
