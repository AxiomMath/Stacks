module

public import StacksFrontier.AlgebraicGeometry.DerivedTildeCounit
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.DerivedSectionsLocality

/-!
# Presenting a complex with quasi-coherent cohomology on an affine open

Let `X` be a scheme, `E` an object of `D(𝒪_X)` all of whose cohomology sheaves are
quasi-coherent, and `U` an affine open of `X`. The restriction `E|_U` is the complex of
quasi-coherent sheaves attached to `RΓ(Spec Γ(X, U), E|_U)`, the derived global sections of `E|_U`
read on the spectrum.

## Main definitions

* `AlgebraicGeometry.IsAffineOpen.derivedRestrictSpec`: `E|_U` carried to `Spec Γ(X, U)` along
  `AlgebraicGeometry.IsAffineOpen.isoSpec`.
* `AlgebraicGeometry.IsAffineOpen.derivedSectionsSpec`: `RΓ(Spec Γ(X, U), E|_U)`.

## Main results

* `AlgebraicGeometry.isQuasicoherent_homology_mapDerivedCategory`: quasi-coherence of every
  cohomology sheaf is inherited along an exact functor of sheaves of modules that preserves
  quasi-coherence, and hence
  (`AlgebraicGeometry.isQuasicoherent_homology_restrictFunctor_mapDerivedCategory`) along
  restriction to an open subscheme.
* `AlgebraicGeometry.IsAffineOpen.nonempty_iso_derivedTilde_derivedSectionsSpec`: `E|_U` is the
  sheaf associated to `RΓ(Spec Γ(X, U), E|_U)`, transported to `U` along `isoSpec`.
* `AlgebraicGeometry.affineDerivedSectionsPresentation_of_isQuasicoherent_homology`:
  `AlgebraicGeometry.AffineDerivedSectionsPresentation E` holds, granted that
  `RΓ(Spec Γ(X, U), E|_U)` is `RΓ(U, E)` on every affine open `U`.
* `AlgebraicGeometry.derivedSectionsPseudoCoherentComparison'_of_derivedSectionsSpec`: granted
  that same identification, the three conditions of Stacks 09VF on relative pseudo-coherence are
  equivalent.

## References

* [The Stacks Project, Lemma 36.3.5 (06Z0)](https://stacks.math.columbia.edu/tag/06Z0)
* [The Stacks Project, Lemma 36.61.8 (09VF)](https://stacks.math.columbia.edu/tag/09VF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty TopologicalSpace
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

universe u

attribute [local instance 10000] HasDerivedCategory.standard

section Quasicoherent

variable {X Y : Scheme.{u}}

/-- **Quasi-coherent cohomology is inherited along an exact functor preserving
quasi-coherence.** If `F` from `𝒪_X`-modules to `𝒪_Y`-modules is exact and carries quasi-coherent
modules to quasi-coherent modules, and every cohomology sheaf of `E` is quasi-coherent, then
every cohomology sheaf of `D(F) E` is. -/
public theorem isQuasicoherent_homology_mapDerivedCategory (F : X.Modules ⥤ Y.Modules)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (hF : ∀ M : X.Modules, M.IsQuasicoherent → (F.obj M).IsQuasicoherent)
    {E : DerivedCategory X.Modules}
    (hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj E).IsQuasicoherent)
    (i : ℤ) :
    ((DerivedCategory.homologyFunctor Y.Modules i).obj
      (F.mapDerivedCategory.obj E)).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso
    ((StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso F i).app E).symm
    (hF _ (hE i))

/-- **Quasi-coherent cohomology is inherited by the restriction to an open subscheme.** For an
open immersion `g : Y ⟶ X` and an object `E` of `D(𝒪_X)` whose cohomology sheaves are all
quasi-coherent, the cohomology sheaves of `E|_Y` are all quasi-coherent. -/
public theorem isQuasicoherent_homology_restrictFunctor_mapDerivedCategory (g : Y ⟶ X)
    [IsOpenImmersion g] {E : DerivedCategory X.Modules}
    (hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj E).IsQuasicoherent)
    (i : ℤ) :
    ((DerivedCategory.homologyFunctor Y.Modules i).obj
      ((Scheme.Modules.restrictFunctor g).mapDerivedCategory.obj E)).IsQuasicoherent :=
  isQuasicoherent_homology_mapDerivedCategory (Scheme.Modules.restrictFunctor g)
    (fun _ _ ↦ inferInstance) hE i

end Quasicoherent

namespace IsAffineOpen

variable {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U) (E : DerivedCategory X.Modules)

/-- The restriction of `E` to an affine open `U`, carried to `Spec Γ(X, U)` along
`AlgebraicGeometry.IsAffineOpen.isoSpec`. -/
public abbrev derivedRestrictSpec : DerivedCategory (Spec Γ(X, U)).Modules :=
  (Scheme.Modules.restrictFunctor hU.isoSpec.inv).mapDerivedCategory.obj
    ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj E)

/-- `RΓ(Spec Γ(X, U), E|_U)`: the derived global sections, over `Γ(X, U)`, of the restriction of
`E` to an affine open `U` read on `Spec Γ(X, U)`. -/
public abbrev derivedSectionsSpec : DerivedCategory (ModuleCat.{u} Γ(X, U)) :=
  (derivedGlobalSectionsOver (𝟙 (Spec Γ(X, U)))).obj (hU.derivedRestrictSpec E)

/-- **The cohomology sheaves of `E|_U`, read on `Spec Γ(X, U)`, are quasi-coherent**, when those
of `E` are. -/
public theorem isQuasicoherent_homology_derivedRestrictSpec
    (hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj E).IsQuasicoherent)
    (i : ℤ) :
    ((DerivedCategory.homologyFunctor (Spec Γ(X, U)).Modules i).obj
      (hU.derivedRestrictSpec E)).IsQuasicoherent :=
  isQuasicoherent_homology_restrictFunctor_mapDerivedCategory hU.isoSpec.inv
    (isQuasicoherent_homology_restrictFunctor_mapDerivedCategory U.ι hE) i

/-- **`E|_U` is presented by its derived global sections.** Let `E` be an object of the derived
category of `𝒪_X`-modules all of whose cohomology sheaves are quasi-coherent, and let `U` be an
affine open of `X`. Then `E|_U` is isomorphic to the complex of quasi-coherent sheaves attached to
`RΓ(Spec Γ(X, U), E|_U)`, transported from `Spec Γ(X, U)` to `U` along
`AlgebraicGeometry.IsAffineOpen.isoSpec`. -/
public theorem nonempty_iso_derivedTilde_derivedSectionsSpec
    (hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj E).IsQuasicoherent) :
    Nonempty ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj E ≅
      (Scheme.Modules.pushforward hU.isoSpec.inv).mapDerivedCategory.obj
        ((tilde.functor Γ(X, U)).mapDerivedCategory.obj (hU.derivedSectionsSpec E))) := by
  have hcounit := derivedTildeGlobalSectionsAdjunction_counit_isIso Γ(X, U)
    ⟨hU.derivedRestrictSpec E, hU.isQuasicoherent_homology_derivedRestrictSpec E hE⟩
  have etilde : (tilde.functor Γ(X, U)).mapDerivedCategory.obj (hU.derivedSectionsSpec E) ≅
      hU.derivedRestrictSpec E :=
    ((derivedTildeCompι Γ(X, U)).app (hU.derivedSectionsSpec E)).symm ≪≫ @asIso _ _ _ _ _ hcounit
  have ecancel : (Scheme.Modules.pushforward hU.isoSpec.inv).mapDerivedCategory.obj
      (hU.derivedRestrictSpec E) ≅
      (Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj E :=
    (Functor.mapDerivedCategoryCompIsoOfCompIso
        (Scheme.Modules.restrictFunctorCompPushforwardIso hU.isoSpec.inv)).app _ ≪≫
      (Functor.mapDerivedCategoryId (U.toScheme).Modules).app _
  exact ⟨ecancel.symm ≪≫
    (Scheme.Modules.pushforward hU.isoSpec.inv).mapDerivedCategory.mapIso etilde.symm⟩

end IsAffineOpen

section Comparison

variable {X S : Scheme.{u}}

/-- For an object `E` of `D(𝒪_X)` with quasi-coherent cohomology sheaves,
`AlgebraicGeometry.AffineDerivedSectionsPresentation E` holds as soon as `RΓ(Spec Γ(X, U), E|_U)`
is `RΓ(U, E)` on every affine open `U`. -/
public theorem affineDerivedSectionsPresentation_of_isQuasicoherent_homology
    (E : DerivedCategory X.Modules)
    (hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj E).IsQuasicoherent)
    (hΓ : ∀ (U : X.Opens) (hU : IsAffineOpen U),
      Nonempty (hU.derivedSectionsSpec E ≅ (derivedSectionsUnbounded X U).obj E)) :
    AffineDerivedSectionsPresentation E := fun U hU ↦
  ⟨hU.derivedSectionsSpec E, hU.nonempty_iso_derivedTilde_derivedSectionsSpec E hE, hΓ U hU⟩

/-- **Relative pseudo-coherence is detected on affine opens, granted that derived global sections
on the spectrum of an affine open are the derived sections over that open.** For `f : X ⟶ S`
locally of finite type, `E` an object of the derived category of `𝒪_X`-modules all of whose
cohomology sheaves are quasi-coherent, and `m` an integer, the three conditions of Stacks 09VF —
relative `m`-pseudo-coherence of `E`, the same for `RΓ(U, E)` over the members of some pair of
nested affine open coverings, and the same over every compatible pair of affine opens — are
equivalent. -/
public theorem derivedSectionsPseudoCoherentComparison'_of_derivedSectionsSpec (f : X ⟶ S)
    [LocallyOfFiniteType f] (E : DerivedCategory X.Modules)
    (hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj E).IsQuasicoherent)
    (hΓ : ∀ (U : X.Opens) (hU : IsAffineOpen U),
      Nonempty (hU.derivedSectionsSpec E ≅ (derivedSectionsUnbounded X U).obj E))
    (m : ℤ) :
    DerivedSectionsPseudoCoherentComparison' f E hE m :=
  derivedSectionsPseudoCoherentComparison'_of_affinePresentation f E hE
    (affineDerivedSectionsPresentation_of_isQuasicoherent_homology E hE hΓ) m

end Comparison

end AlgebraicGeometry

end
