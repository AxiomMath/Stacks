module

public import StacksFrontier.AlgebraicGeometry.CoherentFinite.Basic
public import StacksFrontier.AlgebraicGeometry.Duality.DualizingModuleSections
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.AffineLocalization
public import StacksFrontier.AlgebraicGeometry.Scheme.Points.ModuleStalkSpecialization
public import StacksFrontier.Homology.ExtendScalars.Flat
public import StacksFrontier.RingTheory.Dualizing.LocalizationTransport
import StacksCore.Tactic.StacksAttribute

/-!
# The stalk of a dualizing module is a dualizing module

Let `X` be a locally Noetherian scheme and let `ω` be a quasi-coherent `𝒪_X`-module whose
complex `ω[n]` in some degree is a dualizing complex on `X` ([Stacks, Tag 0A87]). Then at every
point `x` the stalk `ω_x` has its degree-zero complex a dualizing complex over the local ring
`𝒪_{X, x}` ([Stacks, Tag 0A7B]).

The scheme-level predicate is connected to the ring-level one only over affine opens; that
connection is `Stacks.Duality.isDualizingComplex_single_specModule`, and what is added here is
the passage from an affine open to a point of it, which is [Stacks, Tag 0A7G] for the
localization at the corresponding prime, the stalk being that localization.

## Main results

* `Stacks.Duality.isDualizingComplex_single_stalk`: `ω_x[0]` is a dualizing complex over
  `𝒪_{X, x}`.

## Implementation notes

The stalk is the localization of the sections over an affine open neighbourhood, as a ring
(`AlgebraicGeometry.IsAffineOpen.isLocalization_stalk`) and as a module
(`AlgebraicGeometry.isLocalizedModule_germₗ`); extension of scalars along that localization is
exact, so it carries the degree-zero complex on the sections to the degree-zero complex on the
stalk, and [Stacks, Tag 0A7G] in the form
`Dualizing.isDualizingComplex_extendScalars_of_isLocalization` carries the dualizing property.

The module of sections appears in two spellings: `Γ(ω, U)`, which the localization statement for
the germ map uses, and `Stacks.AlgebraicGeometry.CoherentTFAE.specModule`, the sections read on
`Spec Γ(X, U)`, which the affine-open dualizing statement uses. They are identified by
`Stacks.AlgebraicGeometry.CoherentFinite.specSectionsEquiv`.

## References

* [Stacks Project, Tag 0A7B](https://stacks.math.columbia.edu/tag/0A7B)
* [Stacks Project, Tag 0A87](https://stacks.math.columbia.edu/tag/0A87)
* [Stacks Project, Tag 0A7G](https://stacks.math.columbia.edu/tag/0A7G)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.CoherentTFAE

universe u w

namespace Stacks.Duality

/-- **An exact functor of module categories carries a module in degree zero to a module in
degree zero.** -/
def mapDerivedCategorySingleZeroIso {R : Type u} {A : Type u} [CommRing R] [CommRing A]
    (F : ModuleCat.{u} R ⥤ ModuleCat.{u} A) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] (M : ModuleCat.{u} R) :
    letI := HasDerivedCategory.standard (ModuleCat.{u} R)
    letI := HasDerivedCategory.standard (ModuleCat.{u} A)
    F.mapDerivedCategory.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (F.obj M) := by
  letI := HasDerivedCategory.standard (ModuleCat.{u} R)
  letI := HasDerivedCategory.standard (ModuleCat.{u} A)
  set S := (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M with hS
  have hcomm : ∀ i : ℤ,
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj (F.mapDerivedCategory.obj S) ≅
        F.obj ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj S) :=
    fun i => (StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso F i).app S
  refine (DerivedCategory.nonempty_iso_singleFunctor_homologyFunctor_of_isZero
    (F.mapDerivedCategory.obj S) 0 (fun j hj => ?_)).some ≪≫
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).mapIso
        (hcomm 0 ≪≫ F.mapIso ((DerivedCategory.singleFunctorCompHomologyFunctorIso
          (ModuleCat.{u} R) 0).app M))
  refine IsZero.of_iso (F.map_isZero ?_) (hcomm j)
  exact Dualizing.isZero_homology_of_iso_single.{u, u} S 0 M ⟨Iso.refl _⟩ j hj

variable {X : Scheme.{u}} [IsLocallyNoetherian X] [HasDerivedCategory.{w} X.Modules]

/-- **The stalk of a dualizing module is a dualizing module.** -/
theorem isDualizingComplex_single_stalk (ω : X.Modules) [ω.IsQuasicoherent] (n : ℤ)
    (hω : IsDualizingComplex ((DerivedCategory.singleFunctor X.Modules n).obj ω)) (x : X) :
    letI := Stacks.ModuleStalkSpecialization.stalkModule ω x
    letI := HasDerivedCategory.standard (ModuleCat.{u} (X.presheaf.stalk x))
    Dualizing.IsDualizingComplex
      ((DerivedCategory.singleFunctor (ModuleCat.{u} (X.presheaf.stalk x)) 0).obj
        (ModuleCat.of (X.presheaf.stalk x) (ω.presheaf.stalk x))) := by
  let := Stacks.ModuleStalkSpecialization.stalkModule ω x
  let := HasDerivedCategory.standard (ModuleCat.{u} (X.presheaf.stalk x))
  -- An affine open neighbourhood of `x`, and the prime it defines.
  obtain ⟨-, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let := HasDerivedCategory.standard (ModuleCat.{u} Γ(X, U))
  set p := (hU.primeIdealOf ⟨x, hxU⟩).asIdeal with hp
  let : p.IsPrime := (hU.primeIdealOf ⟨x, hxU⟩).isPrime
  let : Algebra Γ(X, U) (X.presheaf.stalk x) :=
    (X.presheaf.germ U x hxU).hom.toAlgebra
  let : IsLocalization.AtPrime (X.presheaf.stalk x) p := hU.isLocalization_stalk ⟨x, hxU⟩
  -- The sections over `U` are a dualizing module, and the stalk is their localization.
  have hM := isDualizingComplex_single_specModule ω n hω U hU
  -- Extension of scalars along the localization is exact.
  have hflat : (algebraMap Γ(X, U) (X.presheaf.stalk x)).Flat :=
    RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat (X.presheaf.stalk x) p.primeCompl)
  let : (ModuleCat.extendScalars.{u, u, u}
      (algebraMap Γ(X, U) (X.presheaf.stalk x))).Additive :=
    extendScalars_additive.{u, u} _
  let : PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u}
      (algebraMap Γ(X, U) (X.presheaf.stalk x))) :=
    extendScalars_preservesFiniteLimits_of_flat'.{u, u} _ hflat
  let : PreservesColimitsOfSize.{u, u} (ModuleCat.extendScalars.{u, u, u}
      (algebraMap Γ(X, U) (X.presheaf.stalk x))) :=
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} _).leftAdjoint_preservesColimits
  let : PreservesFiniteColimits (ModuleCat.extendScalars.{u, u, u}
      (algebraMap Γ(X, U) (X.presheaf.stalk x))) :=
    PreservesColimitsOfSize.preservesFiniteColimits _
  -- The stalk is the base change of the sections.
  let := Stacks.ModuleStalkSpecialization.sectionsStalkModule ω hxU
  let := Stacks.ModuleStalkSpecialization.isScalarTower_sectionsStalk ω hxU
  have hbase : IsBaseChange (X.presheaf.stalk x)
      ((Stacks.ModuleStalkSpecialization.germₗ ω hxU).comp
        ((Stacks.AlgebraicGeometry.CoherentFinite.specSectionsEquiv ω hU :
            specModule ω hU ≃ₗ[Γ(X, U)] Γ(ω, U)) :
          specModule ω hU →ₗ[Γ(X, U)] Γ(ω, U))) :=
    (isLocalizedModule_iff_isBaseChange p.primeCompl _ _).mp
      (IsLocalizedModule.of_linearEquiv_right (S := p.primeCompl)
        (f := Stacks.ModuleStalkSpecialization.germₗ ω hxU)
        (Stacks.AlgebraicGeometry.CoherentFinite.specSectionsEquiv ω hU)
        (hf := Stacks.ModuleStalkSpecialization.isLocalizedModule_germₗ ω hU hxU))
  have hstalk : (ModuleCat.extendScalars.{u, u, u}
        (algebraMap Γ(X, U) (X.presheaf.stalk x))).obj (specModule ω hU) ≅
      ModuleCat.of (X.presheaf.stalk x) (ω.presheaf.stalk x) :=
    hbase.equiv.toModuleIso
  exact ringIsDualizingComplex_of_iso
    (mapDerivedCategorySingleZeroIso _ (specModule ω hU) ≪≫
      (DerivedCategory.singleFunctor (ModuleCat.{u} (X.presheaf.stalk x)) 0).mapIso hstalk)
    (Dualizing.isDualizingComplex_extendScalars_of_isLocalization p.primeCompl _ hM)

end Stacks.Duality

end
