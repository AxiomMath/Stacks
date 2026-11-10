module

public import Mathlib.RingTheory.LocalProperties.Exactness
public import Mathlib.RingTheory.Localization.Module
public import StacksFrontier.AlgebraicGeometry.AssociatedPointPrime.Basic
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.DerivedStalk
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.DegreeZeroCohomology
public import StacksFrontier.AlgebraicGeometry.QcohLimits.Sections

/-!
# Invertibility over an affine open is detected by the stalks

Let `X` be a scheme, `U ⊆ X` an affine open and `A = Γ(X, U)`. For a quasi-coherent
`𝒪_X`-module `F` the germ map `Γ(F, U) → F_x` at a point `x ∈ U` exhibits the stalk as the
localization of `Γ(F, U)` at the prime of `x`, and every prime of `A` arises this way. Localized
at a prime, the germ map carries the map on sections of a morphism `ψ : F ⟶ G` to the map on
stalks; since a map of modules is bijective exactly when all of its localizations are, the map
`Γ(F, U) → Γ(G, U)` is bijective exactly when `ψ` is an isomorphism on every stalk at a point
of `U`.

The same statement in the derived category reads: for `K, L ∈ D(𝒪_X)` whose degree-`n`
cohomology sheaves are quasi-coherent and `φ : K ⟶ L`, the map `Γ(U, Hⁿ(φ))` is bijective
exactly when `Hⁿ` of the derived stalk of `φ` is invertible at every point of `U`. On an affine
scheme the left-hand side is `Hⁿ(RΓ(Spec R, φ))`, the cohomology of derived global sections
being the global sections of cohomology for complexes with quasi-coherent cohomology; so
invertibility of `Hⁿ(RΓ(Spec R, φ))` is a pointwise condition on derived stalks.

## Main results

All names are in the namespace `Stacks.StalkLocalization`.

* `bijective_iff_forall_bijective_localizedMap`: a map of modules is bijective exactly when all
  of its localizations at primes are. This is the local criterion of [Stacks, Tag 00HN] (6).
* `exists_point_primeIdealOf`: every prime of `Γ(X, U)`, for `U` an affine open, is the prime of
  a point of `U`.
* `isLocalizedModule_map_eq_stalkMapₗ`: the localization of the map on sections over an affine
  open is the map on stalks.
* `bijective_appₗ_iff_forall_bijective_stalkMap`: for quasi-coherent modules, the map on
  sections over an affine open is bijective exactly when the map on stalks is bijective at every
  point of that open.
* `bijective_appₗ_homology_iff`: the same for the degree-`n` cohomology sheaves of a morphism of
  the derived category, with the stalk condition read as invertibility of `Hⁿ` of the derived
  stalk.
* `isIso_homology_derivedGlobalSections_iff`: on an affine scheme, `Hⁿ(RΓ(Spec R, φ))` is
  invertible exactly when `Hⁿ` of the derived stalk of `φ` is invertible at every point.

## Implementation notes

The germ map and its localization property are
`Stacks.AlgebraicGeometry.AssociatedPointPrime.germₗ` and `isLocalizedModule_germₗ`; the map on
sections is `Stacks.AlgebraicGeometry.QcohLimits.appₗ`. The two scalar actions on a stalk — over
`𝒪_{X,x}` and over `Γ(X, U)` through the germ map — agree by definition, which is what lets the
map on stalks be read as a `Γ(X, U)`-linear map.

The model of the derived category is a binder, `[HasDerivedCategory.{w} ·]`, for the sheaves of
modules and for every stalk ring.

## References

* [Stacks Project, Tag 00HN](https://stacks.math.columbia.edu/tag/00HN)
* [Stacks Project, Tag 01HV](https://stacks.math.columbia.edu/tag/01HV)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.AlgebraicGeometry.AssociatedPointPrime
open Stacks.AlgebraicGeometry.QcohLimits

universe u w

namespace Stacks.StalkLocalization

/-! ### The local criterion -/

/-- **A map of modules is bijective exactly when all of its localizations are.** This is the
local criterion of [Stacks, Tag 00HN] (6), stated at all primes. -/
theorem bijective_iff_forall_bijective_localizedMap {R : Type u} [CommRing R]
    {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (F : M →ₗ[R] N) :
    Function.Bijective F ↔
      ∀ (p : Ideal R) [p.IsPrime],
        Function.Bijective (LocalizedModule.map p.primeCompl F) :=
  ⟨fun hF _ _ => ⟨LocalizedModule.map_injective _ _ hF.1, LocalizedModule.map_surjective _ _ hF.2⟩,
    fun h => bijective_of_localized_maximal F fun J hJ => @h J hJ.isPrime⟩

/-- The local criterion with the primes of `R` presented as points of `Spec R`. -/
theorem bijective_iff_forall_bijective_localizedMap' {R : Type u} [CommRing R]
    {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (F : M →ₗ[R] N) :
    Function.Bijective F ↔
      ∀ p : PrimeSpectrum R,
        Function.Bijective (LocalizedModule.map p.asIdeal.primeCompl F) := by
  rw [bijective_iff_forall_bijective_localizedMap]
  exact ⟨fun h p => @h p.asIdeal p.isPrime, fun h p hp => h ⟨p, hp⟩⟩

/-- **Any two localizations of a map agree on bijectivity.** The localization of `F` at `S`
computed in `LocalizedModule` is bijective exactly when the one computed through arbitrary
localization maps `g₁, g₂` is. -/
theorem bijective_localizedModule_map_iff {R : Type u} [CommRing R]
    {M N M' N' : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup M'] [Module R M'] [AddCommGroup N'] [Module R N']
    (S : Submonoid R) (F : M →ₗ[R] N) (g₁ : M →ₗ[R] M') (g₂ : N →ₗ[R] N')
    [IsLocalizedModule S g₁] [IsLocalizedModule S g₂] :
    Function.Bijective (LocalizedModule.map S F) ↔
      Function.Bijective (IsLocalizedModule.map S g₁ g₂ F) := by
  rw [LocalizedModule.coe_map_eq g₁ g₂ F, EquivLike.comp_bijective, EquivLike.bijective_comp]

/-! ### Sections over an affine open and stalks -/

variable {X : Scheme.{u}}

/-- **The map on stalks of a morphism of `𝒪_X`-modules, as a `Γ(X, U)`-linear map** for a point
`x` of an open `U`, the module structures being those obtained by restricting scalars along the
germ map `Γ(X, U) → 𝒪_{X,x}`. -/
def stalkMapₗ {K L : X.Modules} (ψ : K ⟶ L) {U : X.Opens} {x : X} (hx : x ∈ U) :
    letI := sectionsStalkModule K hx
    letI := sectionsStalkModule L hx
    K.presheaf.stalk x →ₗ[Γ(X, U)] L.presheaf.stalk x :=
  letI := sectionsStalkModule K hx
  letI := sectionsStalkModule L hx
  { toFun := ((Stacks.ModuleSkyscraper.modulesStalkFunctor X x).map ψ).hom
    map_add' := fun a b => map_add _ a b
    map_smul' := fun r m =>
      ((Stacks.ModuleSkyscraper.modulesStalkFunctor X x).map ψ).hom.map_smul
        ((X.presheaf.germ U x hx) r) m }

/-- The germ map is natural: the map on stalks of `ψ` carries the germ of a section to the germ
of its image. -/
theorem stalkMapₗ_germₗ {K L : X.Modules} (ψ : K ⟶ L) {U : X.Opens} {x : X} (hx : x ∈ U)
    (m : Γ(K, U)) :
    letI := sectionsStalkModule K hx
    letI := sectionsStalkModule L hx
    stalkMapₗ ψ hx (germₗ K hx m) = germₗ L hx (appₗ ψ U m) :=
  Stacks.ModuleSkyscraper.stalkMapLinear_germ
    ((SheafOfModules.forget X.ringCatSheaf).map ψ) x U hx m

/-- **Every prime of the sections over an affine open is the prime of a point of that open.** -/
theorem exists_point_primeIdealOf {U : X.Opens} (hU : IsAffineOpen U)
    (p : PrimeSpectrum Γ(X, U)) :
    ∃ (x : X) (hx : x ∈ U), hU.primeIdealOf ⟨x, hx⟩ = p := by
  obtain ⟨y, hy⟩ :=
    (ConcreteCategory.bijective_of_isIso (Scheme.forgetToTop.map hU.isoSpec.hom)).2 p
  exact ⟨y.1, y.2, hy⟩

/-- **The localization of the map on sections is the map on stalks.** -/
theorem isLocalizedModule_map_eq_stalkMapₗ {K L : X.Modules} (ψ : K ⟶ L) {U : X.Opens}
    {x : X} (hx : x ∈ U) (S : Submonoid Γ(X, U)) :
    letI := sectionsStalkModule K hx
    letI := sectionsStalkModule L hx
    ∀ [IsLocalizedModule S (germₗ K hx)] [IsLocalizedModule S (germₗ L hx)],
      IsLocalizedModule.map S (germₗ K hx) (germₗ L hx) (appₗ ψ U) = stalkMapₗ ψ hx := by
  let := sectionsStalkModule K hx
  let := sectionsStalkModule L hx
  intro _ _
  refine IsLocalizedModule.linearMap_ext S (germₗ K hx) (germₗ L hx) ?_
  ext m
  change IsLocalizedModule.map S (germₗ K hx) (germₗ L hx) (appₗ ψ U) (germₗ K hx m) = _
  rw [IsLocalizedModule.map_apply]
  exact (stalkMapₗ_germₗ ψ hx m).symm

/-- **Invertibility over an affine open is detected by the stalks.** For quasi-coherent
`𝒪_X`-modules `K` and `L` and an affine open `U`, the map on sections
`Γ(K, U) → Γ(L, U)` induced by `ψ : K ⟶ L` is bijective exactly when the map on stalks is
bijective at every point of `U`. -/
theorem bijective_appₗ_iff_forall_bijective_stalkMap {K L : X.Modules}
    [K.IsQuasicoherent] [L.IsQuasicoherent] (ψ : K ⟶ L) {U : X.Opens} (hU : IsAffineOpen U) :
    Function.Bijective (appₗ ψ U) ↔
      ∀ x : X, x ∈ U →
        Function.Bijective ((Stacks.ModuleSkyscraper.modulesStalkFunctor X x).map ψ) := by
  have key (x : X) (hx : x ∈ U) :
      Function.Bijective
          (LocalizedModule.map (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl (appₗ ψ U)) ↔
        Function.Bijective ((Stacks.ModuleSkyscraper.modulesStalkFunctor X x).map ψ) := by
    let := sectionsStalkModule K hx
    let := sectionsStalkModule L hx
    have := isLocalizedModule_germₗ K hU hx
    have := isLocalizedModule_germₗ L hU hx
    rw [bijective_localizedModule_map_iff _ _ (germₗ K hx) (germₗ L hx),
      isLocalizedModule_map_eq_stalkMapₗ ψ hx _]
    exact Iff.rfl
  rw [bijective_iff_forall_bijective_localizedMap']
  refine ⟨fun h x hx => (key x hx).1 (h _), fun h p => ?_⟩
  obtain ⟨x, hx, rfl⟩ := exists_point_primeIdealOf hU p
  exact (key x hx).2 (h x hx)

/-! ### The criterion in the derived category -/

/-- **Invertibility of the cohomology of a morphism of the derived category over an affine open
is detected by the derived stalks.** For `K, L ∈ D(𝒪_X)` whose degree-`n` cohomology sheaves are
quasi-coherent and `φ : K ⟶ L`, the map on sections over an affine open `U` of `Hⁿ(φ)` is
bijective exactly when `Hⁿ` of the derived stalk of `φ` is invertible at every point of `U`. -/
theorem bijective_appₗ_homology_iff [HasDerivedCategory.{w} X.Modules]
    [∀ y : X, HasDerivedCategory.{w} (ModuleCat.{u} (X.presheaf.stalk y))]
    {K L : DerivedCategory X.Modules} (φ : K ⟶ L) (n : ℤ)
    [((DerivedCategory.homologyFunctor X.Modules n).obj K).IsQuasicoherent]
    [((DerivedCategory.homologyFunctor X.Modules n).obj L).IsQuasicoherent]
    {U : X.Opens} (hU : IsAffineOpen U) :
    Function.Bijective (appₗ ((DerivedCategory.homologyFunctor X.Modules n).map φ) U) ↔
      ∀ x : X, x ∈ U → IsIso ((DerivedCategory.homologyFunctor
        (ModuleCat.{u} (X.presheaf.stalk x)) n).map ((derivedStalkFunctor x).map φ)) := by
  rw [bijective_appₗ_iff_forall_bijective_stalkMap _ hU]
  refine forall_congr' fun x => imp_congr_right fun _ => ?_
  have hx : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} (X.presheaf.stalk x)) n).map
        ((derivedStalkFunctor x).map φ)) ↔
      IsIso ((Stacks.ModuleSkyscraper.modulesStalkFunctor X x).map
        ((DerivedCategory.homologyFunctor X.Modules n).map φ)) :=
    Functor.isIso_homologyFunctor_map_mapDerivedCategory_map_iff _ φ n
  rw [hx, ConcreteCategory.isIso_iff_bijective]

/-! ### The affine case -/

section Affine

variable (R : CommRingCat.{u})

/-- A morphism of `𝒪_{Spec R}`-modules is carried to an isomorphism by `R`-linear global
sections exactly when its map on global sections is bijective. -/
theorem isIso_globalSectionsOver_map_iff {K L : (Spec R).Modules} (ψ : K ⟶ L) :
    IsIso ((globalSectionsOver (𝟙 (Spec R))).map ψ) ↔
      Function.Bijective (appₗ ψ ⊤) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  exact Iff.rfl

/-- **The cohomology of derived global sections on an affine scheme is invertible exactly when
all derived stalks are.** For `E, F ∈ D_QCoh(𝒪_{Spec R})` and `φ : E ⟶ F`, the map
`Hⁿ(RΓ(Spec R, φ))` of `R`-modules is an isomorphism exactly when `Hⁿ` of the derived stalk of
`φ` is an isomorphism at every point of `Spec R`. -/
theorem isIso_homology_derivedGlobalSections_iff (n : ℤ)
    {E F : (DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
      (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).FullSubcategory} (φ : E ⟶ F) :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).map
        ((derivedGlobalSectionsQuasicoherent R).map φ)) ↔
      ∀ x : Spec R, IsIso ((DerivedCategory.homologyFunctor
        (ModuleCat.{u} ((Spec R).presheaf.stalk x)) n).map
          ((derivedStalkFunctor x).map ((DerivedCategoryB.derivedCategoryB
            (A := (Spec R).Modules)
            (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).ι.map φ))) := by
  have hq (G : (DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
      (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).FullSubcategory) :
      ((DerivedCategory.homologyFunctor (Spec R).Modules n).obj
        ((DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
          (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).ι.obj G)).IsQuasicoherent :=
    G.property n
  have := hq E
  have := hq F
  refine (NatIso.isIso_map_iff (derivedGlobalSectionsQuasicoherentCompHomologyIso R n) φ).trans ?_
  rw [Functor.comp_map, Functor.comp_map, isIso_globalSectionsOver_map_iff,
    bijective_appₗ_homology_iff ((DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
      (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).ι.map φ) n
      (isAffineOpen_top (Spec R))]
  exact ⟨fun h x => h x trivial, fun h x _ => h x⟩

end Affine

end Stacks.StalkLocalization

end
