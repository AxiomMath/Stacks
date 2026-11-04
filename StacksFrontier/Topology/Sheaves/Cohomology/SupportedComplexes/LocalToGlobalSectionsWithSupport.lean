module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.RestrictionOfModules
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.SectionsWithSupport
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.SupportedSectionsDerivedAdjunction
import StacksCore.Tactic.StacksAttribute

/-!
# Local-to-global sections with support in a closed subset

Let `Z` be a closed subset of a ringed space `X`, let `𝒪_X|_Z` be the restricted structure
sheaf and let `i : (Z, 𝒪_X|_Z) ⟶ (X, 𝒪_X)` be the inclusion.  Taking global sections on `Z` of
the sheaf `H_Z(F)` of sections of `F` supported on `Z` is the same as taking the global sections
of `F` supported on `Z`:

`Γ(Z, H_Z(-)) = Γ_Z(X, -)` as functors `Mod(𝒪_X) ⥤ Mod(𝒪_X(X))`.

Deriving this identity gives **Stacks 0G70**, `RΓ(Z, -) ∘ RH_Z = RΓ_Z(X, -)` as functors
`D(𝒪_X) ⥤ D(𝒪_X(X))`.  The source writes an equality of functors; the two functors are not
literally equal, so the content is the *canonical natural isomorphism* between them, and
canonicity is the point: it is recorded by `derivedSectionsWithSupportIso_hom_fac` and pinned by
`derivedSectionsWithSupportIso_hom_unique`.

## Main definitions

* `closedSubspaceGlobalSections`: the functor `Γ(Z, -) : Mod(𝒪_X|_Z) ⥤ Mod(𝒪_X(X))` of global
  sections on the closed subspace with their `𝒪_X(X)`-module structure, realized as pushforward
  along `i` followed by evaluation on `X`.
* `globalCounit`: the counit of the adjunction `i_* ⊣ H_Z` of Stacks 0G6P, read on global
  sections: `Γ(Z, H_Z(F)) ⟶ Γ(X, F)`.
* `localToGlobalComparison`, `localToGlobalIso`: the underived comparison
  `Γ(Z, H_Z(-)) ⟶ Γ_Z(X, -)`, obtained from `globalCounit` by the universal property of the
  kernel `Γ_Z(X, -) = ker (Γ(X, -) ⟶ Γ(X ∖ Z, -))`, and the isomorphism that it is.
* `localToGlobalUnit`: the canonical comparison exhibiting `RH_Z` followed by `RΓ(Z, -)` as a
  right derived functor of `Γ_Z(X, -)`.

## Main results

* `isRightDerivedFunctor_derivedSupportedSectionsOnClosed_comp`: the composite of `RH_Z` with a
  right derived functor of `Γ(Z, -)` *is* a right derived functor of `Γ_Z(X, -)`, with
  comparison `localToGlobalUnit`.
* `derivedSectionsWithSupportIso`: **Stacks 0G70**, the canonical natural isomorphism
  `RΓ(Z, -) ∘ RH_Z ≅ RΓ_Z(X, -)`.
* `derivedSectionsWithSupportIso_hom_fac` and `derivedSectionsWithSupportIso_hom_unique`: the
  isomorphism of Stacks 0G70 is the unique transformation compatible with the comparisons to the
  underived functors, which is what makes it the canonical one.

## Implementation notes

The proof is the source's: a right derived functor is computed on K-injective resolutions, `H_Z`
preserves K-injectivity (Stacks 0G6Z,
`Stacks.Cohomology.SupportedComplexes.isKInjective_supportedSectionsOnClosed`), and underived
`Γ_Z(X, -) = Γ(Z, -) ∘ H_Z`.  Concretely,
`Stacks.Cohomology.Localization.rightDerived_of_kInjectives` reduces the first main result to the
invertibility of `localToGlobalUnit` at a K-injective complex `I`, where it is a composite of the
comparison of `RH_Z` at `I`, invertible because `I` is K-injective, and the comparison of
`RΓ(Z, -)` at `H_Z(I)`, invertible because `H_Z(I)` is K-injective.  The two derived functors are
quantified over rather than fixed, following the convention of Stacks 0G71 in
`Stacks.Cohomology.SectionsWithSupport`; `Stacks.Cohomology.Localization` supplies models of both.

The underived identification is not a bare isomorphism either.  `Γ_Z(X, F)` is by construction
the kernel of restriction to the complement of `Z`, and the comparison into it is the
factorization of the 0G6P counit `i_* H_Z(F) ⟶ F` read on global sections; `counit_app_eq`
records that this counit is the inclusion of the supported-sections subsheaf, and
`localToGlobalComparison_comp_kernelι` records the factorization.  That the factorization is an
isomorphism is the sections-level statement
`restriction_eq_zero_iff_suppSection_subset`: a global section dies on `X ∖ Z` exactly when its
support (Tag 01AT) lies in `Z`.

## References

* [Stacks Project, Lemma 20.34.4 (Tag 0G70)](https://stacks.math.columbia.edu/tag/0G70)
* [Stacks Project, Lemma 20.34.3 (Tag 0G6Z)](https://stacks.math.columbia.edu/tag/0G6Z)
* [Stacks Project, Lemma 17.13.6 (Tag 0G6P)](https://stacks.math.columbia.edu/tag/0G6P)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.SheafOfModules.SupportedSections
open Stacks.Cohomology.SectionsWithSupport
open Stacks.Cohomology.SupportedComplexes

universe u

namespace Stacks.Cohomology.LocalToGlobalSupport

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSpace.{u, u}) (Z : Set X) (hZ : IsClosed Z)

/-! ### Global sections on the closed subspace -/

/-- Modules over the restricted structure sheaf `𝒪_X|_Z` of a closed subset `Z`. -/
abbrev ClosedModuleSheaves :=
  _root_.SheafOfModules.{u} (structureSheafRing (closedSubsetRingedSpace X Z))

/-- The functor `Γ(Z, -) : Mod(𝒪_X|_Z) ⥤ Mod(𝒪_X(X))` of global sections on the closed subspace
`(Z, 𝒪_X|_Z)`, with the `𝒪_X(X)`-module structure obtained by restricting scalars along
`𝒪_X(X) ⟶ (𝒪_X|_Z)(Z)`.  Both are realized at once by pushing forward along the inclusion
`i : (Z, 𝒪_X|_Z) ⟶ (X, 𝒪_X)` and evaluating on `X`, since `(i_* A)(X) = A(Z)`. -/
def closedSubspaceGlobalSections :
    ClosedModuleSheaves X Z ⥤ GlobalModules X :=
  modulePushforward (closedSubsetInclusion X Z) ⋙
    SheafOfModules.evaluation (structureSheafRing X) (op ⊤)

/-- Global sections on the closed subspace form an additive functor. -/
instance localToGlobal_closedSubspaceGlobalSections_additive :
    (closedSubspaceGlobalSections X Z).Additive where
  map_add := rfl

/-! ### The underived identity `Γ(Z, H_Z(-)) = Γ_Z(X, -)` -/

/-- A global section restricts to zero on `X ∖ Z` exactly when its support is contained in `Z`:
the germ at a point of the complement of the restriction is the germ of the section, and a
section all of whose germs vanish is zero. -/
theorem restriction_eq_zero_iff_suppSection_subset (F : ModuleSheaves X)
    (s : F.val.presheaf.obj (op ⊤)) :
    F.val.presheaf.map (homOfLE (le_top : openComplement Z hZ ≤ ⊤)).op s = 0 ↔
      (AlgebraicGeometry.SheafOfModules.moduleSheafOfModules F).suppSection ⊤ s ⊆ Z := by
  set G := AlgebraicGeometry.SheafOfModules.moduleSheafOfModules F
  have hgerm : ∀ x (hxU : x ∈ openComplement Z hZ),
      G.abPresheaf.germ (openComplement Z hZ) x hxU
        (F.val.presheaf.map (homOfLE (le_top : openComplement Z hZ ≤ ⊤)).op s) =
      G.abPresheaf.germ ⊤ x (Opens.mem_top x) s := fun x hxU =>
    TopCat.Presheaf.germ_res_apply (F := G.abPresheaf)
      (homOfLE (le_top : openComplement Z hZ ≤ ⊤)) x hxU s
  refine ⟨fun hs x ⟨hxTop, hxne⟩ => ?_, fun hs => ?_⟩
  · by_contra hxZ
    have h1 := hgerm x hxZ
    rw [hs] at h1
    exact hxne (h1.symm.trans (map_zero _))
  · refine TopCat.Presheaf.section_ext ⟨F.val.presheaf, F.isSheaf⟩
      (openComplement Z hZ) _ 0 fun x hxU => ?_
    rw [map_zero]
    exact (hgerm x hxU).trans (not_not.1 fun hne => hxU (hs ⟨Opens.mem_top x, hne⟩))

/-- The inclusion of the subsheaf of sections supported on `Z`, as a natural transformation
`H_Z^{sheaf} ⟶ id` of endofunctors of `Mod(𝒪_X)`. -/
def supportedSectionsι : supportedSectionsFunctor X Z ⟶ Functor.id (ModuleSheaves X) where
  app F := supportedSectionsSheafι Z F
  naturality _ _ f := supportedSectionsSheafι_naturality Z f

/-- Restriction to the complement of `Z` kills every global section of the subsheaf of sections
supported on `Z`. -/
theorem supportedSections_comp_restriction (F : ModuleSheaves X) :
    (SheafOfModules.evaluation (structureSheafRing X) (op ⊤)).map ((supportedSectionsι X Z).app F) ≫
      (restrictionToComplement X Z hZ).app F = 0 := by
  ext t
  show F.val.presheaf.map (homOfLE (le_top : openComplement Z hZ ≤ ⊤)).op
      ((supportedSectionsSheafι Z F).val.app (op ⊤) t) = 0
  refine (restriction_eq_zero_iff_suppSection_subset X Z hZ F _).2 ?_
  exact ((mem_supportedSectionsSheafι_range_iff Z F (op ⊤) _).1 ⟨t, rfl⟩).trans
    Set.inter_subset_left

/-- The comparison from the global sections of the subsheaf of sections supported on `Z` to the
kernel of restriction to the complement of `Z`. -/
def globalSupportedSectionsToKernel (F : ModuleSheaves X) :
    (SheafOfModules.evaluation (structureSheafRing X) (op ⊤)).obj
        ((supportedSectionsFunctor X Z).obj F) ⟶
      kernel ((restrictionToComplement X Z hZ).app F) :=
  kernel.lift _ ((SheafOfModules.evaluation (structureSheafRing X) (op ⊤)).map
    ((supportedSectionsι X Z).app F)) (supportedSections_comp_restriction X Z hZ F)

/-- The comparison `globalSupportedSectionsToKernel` followed by the kernel inclusion is the
inclusion of the supported-sections subsheaf on global sections. -/
@[reassoc (attr := simp)]
theorem globalSupportedSectionsToKernel_comp_kernelι (F : ModuleSheaves X) :
    globalSupportedSectionsToKernel X Z hZ F ≫
        kernel.ι ((restrictionToComplement X Z hZ).app F) =
      (SheafOfModules.evaluation (structureSheafRing X) (op ⊤)).map
        ((supportedSectionsι X Z).app F) :=
  kernel.lift_ι _ _ _

/-- The global sections of the subsheaf of sections supported on `Z` *are* the global sections
killed by restriction to the complement: the comparison is injective because the inclusion of the
subsheaf is injective on sections, and surjective by
`restriction_eq_zero_iff_suppSection_subset`. -/
instance localToGlobal_isIso_globalSupportedSectionsToKernel (F : ModuleSheaves X) :
    IsIso (globalSupportedSectionsToKernel X Z hZ F) := by
  have h : ∀ c, (kernel.ι ((restrictionToComplement X Z hZ).app F)).hom
      ((globalSupportedSectionsToKernel X Z hZ F).hom c) =
      ((SheafOfModules.evaluation (structureSheafRing X) (op ⊤)).map
        ((supportedSectionsι X Z).app F)).hom c := fun c => by
    rw [← ConcreteCategory.comp_apply, globalSupportedSectionsToKernel_comp_kernelι]
  have hmono : Function.Injective
      (kernel.ι ((restrictionToComplement X Z hZ).app F)).hom :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  refine (ConcreteCategory.isIso_iff_bijective _).2 ⟨?_, ?_⟩
  · intro a b hab
    refine (supportedSectionsSheaf Z F).2.2.1 (op ⊤) ?_
    exact (h a).symm.trans
      ((congrArg (kernel.ι ((restrictionToComplement X Z hZ).app F)).hom hab).trans (h b))
  · intro y
    have hs0 : F.val.presheaf.map (homOfLE (le_top : openComplement Z hZ ≤ ⊤)).op
        ((kernel.ι ((restrictionToComplement X Z hZ).app F)).hom y) = 0 := by
      change ((restrictionToComplement X Z hZ).app F).hom
        ((kernel.ι ((restrictionToComplement X Z hZ).app F)).hom y) = 0
      rw [← ConcreteCategory.comp_apply, kernel.condition]
      rfl
    have hsupp := (restriction_eq_zero_iff_suppSection_subset X Z hZ F _).1 hs0
    obtain ⟨t, ht⟩ := (mem_supportedSectionsSheafι_range_iff Z F (op ⊤) _).2
      (Set.subset_inter hsupp (fun x hx => hx.1))
    exact ⟨t, hmono ((h t).trans ht)⟩

/-- **The counit of Stacks 0G6P is the inclusion of the supported-sections subsheaf.** The
adjunction `i_* ⊣ H_Z` identifies `i_* H_Z(F)` with that subsheaf of `F`, and its counit at `F`
is that identification followed by the inclusion. -/
theorem counit_app_eq (F : ModuleSheaves X) :
    (modulePushforward_supportedSectionsOnClosed_adjunction X Z hZ).counit.app F =
      (supportedSectionsOnClosedFunctor_comp_modulePushforward_iso X Z hZ).hom.app F ≫
        (supportedSectionsι X Z).app F := by
  have h := (modulePushforward_supportedSectionsOnClosed_adjunction X Z hZ).homEquiv_counit
    (X := (supportedSectionsOnClosedFunctor X Z hZ).obj F) (Y := F)
    (g := 𝟙 ((supportedSectionsOnClosedFunctor X Z hZ).obj F))
  rw [CategoryTheory.Functor.map_id, Category.id_comp] at h
  rw [← h]
  show (modulePushforward (closedSubsetInclusion X Z)).map
      (𝟙 ((supportedSectionsOnClosedFunctor X Z hZ).obj F)) ≫
    (supportedSectionsOnClosedFunctor_comp_modulePushforward_iso X Z hZ).hom.app F ≫
      (supportedSectionsι X Z).app F = _
  rw [CategoryTheory.Functor.map_id, Category.id_comp]

/-- The counit `i_* H_Z(-) ⟶ id` of the adjunction of Stacks 0G6P, read on global sections:
`Γ(Z, H_Z(F)) ⟶ Γ(X, F)`. -/
def globalCounit :
    supportedSectionsOnClosedFunctor X Z hZ ⋙ closedSubspaceGlobalSections X Z ⟶
      SheafOfModules.evaluation (structureSheafRing X) (op ⊤) :=
  Functor.whiskerRight (modulePushforward_supportedSectionsOnClosed_adjunction X Z hZ).counit
    (SheafOfModules.evaluation (structureSheafRing X) (op ⊤))

/-- The component of `globalCounit` at `F` is the counit at `F` evaluated on global sections. -/
@[simp]
theorem globalCounit_app (F : ModuleSheaves X) :
    (globalCounit X Z hZ).app F = (SheafOfModules.evaluation (structureSheafRing X) (op ⊤)).map
      ((modulePushforward_supportedSectionsOnClosed_adjunction X Z hZ).counit.app F) :=
  rfl

/-- A global section of `H_Z(F)` on `Z` restricts to zero on `X ∖ Z`. -/
theorem globalCounit_comp_restriction :
    globalCounit X Z hZ ≫ restrictionToComplement X Z hZ = 0 := by
  refine NatTrans.ext (funext fun F => ?_)
  have hzero : (globalCounit X Z hZ ≫ restrictionToComplement X Z hZ).app F = 0 := by
    rw [NatTrans.comp_app, globalCounit_app, counit_app_eq, CategoryTheory.Functor.map_comp]
    refine (Category.assoc _ _ _).trans (Eq.trans (congrArg
      (fun k => (SheafOfModules.evaluation (structureSheafRing X) (op ⊤)).map
        ((supportedSectionsOnClosedFunctor_comp_modulePushforward_iso X Z hZ).hom.app F) ≫ k)
      (supportedSections_comp_restriction X Z hZ F)) comp_zero)
  rw [hzero]
  exact (NatTrans.app_zero F).symm

/-- The comparison `Γ(Z, H_Z(-)) ⟶ Γ_Z(X, -)`: the 0G6P counit on global sections factors
through the kernel of restriction to the complement, which is `Γ_Z(X, -)` by construction. -/
def localToGlobalComparison :
    supportedSectionsOnClosedFunctor X Z hZ ⋙ closedSubspaceGlobalSections X Z ⟶
      kernel (restrictionToComplement X Z hZ) :=
  kernel.lift (restrictionToComplement X Z hZ) (globalCounit X Z hZ)
    (globalCounit_comp_restriction X Z hZ)

/-- **The comparison is pinned by the 0G6P counit.** Composing `localToGlobalComparison` with
the inclusion of `Γ_Z(X, -)` into `Γ(X, -)` gives back the counit of `i_* ⊣ H_Z` on global
sections; as that inclusion is a monomorphism, this characterises the comparison. -/
@[reassoc (attr := simp)]
theorem localToGlobalComparison_comp_kernelι :
    localToGlobalComparison X Z hZ ≫ kernel.ι (restrictionToComplement X Z hZ) =
      globalCounit X Z hZ :=
  kernel.lift_ι _ _ _

/-- The comparison `Γ(Z, H_Z(F)) ⟶ Γ_Z(X, F)` is invertible at every module sheaf. -/
instance localToGlobal_isIso_localToGlobalComparison_app (F : ModuleSheaves X) :
    IsIso ((localToGlobalComparison X Z hZ).app F) := by
  have hpres : (PreservesKernel.iso ((evaluation (ModuleSheaves X) (GlobalModules X)).obj F)
          (restrictionToComplement X Z hZ)).inv ≫
        (kernel.ι (restrictionToComplement X Z hZ)).app F =
      kernel.ι ((restrictionToComplement X Z hZ).app F) :=
    PreservesKernel.iso_inv_ι ((evaluation (ModuleSheaves X) (GlobalModules X)).obj F)
      (restrictionToComplement X Z hZ)
  have hfac : (localToGlobalComparison X Z hZ).app F ≫
      (kernel.ι (restrictionToComplement X Z hZ)).app F =
      (SheafOfModules.evaluation (structureSheafRing X) (op ⊤)).map
          ((supportedSectionsOnClosedFunctor_comp_modulePushforward_iso X Z hZ).hom.app F) ≫
        (SheafOfModules.evaluation (structureSheafRing X) (op ⊤)).map
          ((supportedSectionsι X Z).app F) := by
    rw [← NatTrans.comp_app, localToGlobalComparison_comp_kernelι, globalCounit_app,
      counit_app_eq, CategoryTheory.Functor.map_comp]
  have hg : (globalSupportedSectionsToKernel X Z hZ F ≫
        (PreservesKernel.iso ((evaluation (ModuleSheaves X) (GlobalModules X)).obj F)
          (restrictionToComplement X Z hZ)).inv) ≫
        (kernel.ι (restrictionToComplement X Z hZ)).app F =
      (SheafOfModules.evaluation (structureSheafRing X) (op ⊤)).map
        ((supportedSectionsι X Z).app F) := by
    rw [Category.assoc, hpres, globalSupportedSectionsToKernel_comp_kernelι]
  have key : (localToGlobalComparison X Z hZ).app F =
      (SheafOfModules.evaluation (structureSheafRing X) (op ⊤)).map
          ((supportedSectionsOnClosedFunctor_comp_modulePushforward_iso X Z hZ).hom.app F) ≫
        (globalSupportedSectionsToKernel X Z hZ F ≫
          (PreservesKernel.iso ((evaluation (ModuleSheaves X) (GlobalModules X)).obj F)
            (restrictionToComplement X Z hZ)).inv) := by
    refine (cancel_mono ((kernel.ι (restrictionToComplement X Z hZ)).app F)).1 (hfac.trans ?_)
    exact ((Category.assoc _ _ _).trans
      (congrArg (fun k => (SheafOfModules.evaluation (structureSheafRing X) (op ⊤)).map
        ((supportedSectionsOnClosedFunctor_comp_modulePushforward_iso X Z hZ).hom.app F) ≫ k)
        hg)).symm
  have h1 : IsIso ((SheafOfModules.evaluation (structureSheafRing X) (op ⊤)).map
      ((supportedSectionsOnClosedFunctor_comp_modulePushforward_iso X Z hZ).hom.app F)) :=
    Functor.map_isIso _ _
  have h2 : IsIso (globalSupportedSectionsToKernel X Z hZ F ≫
      (PreservesKernel.iso ((evaluation (ModuleSheaves X) (GlobalModules X)).obj F)
        (restrictionToComplement X Z hZ)).inv) :=
    IsIso.comp_isIso' inferInstance (Iso.isIso_inv _)
  rw [key]
  exact IsIso.comp_isIso' h1 h2

/-- The comparison `Γ(Z, H_Z(-)) ⟶ Γ_Z(X, -)` is an isomorphism of functors. -/
instance localToGlobal_isIso_localToGlobalComparison :
    IsIso (localToGlobalComparison X Z hZ) :=
  NatIso.isIso_of_isIso_app _

/-- **The underived local-to-global identity for sections with support.** For a closed subset
`Z` of a ringed space `X`, taking global sections on `Z` of the sheaf of sections supported on
`Z` is the functor of global sections supported on `Z`:
`Γ(Z, H_Z(-)) ≅ Γ_Z(X, -)` as functors `Mod(𝒪_X) ⥤ Mod(𝒪_X(X))`.  The isomorphism is the
factorization of the counit of Stacks 0G6P through the kernel of restriction to `X ∖ Z`. -/
def localToGlobalIso :
    supportedSectionsOnClosedFunctor X Z hZ ⋙ closedSubspaceGlobalSections X Z ≅
      sectionsWithSupport X Z hZ :=
  show supportedSectionsOnClosedFunctor X Z hZ ⋙ closedSubspaceGlobalSections X Z ≅
      kernel (restrictionToComplement X Z hZ) from
    asIso (localToGlobalComparison X Z hZ)

/-! ### Deriving the identity -/

variable (RΓZ' : DerivedCategory (ClosedModuleSheaves X Z) ⥤ DerivedGlobalModules X)
  (αΓ : (closedSubspaceGlobalSections X Z).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RΓZ')

/-- The canonical comparison `Γ_Z(X, -) ⟶ RΓ(Z, RH_Z(-))` exhibiting the composite of `RH_Z`
with a right derived functor of `Γ(Z, -)` as a candidate right derived functor of `Γ_Z(X, -)`.
It is the underived identity `localToGlobalIso`, followed by the comparison of `RΓ(Z, -)` and
then the comparison of `RH_Z`. -/
def localToGlobalUnit :
    homotopyToDerived X (sectionsWithSupport X Z hZ) ⟶
      DerivedCategory.Qh ⋙ (derivedSupportedSectionsOnClosed X Z hZ ⋙ RΓZ') :=
  Functor.whiskerRight
      (Functor.mapHomotopyCategoryCompIso (localToGlobalIso X Z hZ) (ComplexShape.up ℤ)).inv
      DerivedCategory.Qh ≫
    (Functor.whiskerLeft
      ((supportedSectionsOnClosedFunctor X Z hZ).mapHomotopyCategory (ComplexShape.up ℤ)) αΓ ≫
      Functor.whiskerRight (derivedSupportedSectionsOnClosedUnit X Z hZ) RΓZ')

/-- **`RΓ(Z, -) ∘ RH_Z` is a right derived functor of `Γ_Z(X, -)`.** The comparison
`localToGlobalUnit` is invertible at a K-injective complex `I`: the comparison of `RH_Z` is
invertible there because `I` is K-injective, and the comparison of `RΓ(Z, -)` is invertible at
`H_Z(I)` because `H_Z` preserves K-injectivity (Stacks 0G6Z). -/
theorem isRightDerivedFunctor_derivedSupportedSectionsOnClosed_comp
    [RΓZ'.IsRightDerivedFunctor αΓ
      (HomotopyCategory.quasiIso (ClosedModuleSheaves X Z) (ComplexShape.up ℤ))] :
    (derivedSupportedSectionsOnClosed X Z hZ ⋙ RΓZ').IsRightDerivedFunctor
      (localToGlobalUnit X Z hZ RΓZ' αΓ)
      (HomotopyCategory.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ)) := by
  refine Stacks.Cohomology.Localization.rightDerived_of_kInjectives _ _ _ (fun I hI => ?_)
  have hH : IsIso ((derivedSupportedSectionsOnClosedUnit X Z hZ).app
      ((HomotopyCategory.quotient (ModuleSheaves X) (ComplexShape.up ℤ)).obj I)) :=
    Stacks.Cohomology.Localization.derivedUnit_isIsoOnKInjective _ _ _ I
  have hG : IsIso (αΓ.app
      (((supportedSectionsOnClosedFunctor X Z hZ).mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient (ModuleSheaves X) (ComplexShape.up ℤ)).obj I))) := by
    rw [Functor.mapHomotopyCategory_obj (supportedSectionsOnClosedFunctor X Z hZ)
      (ComplexShape.up ℤ)
      ((HomotopyCategory.quotient (ModuleSheaves X) (ComplexShape.up ℤ)).obj I)]
    have hasKI : CochainComplex.IsKInjective
        ((HomotopyCategory.quotient (ModuleSheaves X) (ComplexShape.up ℤ)).obj I).as := hI
    have hHI := isKInjective_supportedSectionsOnClosed X Z hZ
      ((HomotopyCategory.quotient (ModuleSheaves X) (ComplexShape.up ℤ)).obj I).as
    exact Stacks.Cohomology.Localization.derivedUnit_isIsoOnKInjective _ _ _ _
  dsimp only [localToGlobalUnit]
  rw [NatTrans.comp_app, NatTrans.comp_app]
  refine IsIso.comp_isIso' ?_ (IsIso.comp_isIso' hG ?_)
  · exact inferInstanceAs (IsIso (DerivedCategory.Qh.map _))
  · exact Functor.map_isIso RΓZ' _

variable (RΓZ : DerivedModuleSheaves X ⥤ DerivedGlobalModules X)
  (αZ : homotopyToDerived X (sectionsWithSupport X Z hZ) ⟶ DerivedCategory.Qh ⋙ RΓZ)

/-- **Stacks 0G70.** Let `Z` be a closed subset of a ringed space `X` and let
`i : (Z, 𝒪_X|_Z) ⟶ (X, 𝒪_X)` be the inclusion.  Then `RΓ(Z, -) ∘ RH_Z = RΓ_Z(X, -)` as functors
`D(𝒪_X) ⥤ D(𝒪_X(X))`: for every right derived functor `RΓ(Z, -)` of global sections on `Z` and
every right derived functor `RΓ_Z(X, -)` of global sections supported on `Z`, there is a
canonical natural isomorphism from the composite of `RH_Z` with `RΓ(Z, -)` to `RΓ_Z(X, -)`.  It
is canonical by uniqueness of right derived functors: it is the unique transformation compatible
with the comparisons to the underived functors, by
`derivedSectionsWithSupportIso_hom_fac` together with
`derivedSectionsWithSupportIso_hom_unique`. -/
@[stacks 0G70]
def derivedSectionsWithSupportIso
    [RΓZ'.IsRightDerivedFunctor αΓ
      (HomotopyCategory.quasiIso (ClosedModuleSheaves X Z) (ComplexShape.up ℤ))]
    [RΓZ.IsRightDerivedFunctor αZ
      (HomotopyCategory.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ))] :
    derivedSupportedSectionsOnClosed X Z hZ ⋙ RΓZ' ≅ RΓZ :=
  have := isRightDerivedFunctor_derivedSupportedSectionsOnClosed_comp X Z hZ RΓZ' αΓ
  Functor.rightDerivedUnique _ RΓZ (localToGlobalUnit X Z hZ RΓZ' αΓ) αZ
    (HomotopyCategory.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ))

/-- **Stacks 0G70, the normalization that makes the isomorphism the canonical one.** The
isomorphism of Stacks 0G70 carries the comparison `localToGlobalUnit` of `RΓ(Z, -) ∘ RH_Z` to
the comparison `αZ` of `RΓ_Z(X, -)`. -/
@[stacks 0G70 "the comparison is the canonical one"]
theorem derivedSectionsWithSupportIso_hom_fac
    [RΓZ'.IsRightDerivedFunctor αΓ
      (HomotopyCategory.quasiIso (ClosedModuleSheaves X Z) (ComplexShape.up ℤ))]
    [RΓZ.IsRightDerivedFunctor αZ
      (HomotopyCategory.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ))] :
    localToGlobalUnit X Z hZ RΓZ' αΓ ≫ Functor.whiskerLeft DerivedCategory.Qh
        (derivedSectionsWithSupportIso X Z hZ RΓZ' αΓ RΓZ αZ).hom =
      αZ := by
  have := isRightDerivedFunctor_derivedSupportedSectionsOnClosed_comp X Z hZ RΓZ' αΓ
  refine Eq.trans (Functor.rightDerivedNatTrans_fac _ RΓZ
    (localToGlobalUnit X Z hZ RΓZ' αΓ) αZ
    (HomotopyCategory.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ)) (𝟙 _)) ?_
  rw [Category.id_comp]

/-- The transformation normalized by `derivedSectionsWithSupportIso_hom_fac` is unique, so the
isomorphism of Stacks 0G70 is determined by that normalization. -/
theorem derivedSectionsWithSupportIso_hom_unique
    [RΓZ'.IsRightDerivedFunctor αΓ
      (HomotopyCategory.quasiIso (ClosedModuleSheaves X Z) (ComplexShape.up ℤ))]
    [RΓZ.IsRightDerivedFunctor αZ
      (HomotopyCategory.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ))]
    (t : derivedSupportedSectionsOnClosed X Z hZ ⋙ RΓZ' ⟶ RΓZ)
    (ht : localToGlobalUnit X Z hZ RΓZ' αΓ ≫ Functor.whiskerLeft DerivedCategory.Qh t = αZ) :
    t = (derivedSectionsWithSupportIso X Z hZ RΓZ' αΓ RΓZ αZ).hom := by
  have := isRightDerivedFunctor_derivedSupportedSectionsOnClosed_comp X Z hZ RΓZ' αΓ
  refine Functor.rightDerived_ext _ (localToGlobalUnit X Z hZ RΓZ' αΓ)
    (HomotopyCategory.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ)) RΓZ t _ ?_
  rw [ht, derivedSectionsWithSupportIso_hom_fac]

/-! ### Models of the two derived functors -/

/-- The total right derived functor `RΓ(Z, -) : D(𝒪_X|_Z) ⥤ D(𝒪_X(X))`, a model of the derived
functor quantified over above.  It exists because `Mod(𝒪_X|_Z)` is Grothendieck abelian, so
every complex has a K-injective resolution. -/
def derivedClosedSubspaceGlobalSections :
    DerivedCategory (ClosedModuleSheaves X Z) ⥤ DerivedGlobalModules X :=
  Functor.totalRightDerived
    ((closedSubspaceGlobalSections X Z).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh) DerivedCategory.Qh
    (HomotopyCategory.quasiIso (ClosedModuleSheaves X Z) (ComplexShape.up ℤ))

/-- The comparison exhibits `derivedClosedSubspaceGlobalSections` as a right derived functor of
`Γ(Z, -)`. -/
instance localToGlobal_derivedClosedSubspaceGlobalSections_isRightDerivedFunctor :
    (derivedClosedSubspaceGlobalSections X Z).IsRightDerivedFunctor
      (Functor.totalRightDerivedUnit
        ((closedSubspaceGlobalSections X Z).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh) DerivedCategory.Qh
        (HomotopyCategory.quasiIso (ClosedModuleSheaves X Z) (ComplexShape.up ℤ)))
      (HomotopyCategory.quasiIso (ClosedModuleSheaves X Z) (ComplexShape.up ℤ)) := by
  dsimp only [derivedClosedSubspaceGlobalSections]
  infer_instance

/-- The total right derived functor `RΓ_Z(X, -) : D(𝒪_X) ⥤ D(𝒪_X(X))`. -/
def derivedSectionsWithSupport :
    DerivedModuleSheaves X ⥤ DerivedGlobalModules X :=
  Functor.totalRightDerived (homotopyToDerived X (sectionsWithSupport X Z hZ))
    DerivedCategory.Qh (HomotopyCategory.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ))

/-- The comparison exhibits `derivedSectionsWithSupport` as a right derived functor of
`Γ_Z(X, -)`. -/
instance localToGlobal_derivedSectionsWithSupport_isRightDerivedFunctor :
    (derivedSectionsWithSupport X Z hZ).IsRightDerivedFunctor
      (Functor.totalRightDerivedUnit (homotopyToDerived X (sectionsWithSupport X Z hZ))
        DerivedCategory.Qh (HomotopyCategory.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ)))
      (HomotopyCategory.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ)) := by
  dsimp only [derivedSectionsWithSupport]
  infer_instance

/-- **Stacks 0G70 at the total right derived functors.** The two models exist, so the
isomorphism of Stacks 0G70 is not a statement about an empty family. -/
def derivedSectionsWithSupportIsoTotal :
    derivedSupportedSectionsOnClosed X Z hZ ⋙ derivedClosedSubspaceGlobalSections X Z ≅
      derivedSectionsWithSupport X Z hZ :=
  derivedSectionsWithSupportIso X Z hZ (derivedClosedSubspaceGlobalSections X Z)
    (Functor.totalRightDerivedUnit _ DerivedCategory.Qh _)
    (derivedSectionsWithSupport X Z hZ)
    (Functor.totalRightDerivedUnit _ DerivedCategory.Qh _)

end Stacks.Cohomology.LocalToGlobalSupport

end
