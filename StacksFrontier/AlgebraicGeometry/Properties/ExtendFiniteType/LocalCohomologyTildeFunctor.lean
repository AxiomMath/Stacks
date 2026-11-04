module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.LocalCohomology.SectionsWithSupport
public import StacksFrontier.AlgebraicGeometry.Modules.TildeExactness
public import StacksFrontier.AlgebraicGeometry.Properties.ExtendFiniteType.LocalCohomologySequence
public import StacksFrontier.AlgebraicGeometry.Properties.ExtendFiniteType.LocalCohomologyTilde
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.CompositeRightDerivedFunctors

/-!
# Sections with support on the spectrum, as a natural isomorphism of functors

Let `A` be a commutative ring, `X = Spec A` and `T ⊆ X` a closed subset.  Two functors on
`A`-modules compute sections with support in `T`: the algebraic one
`Stacks.LocalCohomology.sectionsWithSupportInFunctor`, and the geometric one `M ↦ Γ_T(X, M̃)`.
They are naturally isomorphic, and consequently so are their right derived functors in every
degree.

## Main results

* `Stacks.LocalCohomologyTilde.mem_sectionsWithSupportIn_iff_res_eq_zero`: an element of `M` is
  an algebraic section with support in `T` exactly when the corresponding global section of `M̃`
  restricts to zero on the open complement of `T`.
* `Stacks.LocalCohomologyTilde.sectionsWithSupportTildeIso`: the degree-zero comparison as a
  natural isomorphism `Γ_T(X, (-)~) ≅ H⁰_T(-)` of functors from `A`-modules to `A`-modules.
* `Stacks.LocalCohomologyTilde.rightDerivedSectionsWithSupportTildeIso`: in every degree, the
  right derived functor of `M ↦ Γ_T(X, M̃)` agrees with the right derived functor of the
  algebraic sections with support in `T`.
* `Stacks.LocalCohomologyTilde.rightDerivedCohomologyWithSupportTildeIso`: granted that `M ↦ M̃`
  carries injective modules to injective module sheaves, the cohomology with support in `T` of
  `M̃` is the algebraic local cohomology of `M` in every degree.

## Implementation notes

The scalars on the geometric side are the ring of global functions on `Spec A`, which enters as
the `RingCat` coercion of the sections of the structure sheaf, whereas `A` enters as a
`CommRingCat`; `Stacks.LocalCohomologyTilde.globalToBase` is restriction of scalars along the
ring isomorphism `A ≅ Γ(Spec A, 𝒪)`.  It is an equivalence of categories, hence exact, so the
degree-zero comparison propagates to the derived functors.  Composing
it with evaluation on the whole space *is* `AlgebraicGeometry.moduleSpecΓFunctor`, the global
sections functor of the associated-sheaf adjunction, so the comparison `M ≅ Γ(Spec A, M̃)` is
that adjunction's unit and needs no transport.  The subset is given at the spelling
`Set (PrimeSpectrum A)`, which is the one the algebraic side needs, and
`Stacks.LocalCohomologyTilde.supportSubset` retypes it for the geometric side.

The geometric functor is the kernel of restriction to the open complement, so both sides are
kernels of one morphism: evaluation at a module sheaf and `globalToBase` both preserve that
kernel, and the algebraic side is a kernel of the same morphism because membership in
`Stacks.LocalCohomology.sectionsWithSupportIn` is exactly the vanishing of the restriction.  The
comparison is therefore obtained from the universal property of the kernel, and it is an
isomorphism because it is a monomorphism by that factorization and an epimorphism by the same
membership criterion.  Its naturality follows from the two naturality squares after cancelling
the monomorphism into global sections.

Only the degree-zero comparison is a clause of Tag 0A6T.  What
`rightDerivedSectionsWithSupportTildeIso` compares in higher degrees is the right derived functor
of the *composite* `M ↦ Γ_T(X, M̃)` with the algebraic local cohomology; identifying it with
`H^n_T(X, M̃)`, the right derived functor of `Γ_T(X, -)` evaluated at `M̃`, needs the
associated-sheaf functor to carry injective modules to injective module sheaves, which is the
hypothesis of `rightDerivedCohomologyWithSupportTildeIso`.

## References

* [Stacks Project, Tag 0A6T](https://stacks.math.columbia.edu/tag/0A6T)
* [Stacks Project, Tag 0EF4](https://stacks.math.columbia.edu/tag/0EF4)
* [Stacks Project, Tag 0G71](https://stacks.math.columbia.edu/tag/0G71)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.SectionsWithSupport
open Stacks.LocalCohomology (sectionsWithSupportIn sectionsWithSupportInFunctor)

universe u

namespace Stacks.LocalCohomologyTilde

variable {A : CommRingCat.{u}}

/-! ### The bridge between the two rings of scalars -/

/-- The canonical ring isomorphism from `A` to the global functions on `Spec A`. -/
abbrev baseRingEquiv (A : CommRingCat.{u}) : A ≃+* Γ(Spec A, (⊤ : (Spec A).Opens)) :=
  (Scheme.ΓSpecIso A).symm.commRingCatIsoToRingEquiv

/-- A module over the global functions on `Spec A`, read as an `A`-module. -/
def globalToBase (A : CommRingCat.{u}) :
    GlobalModules (Spec A).toRingedSpace ⥤ ModuleCat.{u} A :=
  ModuleCat.restrictScalars (baseRingEquiv A).toRingHom

/-- Restriction of scalars from the global functions on `Spec A` to `A` is additive. -/
instance globalToBase_additive : (globalToBase A).Additive :=
  inferInstanceAs (ModuleCat.restrictScalars (baseRingEquiv A).toRingHom).Additive

/-- Restriction of scalars from the global functions on `Spec A` to `A` is an equivalence of
categories. -/
instance globalToBase_isEquivalence : (globalToBase A).IsEquivalence :=
  inferInstanceAs (ModuleCat.restrictScalars (baseRingEquiv A).toRingHom).IsEquivalence

/-- Restriction of scalars from the global functions on `Spec A` to `A` preserves homology. -/
instance globalToBase_preservesHomology : (globalToBase A).PreservesHomology := inferInstance

/-- Restriction of scalars from the global functions on `Spec A` to `A` preserves the kernel of
every morphism. -/
instance globalToBase_preservesKernel {Y₁ Y₂ : GlobalModules (Spec A).toRingedSpace}
    (g : Y₁ ⟶ Y₂) : PreservesLimit (parallelPair g 0) (globalToBase A) :=
  Functor.PreservesHomology.preservesKernel (globalToBase A) g

/-- The associated-sheaf functor, at the spelling of modules over the structure sheaf of the
ringed space underlying `Spec A`. -/
def tildeSheafFunctor (A : CommRingCat.{u}) :
    ModuleCat.{u} A ⥤ ModuleSheaves (Spec A).toRingedSpace :=
  tilde.functor A

/-- The associated-sheaf functor `M ↦ M̃` is additive. -/
instance tildeSheafFunctor_additive : (tildeSheafFunctor A).Additive :=
  inferInstanceAs (tilde.functor A).Additive

/-- The associated-sheaf functor `M ↦ M̃` preserves finite limits. -/
instance tildeSheafFunctor_preservesFiniteLimits :
    PreservesFiniteLimits (tildeSheafFunctor A) :=
  inferInstanceAs (PreservesFiniteLimits (tilde.functor A))

/-- The associated-sheaf functor `M ↦ M̃` preserves finite colimits. -/
instance tildeSheafFunctor_preservesFiniteColimits :
    PreservesFiniteColimits (tildeSheafFunctor A) :=
  inferInstanceAs (PreservesFiniteColimits (tilde.functor A))

/-- `M ↦ Γ(Spec A, M̃)`, as a functor to `A`-modules. -/
abbrev tildeGlobalSections (A : CommRingCat.{u}) : ModuleCat.{u} A ⥤ ModuleCat.{u} A :=
  tildeSheafFunctor A ⋙
    SheafOfModules.evaluation (structureSheafRing (Spec A).toRingedSpace)
      (op ⊤) ⋙ globalToBase A

/-- The canonical isomorphism `M ≅ Γ(Spec A, M̃)` of `A`-modules, natural in `M`.  It is the unit
of the associated-sheaf adjunction. -/
def globalSectionsTildeIso (A : CommRingCat.{u}) :
    𝟭 (ModuleCat.{u} A) ≅ tildeGlobalSections A :=
  tilde.toTildeΓNatIso

/-- The inverse of `M ≅ Γ(Spec A, M̃)` followed by the isomorphism is the identity on a global
section. -/
theorem globalSectionsTildeIso_hom_inv_apply (M : ModuleCat.{u} A)
    (y : (tildeGlobalSections A).obj M) :
    ((globalSectionsTildeIso A).hom.app M) (((globalSectionsTildeIso A).inv.app M) y) = y := by
  simp

/-- The isomorphism `M ≅ Γ(Spec A, M̃)` followed by its inverse is the identity on an element of
the module. -/
theorem globalSectionsTildeIso_inv_hom_apply (M : ModuleCat.{u} A) (m : M) :
    ((globalSectionsTildeIso A).inv.app M) (((globalSectionsTildeIso A).hom.app M) m) = m := by
  simp

/-- A subset of the prime spectrum of `A`, read as a subset of the space underlying `Spec A`. -/
def supportSubset (T : Set (PrimeSpectrum A)) : Set (Spec A).toRingedSpace := T

/-! ### The two functors of sections with support -/

variable (T : Set (PrimeSpectrum A)) (hT : IsClosed (supportSubset T))

/-- `M ↦ Γ_T(Spec A, M̃)`, as a functor to modules over the global functions. -/
def tildeSupportSheaf : ModuleCat.{u} A ⥤ GlobalModules (Spec A).toRingedSpace :=
  tildeSheafFunctor A ⋙ sectionsWithSupport (Spec A).toRingedSpace (supportSubset T) hT

/-- The functor `M ↦ Γ_T(Spec A, M̃)` is additive. -/
instance tildeSupportSheaf_additive : (tildeSupportSheaf T hT).Additive :=
  inferInstanceAs (tildeSheafFunctor A ⋙
    sectionsWithSupport (Spec A).toRingedSpace (supportSubset T) hT).Additive

/-- `M ↦ Γ(Spec A ∖ T, M̃)`, as a functor to `A`-modules. -/
abbrev tildeComplementSections : ModuleCat.{u} A ⥤ ModuleCat.{u} A :=
  tildeSheafFunctor A ⋙
    sectionsOnComplement (Spec A).toRingedSpace (supportSubset T) hT ⋙ globalToBase A

/-- Forgetting the support condition, `Γ_T(Spec A, M̃) ⟶ Γ(Spec A, M̃)`, natural in `M`. -/
def supportInclusion : tildeSupportSheaf T hT ⋙ globalToBase A ⟶ tildeGlobalSections A :=
  Functor.whiskerRight (Functor.whiskerLeft (tildeSheafFunctor A)
    (kernel.ι (restrictionToComplement (Spec A).toRingedSpace (supportSubset T) hT)))
    (globalToBase A)

/-- Restriction to the open complement, `Γ(Spec A, M̃) ⟶ Γ(Spec A ∖ T, M̃)`, natural in `M`. -/
def complementRestriction : tildeGlobalSections A ⟶ tildeComplementSections T hT :=
  Functor.whiskerRight (Functor.whiskerLeft (tildeSheafFunctor A)
    (restrictionToComplement (Spec A).toRingedSpace (supportSubset T) hT)) (globalToBase A)

/-- The inclusion of the algebraic sections with support in `T` into the module, natural in the
module. -/
def algebraicSupportInclusion :
    sectionsWithSupportInFunctor.{u, u} A T ⟶ 𝟭 (ModuleCat.{u} A) where
  app M := ModuleCat.ofHom (sectionsWithSupportIn A T M).subtype
  naturality M N f := by ext x; rfl

/-! ### The comparison -/

/-- An element of `M` is an algebraic section with support in `T` exactly when the corresponding
global section of `M̃` restricts to zero on the open complement of `T`. -/
theorem mem_sectionsWithSupportIn_iff_res_eq_zero (M : ModuleCat.{u} A) (m : M) :
    m ∈ sectionsWithSupportIn A T M ↔
      ((tilde M).val.presheaf.map
          (homOfLE (le_top : openComplement (supportSubset T) hT ≤ ⊤)).op).hom
        ((tilde.toOpen M ⊤) m) = 0 := by
  refine (mem_sectionsWithSupportIn_iff M T m).trans ?_
  refine (mem_supportedSectionsSubmodule_iff (supportSubset T) (tilde M) ⊤ _).trans ?_
  have hg := fun x (hx : x ∈ openComplement (supportSubset T) hT) =>
    TopCat.Presheaf.germ_res_apply (tilde M).val.presheaf
      (homOfLE (le_top : openComplement (supportSubset T) hT ≤ ⊤)) x hx ((tilde.toOpen M ⊤) m)
  constructor
  · intro h
    refine TopCat.Presheaf.section_ext
      (⟨(tilde M).val.presheaf, (tilde M).isSheaf⟩ : TopCat.Sheaf AddCommGrpCat.{u} (Spec A))
      (openComplement (supportSubset T) hT) _ 0 ?_
    intro x hx
    rw [map_zero]
    exact (hg x hx).trans (h x trivial hx)
  · intro h x _ hxT
    rw [← hg x hxT, h, map_zero]

/-- An element of `M` is an algebraic section with support in `T` exactly when the corresponding
global section of `M̃` has zero image under restriction to the open complement of `T`. -/
theorem mem_sectionsWithSupportIn_iff_app_eq_zero (M : ModuleCat.{u} A) (m : M) :
    m ∈ sectionsWithSupportIn A T M ↔
      ((globalSectionsTildeIso A).hom.app M ≫ (complementRestriction T hT).app M) m = 0 :=
  mem_sectionsWithSupportIn_iff_res_eq_zero T hT M m

/-- The two maps out of sections with support compose to zero. -/
theorem supportInclusion_comp_complementRestriction (M : ModuleCat.{u} A) :
    (supportInclusion T hT).app M ≫ (complementRestriction T hT).app M = 0 := by
  have h := NatTrans.congr_app
    (sectionsWithSupport_comp_restrictionToComplement (Spec A).toRingedSpace
      (supportSubset T) hT) ((tildeSheafFunctor A).obj M)
  simp only [NatTrans.comp_app, zero_app] at h
  simp only [supportInclusion, complementRestriction, Functor.whiskerRight_app,
    Functor.whiskerLeft_app]
  refine ((globalToBase A).map_comp _ _).symm.trans ?_
  rw [h]
  exact (globalToBase A).map_zero _ _

/-- The algebraic sections with support in `T`, included into the global sections of `M̃`. -/
def algebraicToGlobalSections (M : ModuleCat.{u} A) :
    (sectionsWithSupportInFunctor.{u, u} A T).obj M ⟶ (tildeGlobalSections A).obj M :=
  (algebraicSupportInclusion T).app M ≫ (globalSectionsTildeIso A).hom.app M

/-- The inclusion of the algebraic sections with support in `T` into `Γ(Spec A, M̃)` is a
monomorphism. -/
instance algebraicToGlobalSections_mono (M : ModuleCat.{u} A) :
    Mono (algebraicToGlobalSections T M) := by
  rw [ModuleCat.mono_iff_injective]
  intro x y hxy
  refine Subtype.val_injective ?_
  have h := congrArg (fun z => ((globalSectionsTildeIso A).inv.app M) z) hxy
  simp only [algebraicToGlobalSections, CategoryTheory.comp_apply,
    globalSectionsTildeIso_inv_hom_apply] at h
  exact h

/-- The inclusion of the algebraic sections with support is natural in the module. -/
theorem algebraicToGlobalSections_naturality {M N : ModuleCat.{u} A} (f : M ⟶ N) :
    (sectionsWithSupportInFunctor.{u, u} A T).map f ≫ algebraicToGlobalSections T N =
      algebraicToGlobalSections T M ≫ (tildeGlobalSections A).map f := by
  rw [algebraicToGlobalSections, algebraicToGlobalSections, ← Category.assoc,
    (algebraicSupportInclusion T).naturality f, Category.assoc,
    (globalSectionsTildeIso A).hom.naturality f, Category.assoc]

/-- The algebraic sections with support in `T` restrict to zero on the open complement. -/
theorem algebraicToGlobalSections_comp_complementRestriction (M : ModuleCat.{u} A) :
    algebraicToGlobalSections T M ≫ (complementRestriction T hT).app M = 0 := by
  ext x
  exact (mem_sectionsWithSupportIn_iff_app_eq_zero T hT M x.val).mp x.property

/-- **The geometric sections with support are a kernel.**  Sections with support in `T` are the
kernel of restriction to the open complement in the functor category, and both evaluation at a
module sheaf and restriction of scalars to `A` preserve that kernel. -/
def geometricForkIsLimit (M : ModuleCat.{u} A) :
    IsLimit (KernelFork.ofι ((supportInclusion T hT).app M)
      (supportInclusion_comp_complementRestriction T hT M)) := by
  have h1 := KernelFork.mapIsLimit
    (c := KernelFork.ofι (kernel.ι (restrictionToComplement (Spec A).toRingedSpace
      (supportSubset T) hT)) (kernel.condition _))
    (kernelIsKernel _)
    ((CategoryTheory.evaluation (ModuleSheaves (Spec A).toRingedSpace)
      (GlobalModules (Spec A).toRingedSpace)).obj ((tildeSheafFunctor A).obj M))
  exact KernelFork.mapIsLimit (c := _) h1 (globalToBase A)

/-- The inclusion `Γ_T(Spec A, M̃) ⟶ Γ(Spec A, M̃)` is a monomorphism. -/
instance supportInclusion_app_mono (M : ModuleCat.{u} A) :
    Mono ((supportInclusion T hT).app M) :=
  mono_of_isLimit_fork (geometricForkIsLimit T hT M)

/-- The comparison from the algebraic to the geometric sections with support, at a module. -/
def algebraicToGeometricApp (M : ModuleCat.{u} A) :
    (sectionsWithSupportInFunctor.{u, u} A T).obj M ⟶
      (tildeSupportSheaf T hT ⋙ globalToBase A).obj M :=
  (KernelFork.IsLimit.lift' (geometricForkIsLimit T hT M) (algebraicToGlobalSections T M)
    (algebraicToGlobalSections_comp_complementRestriction T hT M)).1

/-- The comparison is compatible with the two inclusions into the global sections of `M̃`. -/
theorem algebraicToGeometricApp_comp (M : ModuleCat.{u} A) :
    algebraicToGeometricApp T hT M ≫ (supportInclusion T hT).app M =
      algebraicToGlobalSections T M :=
  (KernelFork.IsLimit.lift' _ _ _).2

/-- A geometric section with support in `T` is, through `M ≅ Γ(Spec A, M̃)`, an algebraic section
with support in `T`. -/
theorem inv_supportInclusion_mem (M : ModuleCat.{u} A)
    (s : (tildeSupportSheaf T hT ⋙ globalToBase A).obj M) :
    ((globalSectionsTildeIso A).inv.app M) (((supportInclusion T hT).app M) s) ∈
      sectionsWithSupportIn A T M := by
  have hz : ((complementRestriction T hT).app M) (((supportInclusion T hT).app M) s) = 0 := by
    rw [← CategoryTheory.comp_apply, supportInclusion_comp_complementRestriction]
    simp
  refine (mem_sectionsWithSupportIn_iff_app_eq_zero T hT M _).mpr ?_
  rw [CategoryTheory.comp_apply, globalSectionsTildeIso_hom_inv_apply, hz]

/-- The comparison from the algebraic to the geometric sections with support is an isomorphism
at every module. -/
instance algebraicToGeometricApp_isIso (M : ModuleCat.{u} A) :
    IsIso (algebraicToGeometricApp T hT M) := by
  have hmono : Mono (algebraicToGeometricApp T hT M) :=
    mono_of_mono_fac (algebraicToGeometricApp_comp T hT M)
  have hepi : Epi (algebraicToGeometricApp T hT M) := by
    rw [ModuleCat.epi_iff_surjective]
    intro s
    refine ⟨⟨_, inv_supportInclusion_mem T hT M s⟩, ?_⟩
    apply (ModuleCat.mono_iff_injective _).mp (supportInclusion_app_mono T hT M)
    rw [← CategoryTheory.comp_apply, algebraicToGeometricApp_comp, algebraicToGlobalSections,
      CategoryTheory.comp_apply]
    exact globalSectionsTildeIso_hom_inv_apply M _
  exact isIso_of_mono_of_epi _

/-- The comparison from the algebraic to the geometric sections with support. -/
def algebraicToGeometric :
    sectionsWithSupportInFunctor.{u, u} A T ⟶ tildeSupportSheaf T hT ⋙ globalToBase A where
  app M := algebraicToGeometricApp T hT M
  naturality M N f := by
    rw [← cancel_mono ((supportInclusion T hT).app N), Category.assoc,
      algebraicToGeometricApp_comp, Category.assoc, (supportInclusion T hT).naturality f,
      ← Category.assoc, algebraicToGeometricApp_comp, algebraicToGlobalSections_naturality]

/-- Each component of the comparison `algebraicToGeometric` is an isomorphism. -/
instance algebraicToGeometric_app_isIso (M : ModuleCat.{u} A) :
    IsIso ((algebraicToGeometric T hT).app M) :=
  algebraicToGeometricApp_isIso T hT M

/-- The comparison `algebraicToGeometric` is a natural isomorphism. -/
instance algebraicToGeometric_isIso : IsIso (algebraicToGeometric T hT) :=
  NatIso.isIso_of_isIso_app _

/-- For a closed subset `T` of `Spec A`, the global sections with support in `T` of the sheaf
`M̃`, read as an `A`-module, are the algebraic sections of `M` with support in `T`, naturally in
`M`. -/
@[stacks 0A6T "degree zero, as a natural isomorphism of functors"]
def sectionsWithSupportTildeIso :
    tildeSupportSheaf T hT ⋙ globalToBase A ≅
      sectionsWithSupportInFunctor.{u, u} A T :=
  (asIso (algebraicToGeometric T hT)).symm

/-- In every degree, the right derived functor of `M ↦ Γ_T(Spec A, M̃)`, read over `A`, is the
right derived functor of the algebraic sections of `M` with support in `T`. -/
def rightDerivedSectionsWithSupportTildeIso (n : ℕ) :
    (tildeSupportSheaf T hT).rightDerived n ⋙ globalToBase A ≅
      (sectionsWithSupportInFunctor.{u, u} A T).rightDerived n :=
  Stacks.Cohomology.ModuleComparison.rightDerivedCompIso _ _ _
    (sectionsWithSupportTildeIso T hT) n

/-- If `M ↦ M̃` carries injective `A`-modules to injective module sheaves, then in every degree
the cohomology with support in `T` of `M̃`, read over `A`, is the algebraic local cohomology of
`M`. -/
def rightDerivedCohomologyWithSupportTildeIso
    (hinj : (tildeSheafFunctor A).PreservesInjectiveObjects) (n : ℕ) :
    tildeSheafFunctor A ⋙
        (sectionsWithSupport (Spec A).toRingedSpace (supportSubset T) hT).rightDerived n ⋙
          globalToBase A ≅
      (sectionsWithSupportInFunctor.{u, u} A T).rightDerived n :=
  Functor.isoWhiskerRight
      (Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso (tildeSheafFunctor A)
        (sectionsWithSupport (Spec A).toRingedSpace (supportSubset T) hT) n).symm
      (globalToBase A) ≪≫
    rightDerivedSectionsWithSupportTildeIso T hT n

end Stacks.LocalCohomologyTilde

end
