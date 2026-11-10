module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkEpiMono
public import StacksFrontier.AlgebraicGeometry.Coherent.HomColimit.IdealPowerBridge
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Finiteness
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.FittingIdeals
public import StacksFrontier.AlgebraicGeometry.IntegralReduction.Transport
public import StacksFrontier.AlgebraicGeometry.QcohLimits.Sections
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.FiniteTypeGeneration
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.SubmoduleFactorAffine
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.FiniteTypeSubobjectExtension
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.FiniteTypeSubobjects

/-!
# A quasi-compact open is the complement of the vanishing locus of a finite type ideal sheaf

Let `X` be a quasi-compact and quasi-separated scheme and let `U ⊆ X` be a quasi-compact open.
Then there is a finite type quasi-coherent sheaf of ideals on `X` whose vanishing locus is
`X \ U`. This is the implication (2) ⟹ (4) of Stacks 01PH; the remaining clauses of that tag
are in `StacksFrontier/AlgebraicGeometry/Properties/ExtendFiniteType/RetrocompactOpen.lean`.

The proof is the source's. Let `J` be the ideal sheaf cutting out the reduced induced closed
subscheme structure on `X \ U` (Stacks 01J3, here
`AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal`). Its ideal on an affine open contained
in `U` is the unit ideal, so the inclusion `J ⟶ 𝒪_X` is bijective on sections over every open
contained in `U`, and therefore `J|_U` is `𝒪_U`, which is of finite type. Stacks 01PF
(`AlgebraicGeometry.exists_finiteTypeQuasicoherentSubobject_extension`) then produces a finite
type quasi-coherent submodule of `J` agreeing with `J` over `U`, and that submodule is the
required sheaf of ideals.

## Main definitions

* `AlgebraicGeometry.idealSheafDataOfHom`: the sheaf of ideals which is the image of a
  quasi-coherent `𝒪_X`-module under a morphism to the structure sheaf.
* `AlgebraicGeometry.toIdealPowOfHom`: the factorization of that morphism through its image.

## Main results

* `AlgebraicGeometry.exists_isFiniteType_idealSheafData_support_eq_compl`: **Tag 01PH,
  (2) ⟹ (4)**.
* `AlgebraicGeometry.isFiniteType_idealSheafDataOfHom`: the image of a module of finite type is
  a sheaf of ideals of finite type.
* `AlgebraicGeometry.epi_toIdealPowOfHom`: the image ideal sheaf of a morphism to the structure
  sheaf is a quotient of the module it is the image of.

## Implementation notes

Stacks 01PF is stated for subobjects of a sheaf of modules, while clause (4) of 01PH is about a
sheaf of ideals, which in this development is
`AlgebraicGeometry.Scheme.IdealSheafData` — a family of ideals on the affine opens compatible
with localization. Passing from the former to the latter is
`AlgebraicGeometry.idealSheafDataOfHom`, which takes the ideal on an affine open `V` to be the
image of `Γ(A, V)` in `Γ(X, V)`. The content of that construction is the compatibility
`AlgebraicGeometry.map_idealOfHom_basicOpen`, which is the statement that the sections of a
quasi-coherent module over a basic open are a localization
(`Stacks.AlgebraicGeometry.QuasicoherentBaseChange.isLocalizedModule_restrictₗ`): a section of
`A` over `D(f)` becomes a restriction after multiplication by a power of `f`, and `f` is
invertible there.

Clause (4) is stated with `AlgebraicGeometry.Scheme.IdealSheafData.IsFiniteType`, finite
generation of the ideal on each affine open, which is the hypothesis that the converse
implication `AlgebraicGeometry.isCompact_of_isFiniteType_idealSheafData` consumes, so that the
two clauses compose.

## References

* [Stacks Project, Tag 01PH](https://stacks.math.columbia.edu/tag/01PH)
* [Stacks Project, Tag 01PF](https://stacks.math.columbia.edu/tag/01PF)
* [Stacks Project, Tag 01J3](https://stacks.math.columbia.edu/tag/01J3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.IdealPowerColimit
open Stacks.AlgebraicGeometry.QuasicoherentBaseChange
open Stacks.AlgebraicGeometry.Tag01YEIntegralReduction (isIso_restrictFunctor_map_of_forall_app
  isIso_app_of_isIso_restrictFunctor_map)

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- A morphism from an `𝒪_X`-module to the structure sheaf, on sections over an open, as a
linear map with values in `Γ(X, V)` on the nose.  This is
`Stacks.AlgebraicGeometry.QcohLimits.appₗ` with its target read as `Γ(X, V)` rather than as the
sections of the structure sheaf viewed as a module over itself. -/
noncomputable def structureAppₗ {A : X.Modules} (φ : A ⟶ structureModule X) (V : X.Opens) :
    Γ(A, V) →ₗ[Γ(X, V)] Γ(X, V) :=
  Stacks.AlgebraicGeometry.QcohLimits.appₗ φ V

/-- Restriction of sections commutes with a morphism into the structure sheaf. -/
theorem map_structureAppₗ {A : X.Modules} (φ : A ⟶ structureModule X) {V W : X.Opens}
    (h : W ≤ V) (a : Γ(A, V)) :
    (X.presheaf.map (homOfLE h).op).hom (structureAppₗ φ V a)
      = structureAppₗ φ W (A.presheaf.map (homOfLE h).op a) :=
  app_naturality φ h a

/-- The ideal of sections of `𝒪_X` over `V` coming from `A` along `φ`. -/
noncomputable def idealOfHom (A : X.Modules) (φ : A ⟶ structureModule X) (V : X.Opens) :
    Ideal Γ(X, V) :=
  LinearMap.range (structureAppₗ φ V)

/-- A section `y` of `𝒪_X` over `V` lies in `idealOfHom A φ V` if and only if it is the image
under `φ` of a section of `A` over `V`. -/
theorem mem_idealOfHom_iff {A : X.Modules} {φ : A ⟶ structureModule X} {V : X.Opens}
    {y : Γ(X, V)} : y ∈ idealOfHom A φ V ↔ ∃ x : Γ(A, V), structureAppₗ φ V x = y :=
  Iff.rfl

/-- The ideals `idealOfHom A φ V` are compatible with passing to a basic open: this is the
localization statement for the quasi-coherent module `A`. -/
theorem map_idealOfHom_basicOpen (A : X.Modules) [A.IsQuasicoherent]
    (φ : A ⟶ structureModule X) (V : X.affineOpens) (f : Γ(X, V.1)) :
    (idealOfHom A φ V.1).map (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom =
      idealOfHom A φ (X.basicOpen f) := by
  have hle : X.basicOpen f ≤ V.1 := X.basicOpen_le f
  let _ : Algebra Γ(X, V.1) Γ(X, X.basicOpen f) := algebraOfLE X hle
  let _ : IsLocalization.Away f Γ(X, X.basicOpen f) := V.2.isLocalization_basicOpen f
  let _ := moduleOfLE A hle
  have hA : IsLocalizedModule (Submonoid.powers f) (restrictₗ A hle) :=
    isLocalizedModule_restrictₗ A V.2 f rfl hle
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    rintro y ⟨x, rfl⟩
    exact ⟨A.presheaf.map (homOfLE hle).op x, (map_structureAppₗ φ hle x).symm⟩
  · rintro y ⟨x, rfl⟩
    obtain ⟨⟨a, s⟩, hs⟩ := hA.surj x
    obtain ⟨n, hn⟩ := s.2
    have hs' : (s : Γ(X, V.1)) • x = restrictₗ A hle a := hs
    have hsmul : (s : Γ(X, V.1)) • x
        = (X.presheaf.map (homOfLE hle).op).hom (s : Γ(X, V.1)) • x := rfl
    have key : (X.presheaf.map (homOfLE hle).op).hom (s : Γ(X, V.1)) *
        structureAppₗ φ (X.basicOpen f) x
          = (X.presheaf.map (homOfLE hle).op).hom (structureAppₗ φ V.1 a) := by
      rw [← smul_eq_mul, ← LinearMap.map_smul, ← hsmul, hs']
      exact (map_structureAppₗ φ hle a).symm
    have hmem : (X.presheaf.map (homOfLE hle).op).hom (s : Γ(X, V.1)) *
        structureAppₗ φ (X.basicOpen f) x
          ∈ (idealOfHom A φ V.1).map (X.presheaf.map (homOfLE hle).op).hom := by
      rw [key]
      exact Ideal.mem_map_of_mem _ ⟨a, rfl⟩
    refine (Ideal.unit_mul_mem_iff_mem _ ?_).mp hmem
    have hf : IsUnit ((X.presheaf.map (homOfLE hle).op).hom f) :=
      IsLocalization.map_units (M := Submonoid.powers f) Γ(X, X.basicOpen f) ⟨f, 1, pow_one f⟩
    rw [← hn]
    simpa using hf.pow n

/-- The quasi-coherent sheaf of ideals which is the image of a quasi-coherent `𝒪_X`-module
under a morphism to the structure sheaf. -/
noncomputable def idealSheafDataOfHom (A : X.Modules) [A.IsQuasicoherent]
    (φ : A ⟶ structureModule X) : X.IdealSheafData where
  ideal V := idealOfHom A φ V.1
  map_ideal_basicOpen V f := map_idealOfHom_basicOpen A φ V f

/-- Over an affine open `V`, the ideal of `idealSheafDataOfHom A φ` is `idealOfHom A φ V`. -/
@[simp]
theorem idealSheafDataOfHom_ideal (A : X.Modules) [A.IsQuasicoherent]
    (φ : A ⟶ structureModule X) (V : X.affineOpens) :
    (idealSheafDataOfHom A φ).ideal V = idealOfHom A φ V.1 := rfl

/-- **The image ideal sheaf, as a quotient of the module it is the image of.** A morphism
`φ : A ⟶ 𝒪_X` from a quasi-coherent `𝒪_X`-module factors through its image
`idealSheafDataOfHom A φ`, read as the sheaf of modules
`Stacks.AlgebraicGeometry.IdealPowerColimit.idealPow _ 1`.

The affine-local check that the values of `φ` land in the image is a tautology: the ideal of
`idealSheafDataOfHom A φ` over an affine open is by definition the range of `φ` there. -/
noncomputable def toIdealPowOfHom (A : X.Modules) [A.IsQuasicoherent]
    (φ : A ⟶ structureModule X) :
    A ⟶ idealPow (idealSheafDataOfHom A φ) 1 :=
  factorThruOfForallAffineOpens _ φ fun V x ↦ by
    refine (obj_idealPow_affineOpen (idealSheafDataOfHom A φ) 1 V).ge ?_
    rw [pow_one, idealSheafDataOfHom_ideal]
    exact ⟨x, rfl⟩

/-- The factorization through the image ideal sheaf, composed with the inclusion of the latter
into the structure sheaf, is the original morphism. -/
@[reassoc (attr := simp)]
theorem toIdealPowOfHom_ι (A : X.Modules) [A.IsQuasicoherent]
    (φ : A ⟶ structureModule X) :
    toIdealPowOfHom A φ ≫ (Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple
        (idealSheafDataOfHom A φ) 1 (structureModule X)).ι = φ :=
  factorThruOfForallAffineOpens_ι _ _ _

/-- The factorization through the image ideal sheaf does not change the value of a section. -/
theorem val_toIdealPowOfHom_app (A : X.Modules) [A.IsQuasicoherent]
    (φ : A ⟶ structureModule X) (W : X.Opens) (x : Γ(A, W)) :
    (((toIdealPowOfHom A φ).app W x).1 : Γ(X, W)) = φ.app W x := rfl

/-- **The image ideal sheaf of a morphism to the structure sheaf is a quotient of the source.**
Over an affine open the ideal is exactly the range of `φ`, so a section of the image over any
open is, on an affine neighbourhood of each of its points, the image of a section of `A`; that
is the section-level criterion for an epimorphism of sheaves of modules.

This is what makes the image of a finite locally free module a finite-locally-free quotient,
which is the shape in which [Stacks, Tag 0F89] consumes a sheaf of ideals. -/
theorem epi_toIdealPowOfHom (A : X.Modules) [A.IsQuasicoherent]
    (φ : A ⟶ structureModule X) : Epi (toIdealPowOfHom A φ) := by
  have hepi : @Epi (SheafOfModules X.ringCatSheaf) _ _ _ (toIdealPowOfHom A φ) := by
    refine Stacks.SheafOfModules.StalkEpiMono.epi_of_exists_sections _ fun W t p hp ↦ ?_
    obtain ⟨-, ⟨V, hVaff, rfl⟩, hpV, hVW⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (show p ∈ (W : Set X) from hp) W.isOpen
    have hmem := (obj_idealPow_affineOpen (idealSheafDataOfHom A φ) 1 ⟨V, hVaff⟩).le
      ((idealPow (idealSheafDataOfHom A φ) 1).val.map (homOfLE hVW).op t).2
    rw [pow_one, idealSheafDataOfHom_ideal] at hmem
    obtain ⟨x, hx⟩ := hmem
    exact ⟨V, hVW, hpV, x, Subtype.ext hx⟩
  exact ⟨fun g₁ g₂ h ↦ hepi.left_cancellation g₁ g₂ h⟩

/-- The image of a quasi-coherent module of finite type is a finite type sheaf of ideals. -/
theorem isFiniteType_idealSheafDataOfHom (A : X.Modules) [A.IsQuasicoherent] [A.IsFiniteType]
    (φ : A ⟶ structureModule X) :
    (idealSheafDataOfHom A φ).IsFiniteType := by
  intro V
  rw [idealSheafDataOfHom_ideal, idealOfHom, LinearMap.range_eq_map]
  exact (Module.finite_def.mp (moduleFinite_sections_on_affine A V.1 V.2)).map _

/-- The vanishing ideal of a closed subset is the unit ideal on an affine open disjoint from it. -/
theorem Scheme.IdealSheafData.vanishingIdeal_ideal_eq_top_of_subset_compl (Z : Closeds X)
    (V : X.affineOpens) (hV : (V.1 : Set X) ⊆ (Z : Set X)ᶜ) : (vanishingIdeal Z).ideal V = ⊤ := by
  rw [Scheme.IdealSheafData.vanishingIdeal_ideal]
  refine Eq.trans (congrArg PrimeSpectrum.vanishingIdeal ?_) PrimeSpectrum.vanishingIdeal_empty
  ext p
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hp
  have hmem : _ ∈ (V.1 : Set X) := V.2.range_fromSpec ▸ Set.mem_range_self p
  exact hV hmem hp

/-- A point of an affine open on which an ideal sheaf is the unit ideal is not in its support. -/
theorem Scheme.IdealSheafData.notMem_support_of_ideal_eq_top {I : X.IdealSheafData}
    (V : X.affineOpens) {x : X} (hxV : x ∈ V.1) (h : I.ideal V = ⊤) : x ∉ I.support := by
  intro hx
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := V) hxV, h] at hx
  simp only [Scheme.mem_zeroLocus_iff, SetLike.mem_coe] at hx
  exact hx 1 Submodule.mem_top (by simpa using hxV)

/-- If an ideal sheaf is the unit ideal on every affine open inside `U`, then every section of
`𝒪_X` over an open inside `U` lies in it. -/
theorem Scheme.IdealSheafData.mem_unitSubmodule_obj_of_forall_ideal_eq_top
    (J : X.IdealSheafData) {U : X.Opens} (hJ : ∀ V : X.affineOpens, V.1 ≤ U → J.ideal V = ⊤)
    {W : X.Opens} (hW : W ≤ U) (a : Γ(X, W)) : a ∈ J.unitSubmodule.toSubmodule.obj (op W) := by
  refine Stacks.AlgebraicGeometry.IdealPower.mem_of_forall_affineOpens J.unitSubmodule
    (show Γ(structureModule X, W) from a) fun V hV ↦ ?_
  have hV' : J.unitSubmodule.toSubmodule.obj (op V.1) = (J.ideal V : Ideal Γ(X, V.1)) :=
    Scheme.IdealSheafData.unitSubmodule_obj_affine J V
  rw [hV', hJ V (hV.trans hW)]
  trivial

/-- If an ideal sheaf is the unit ideal on every affine open inside `U`, then its restriction
to `U` is of finite type. -/
theorem Scheme.IdealSheafData.isFiniteType_restrict_unitSubmodule_of_forall_ideal_eq_top
    (J : X.IdealSheafData) (U : X.Opens) (hJ : ∀ V : X.affineOpens, V.1 ≤ U → J.ideal V = ⊤) :
    ((subMod J.unitSubmodule).restrict U.ι).IsFiniteType := by
  set ν : subMod J.unitSubmodule ⟶ structureModule X := J.unitSubmodule.ι
  have hιiso : ∀ W : X.Opens, W ≤ U → IsIso (ν.app W) := fun W hW ↦ by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact ⟨fun y₁ y₂ h ↦ Subtype.ext h,
      fun a ↦ ⟨⟨a, J.mem_unitSubmodule_obj_of_forall_ideal_eq_top hJ hW a⟩, rfl⟩⟩
  have : IsIso ((Scheme.Modules.restrictFunctor U.ι).map ν) :=
    isIso_restrictFunctor_map_of_forall_app ν U hιiso
  exact isFiniteType_of_iso_modules
    (asIso ((Scheme.Modules.restrictFunctor U.ι).map ν) ≪≫ Scheme.Modules.restrictUnitIso U.ι)
    (unit_isQuasicoherent_and_isFiniteType (X := U.toScheme)).2

/-- On a quasi-compact quasi-separated scheme, an ideal sheaf which is the unit ideal on every
affine open inside a quasi-compact open `U` contains a finite type ideal sheaf with the same
property. -/
theorem Scheme.IdealSheafData.exists_isFiniteType_le_forall_ideal_eq_top
    [CompactSpace X] [QuasiSeparatedSpace X] (J : X.IdealSheafData) (U : X.Opens)
    (hU : IsCompact (U : Set X)) (hJ : ∀ V : X.affineOpens, V.1 ≤ U → J.ideal V = ⊤) :
    ∃ I : X.IdealSheafData, I.IsFiniteType ∧ I ≤ J ∧
      ∀ V : X.affineOpens, V.1 ≤ U → I.ideal V = ⊤ := by
  classical
  set N : (structureModule X).Submodule := J.unitSubmodule
  set ν : subMod N ⟶ structureModule X := N.ι
  have hFwft : ((subMod N).restrict U.ι).IsFiniteType :=
    J.isFiniteType_restrict_unitSubmodule_of_forall_ideal_eq_top U hJ
  have hqcJ : (subMod N).IsQuasicoherent :=
    AlgebraicGeometry.Scheme.IdealSheafData.unitSubmodule_isQuasicoherent J
  set eTop : ((⊤ : Subobject ((subMod N).restrict U.ι)) : U.toScheme.Modules) ≅
      (subMod N).restrict U.ι := asIso (⊤ : Subobject ((subMod N).restrict U.ι)).arrow
  have : ((⊤ : Subobject ((subMod N).restrict U.ι)) : U.toScheme.Modules).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).prop_of_iso eTop.symm inferInstance
  have : ((⊤ : Subobject ((subMod N).restrict U.ι)) : U.toScheme.Modules).IsFiniteType :=
    isFiniteType_of_iso_modules eTop hFwft
  obtain ⟨G, hGqc, hGft, e, he⟩ :=
    exists_finiteTypeQuasicoherentSubobject_extension (subMod N) U hU ⊤
  have hGresiso : IsIso ((Scheme.Modules.restrictFunctor U.ι).map G.arrow) := by
    rw [he]
    infer_instance
  have hGiso : ∀ W : X.Opens, W ≤ U → IsIso (G.arrow.app W) :=
    isIso_app_of_isIso_restrictFunctor_map G.arrow U hGresiso
  set φ : (G : X.Modules) ⟶ structureModule X := G.arrow ≫ ν
  have hφapp : ∀ (W : X.Opens) (x : Γ((G : X.Modules), W)),
      structureAppₗ φ W x = ((G.arrow.app W x).1 : Γ(X, W)) := fun _ _ ↦ rfl
  refine ⟨idealSheafDataOfHom (G : X.Modules) φ,
    isFiniteType_idealSheafDataOfHom (G : X.Modules) φ, fun V ↦ ?_, fun V hVU ↦ ?_⟩
  · rintro y ⟨x, rfl⟩
    rw [hφapp]
    exact (Scheme.IdealSheafData.unitSubmodule_obj_affine J V).le (G.arrow.app V.1 x).2
  have hNtop := J.mem_unitSubmodule_obj_of_forall_ideal_eq_top hJ hVU (1 : Γ(X, V.1))
  have h1 : (1 : Γ(X, V.1)) ∈ idealOfHom (G : X.Modules) φ V.1 := by
    have hiso : IsIso (G.arrow.app V.1) := hGiso V.1 hVU
    refine ⟨inv (G.arrow.app V.1) ⟨(1 : Γ(X, V.1)), hNtop⟩, ?_⟩
    rw [hφapp]
    have : G.arrow.app V.1 (inv (G.arrow.app V.1) ⟨(1 : Γ(X, V.1)), hNtop⟩)
        = ⟨(1 : Γ(X, V.1)), hNtop⟩ := by
      change (inv (G.arrow.app V.1) ≫ G.arrow.app V.1) _ = _
      rw [IsIso.inv_hom_id]
      rfl
    rw [this]
  exact Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one

/-- **A quasi-compact open of a quasi-compact quasi-separated scheme is the complement of the
vanishing locus of a finite type quasi-coherent sheaf of ideals.** -/
@[stacks 01PH "(2) ⟹ (4)"]
theorem exists_isFiniteType_idealSheafData_support_eq_compl
    [CompactSpace X] [QuasiSeparatedSpace X] (U : X.Opens) (hU : IsCompact (U : Set X)) :
    ∃ I : X.IdealSheafData, I.IsFiniteType ∧ (I.support : Set X) = (U : Set X)ᶜ := by
  set Z : Closeds X := ⟨(U : Set X)ᶜ, U.2.isClosed_compl⟩
  have hJsupp : ((Scheme.IdealSheafData.vanishingIdeal Z).support : Set X) = (U : Set X)ᶜ :=
    Scheme.IdealSheafData.coe_support_vanishingIdeal Z
  obtain ⟨I, hI, hle, htop⟩ := (Scheme.IdealSheafData.vanishingIdeal Z)
    |>.exists_isFiniteType_le_forall_ideal_eq_top U hU fun V hV ↦
      Scheme.IdealSheafData.vanishingIdeal_ideal_eq_top_of_subset_compl Z V
        fun _ hx hxZ ↦ hxZ (hV hx)
  refine ⟨I, hI, subset_antisymm (fun x hx hxU ↦ ?_) ?_⟩
  · obtain ⟨-, ⟨V, hVaff, rfl⟩, hxV, hVU⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hxU U.isOpen
    exact Scheme.IdealSheafData.notMem_support_of_ideal_eq_top ⟨V, hVaff⟩ hxV
      (htop ⟨V, hVaff⟩ hVU) hx
  · rw [← hJsupp]
    exact fun x hx ↦ Scheme.IdealSheafData.support_antitone hle hx

end AlgebraicGeometry

end
