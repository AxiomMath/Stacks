module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.SingleHomology
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Dualizing.PowerTorsionComparison.LocalCohomologyFunctor
public import StacksFrontier.RingTheory.LocalCohomology.LowDegree

/-!
# The localization triangle and the low-degree sequence for local cohomology

Let `I` be a finitely generated ideal of a commutative ring `A` and let `U = Spec A \ V(I)`.
For an `A`-module `M` the counit of the local-cohomology adjunction (Stacks 0A6Q) is a map
`RΓ_{V(I)}(M) ⟶ M` in the derived category of `A`-modules, and its cone is derived sections on
`U`. Taking cohomology of that distinguished triangle produces the five-term sequence
`0 ⟶ H⁰_I(M) ⟶ M ⟶ Γ(U, M̃|U) ⟶ H¹_I(M) ⟶ 0` of Stacks 0DWR.

This file carries the structure that packages the localization triangle together with the two
pieces of data that are not determined by the triangle itself — the identification of the
degree-zero cohomology of the cone with sections on `U`, and the fact that the resulting map
out of `M` is `m ↦ m/1` — and the two naturality results about the maps the triangle produces.

The sheaf of modules associated to a module whose universe is independent of the ring's is built
here as well, on top of the locally fractional sections of
`StacksFrontier/RingTheory/LocalCohomology/LowDegree.lean`: the action of the structure sheaf on
those sections is the content of `Stacks.LocalCohomology.sectionsModule`, and
`Stacks.LocalCohomology.associatedSheaf_eq_tilde` records that in a common universe the result
is Mathlib's `AlgebraicGeometry.tilde`.

## Main definitions

* `Stacks.LocalCohomology.sectionsModule` — locally fractional sections of a module as a module
  over the locally fractional sections of the ring.
* `Stacks.LocalCohomology.associatedSheaf` — the associated sheaf of modules on `Spec A`, for a
  module of independent universe.
* `Stacks.LocalCohomology.complementTilde` — its restriction to `U = Spec A \ V(I)`.
* `Stacks.LocalCohomology.localCohomologyDerived`,
  `Stacks.LocalCohomology.localCohomologyModule`,
  `Stacks.LocalCohomology.localCohomologyOnModules` — local cohomology as an endofunctor of the
  derived category, the local cohomology modules of a module, and local cohomology as a functor
  on modules.
* `Stacks.LocalCohomology.localCohomologyZeroToModule` — the canonical map `H⁰_I(M) ⟶ M`.
* `Stacks.LocalCohomology.LocalizationTriangleData` — the localization triangle together with its
  degree-zero sections comparison.
* `Stacks.LocalCohomology.restrictionToComplement`,
  `Stacks.LocalCohomology.localizationBoundary` — the restriction map `M → Γ(U, F)` and the
  connecting map `Γ(U, F) → H¹_I(M)`.

## Main results

* `Stacks.LocalCohomology.associatedSheaf_eq_tilde` — agreement with Mathlib's `tilde` in a
  common universe.
* `Stacks.LocalCohomology.restrictionToComplement_apply` — the restriction map sends `m` to the
  section `m/1`.
* `Stacks.LocalCohomology.localizationBoundary_naturality` — the connecting map is natural in
  the module.
* `Stacks.LocalCohomology.exact_localCohomologyZeroToModule_restrictionToComplement`,
  `Stacks.LocalCohomology.exact_restrictionToComplement_localizationBoundary`,
  `Stacks.LocalCohomology.localizationBoundary_surjective` — the three statements of Stacks 0DWR
  that the long exact homology sequence of the localization triangle gives at once. The remaining
  one, injectivity of `H⁰_I(M) ⟶ M`, is equivalent to the vanishing of `H⁻¹` of derived sections
  on `U` and is not a consequence of the triangle alone.

## Implementation notes

Mathlib's `AlgebraicGeometry.StructureSheaf.sectionsSubalgebraSubmodule` needs
`set_option backward.isDefEq.respectTransparency false` because the instance
`Module ↥(sectionsSubalgebra A U) (Π x : U, Localizations M x)` is only found after unfolding the
coercion of a subalgebra to a subsemiring. Supplying that instance explicitly, as
`Stacks.LocalCohomology.modulePiLocalizedModule`, removes the need for the option, and a single
`change` past the semireducible presheaf of abelian groups does the same for the sheaf condition.

The existence of a `LocalizationTriangleData` is not established here: the counit of Stacks 0A6Q
is obtained from an abstract coreflection, so identifying the cone of the counit with derived
sections on `U` — which is what `LocalizationTriangleData.sectionsIso` and
`LocalizationTriangleData.restriction_eq` record — requires the Čech model of local cohomology
for a finite set of generators of `I`. Everything in this file is stated for a given
`LocalizationTriangleData`.

## References

* [Stacks Project, Tag 0DWR](https://stacks.math.columbia.edu/tag/0DWR)
* [Stacks Project, Tag 0A6Q](https://stacks.math.columbia.edu/tag/0A6Q)
* [Stacks Project, Tag 08D0](https://stacks.math.columbia.edu/tag/08D0)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open CategoryTheory.Pretriangulated

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.LocalCohomology

variable {A : Type u} [CommRing A]

/-- The locally fractional sections of the ring act on all dependent families of elements of the
localizations of a module, componentwise. This is the instance that Mathlib's
`AlgebraicGeometry.StructureSheaf.sectionsSubalgebraSubmodule` finds by unfolding the coercion
from subalgebras to subsemirings; naming it makes that definitional step unnecessary. -/
instance modulePiLocalizedModule (M : ModuleCat.{v} A) (U : Opens (PrimeSpectrum.Top A)) :
    Module (StructureSheaf.sectionsSubalgebra A U)
      (∀ x : U, LocalizedModule x.1.asIdeal.primeCompl M) :=
  Subsemiring.instModuleSubtypeMem (StructureSheaf.sectionsSubalgebra A U).toSubsemiring

/-- Locally fractional sections of a module, as a module over the locally fractional sections of
the ring. This is Mathlib's `AlgebraicGeometry.StructureSheaf.sectionsSubalgebraSubmodule` with
the module universe independent of the ring universe. -/
def sectionsModule (M : ModuleCat.{v} A) (U : Opens (PrimeSpectrum.Top A)) :
    Submodule (StructureSheaf.sectionsSubalgebra A U)
      (∀ x : U, LocalizedModule x.1.asIdeal.primeCompl M) where
  __ := moduleSections M U
  smul_mem' r {a} ha x := by
    obtain ⟨V, hxV, hVU, rx, rs, hr⟩ := r.2 x
    obtain ⟨W, hxW, hWU, ax, as, ha⟩ := ha x
    refine ⟨V ⊓ W, ⟨hxV, hxW⟩, homOfLE (inf_le_left.trans hVU.le), rx • ax, as * rs,
      fun y ↦ ?_⟩
    obtain ⟨hrsy, hry⟩ := hr ⟨y.1, y.2.1⟩
    obtain ⟨hasy, hay⟩ := ha ⟨y.1, y.2.2⟩
    exact ⟨y.1.asIdeal.primeCompl.mul_mem hasy hrsy, congr($hry • $hay)⟩

/-- In a common universe this is Mathlib's submodule of locally fractional sections. -/
theorem sectionsModule_eq (M : ModuleCat.{u} A) (U : Opens (PrimeSpectrum.Top A)) :
    sectionsModule M U = StructureSheaf.sectionsSubalgebraSubmodule M U := rfl

variable (A) in
/-- The sheaf of modules on `Spec A` associated to an `A`-module whose universe is independent of
the universe of `A`: the locally fractional sections, with the structure-sheaf action of
`sectionsModule`. -/
def associatedSheaf (M : ModuleCat.{v} A) :
    SheafOfModules.{max u v} (Spec (CommRingCat.of A)).ringCatSheaf where
  val := by
    letI (U : (Spec (CommRingCat.of A)).Opensᵒᵖ) :
        Module ((Spec (CommRingCat.of A)).ringCatSheaf.obj.obj U)
          ((associatedAbPresheaf M).obj U) :=
      (sectionsModule M U.unop).module
    exact .ofPresheaf (associatedAbPresheaf M) (fun _ _ _ _ _ ↦ rfl)
  isSheaf := by
    change (associatedAbPresheaf M).IsSheaf
    exact associatedAbPresheaf_isSheaf M

/-- When the ring and the module share a universe, the associated sheaf is Mathlib's `tilde`. -/
theorem associatedSheaf_eq_tilde (M : ModuleCat.{u} A) : associatedSheaf A M = tilde M := rfl

variable (A) in
/-- The restriction to `U = Spec A \ V(I)` of the sheaf associated to `M`, with the module
universe independent of the universe of `A`. -/
abbrev complementTilde (I : Ideal A) (M : ModuleCat.{v} A) :=
  (restrictFunctor (complementZeroLocus A I).ι).obj (associatedSheaf A M)

/-- Local cohomology with support in `V(I)` as an endofunctor of `D(A)`: the coreflection onto
the objects with `I`-power-torsion cohomology of Stacks 0A6Q, followed by the inclusion of that
subcategory. -/
abbrev localCohomologyDerived (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG) :
    DerivedCategory (ModuleCat.{v} A) ⥤ DerivedCategory (ModuleCat.{v} A) :=
  Dualizing.localCohomologyFunctor A I hI ⋙ (Dualizing.derivedPowerTorsionProperty A I hI).ι

/-- The `i`-th local cohomology module of `M` with support in `V(I)`. -/
abbrev localCohomologyModule
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)
    (M : ModuleCat.{v} A) (i : ℤ) : ModuleCat.{v} A :=
  (DerivedCategory.homologyFunctor (ModuleCat.{v} A) i).obj
    ((Dualizing.derivedPowerTorsionProperty A I hI).ι.obj
      ((Dualizing.localCohomologyFunctor A I hI).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj M)))

/-- The canonical map `H⁰_I(M) ⟶ M`, the degree-zero cohomology of the counit of the
local-cohomology adjunction of Stacks 0A6Q. -/
def localCohomologyZeroToModule
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)
    (M : ModuleCat.{v} A) : localCohomologyModule A I hI M 0 ⟶ M :=
  (DerivedCategory.homologyFunctor (ModuleCat.{v} A) 0).map
      ((Dualizing.localCohomologyAdjunction A I hI).counit.app
        ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj M)) ≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso
      (ModuleCat.{v} A) 0).hom.app M

/-- Local cohomology with support in `V(I)`, applied to a module placed in degree zero and
regarded as a functor on modules. -/
abbrev localCohomologyOnModules (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG) :
    ModuleCat.{v} A ⥤ DerivedCategory (ModuleCat.{v} A) :=
  DerivedCategory.singleFunctor (ModuleCat.{v} A) 0 ⋙
    Dualizing.localCohomologyFunctor A I hI ⋙
      (Dualizing.derivedPowerTorsionProperty A I hI).ι

variable (A) in
/-- The affine localization triangle, including its comparison with sections on
`U = Spec A \ V(I)`. Its first map is the local-cohomology counit, its second map induces
restriction of sections, and its third map is natural in the module. The degree-zero comparison
is natural as well, so the transported boundary map is natural. -/
structure LocalizationTriangleData (I : Ideal A) (hI : I.FG) where
  /-- Derived sections on the complement, the third object of the localization triangle. -/
  complement : ModuleCat.{v} A ⥤ DerivedCategory (ModuleCat.{v} A)
  /-- The second map of the localization triangle, inducing restriction of sections. -/
  restriction : DerivedCategory.singleFunctor (ModuleCat.{v} A) 0 ⟶ complement
  /-- The third map of the localization triangle, the source of the connecting map. -/
  boundary : complement ⟶ localCohomologyOnModules A I hI ⋙
    shiftFunctor (DerivedCategory (ModuleCat.{v} A)) (1 : ℤ)
  /-- The localization triangle is distinguished, with the counit as its first map. -/
  distinguished (M : ModuleCat.{v} A) :
    Triangle.mk
      ((Dualizing.localCohomologyAdjunction A I hI).counit.app
        ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj M))
      (restriction.app M) (boundary.app M) ∈ distTriang _
  /-- The usual identification `H⁰(RΓ(U, M̃|U)) = Γ(U, M̃|U)`.
  A linear equivalence accommodates independently sized modules and section types. -/
  sectionsIso (M : ModuleCat.{v} A) :
    (DerivedCategory.homologyFunctor (ModuleCat.{v} A) 0).obj (complement.obj M) ≃ₗ[A]
      complementGlobalSections A I (complementTilde A I M)
  /-- The identification of degree-zero cohomology with sections is natural in the module. -/
  sectionsIso_naturality {M N : ModuleCat.{v} A} (f : M ⟶ N)
      (x : (DerivedCategory.homologyFunctor (ModuleCat.{v} A) 0).obj (complement.obj M)) :
    sectionsIso N ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) 0).map
        (complement.map f) x) =
      (associatedAbPresheafMap f).app
        (op ((complementZeroLocus A I).ι ''ᵁ ⊤)) (sectionsIso M x)
  /-- The map induced by the second arrow sends `m` to the section `m/1`. -/
  restriction_eq (M : ModuleCat.{v} A) (m : M) :
    sectionsIso M ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) 0).map
      (restriction.app M)
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso
          (ModuleCat.{v} A) 0).inv.app M m)) =
      ⟨fun x ↦ LocalizedModule.mk m (1 : x.1.asIdeal.primeCompl),
        fun x ↦ ⟨_, x.2, 𝟙 _, m, 1, fun y ↦ ⟨by simp [Ideal.IsPrime.one_notMem], rfl⟩⟩⟩

/-- The affine localization triangle evaluated at a module. -/
def LocalizationTriangleData.triangle
    {I : Ideal A} {hI : I.FG} (D : LocalizationTriangleData.{u, v} A I hI)
    (M : ModuleCat.{v} A) : Triangle (DerivedCategory (ModuleCat.{v} A)) :=
  Triangle.mk
    ((Dualizing.localCohomologyAdjunction A I hI).counit.app
      ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj M))
    (D.restriction.app M) (D.boundary.app M)

/-- A module map gives a morphism of the localization triangles. -/
def LocalizationTriangleData.triangleMap
    {I : Ideal A} {hI : I.FG} (D : LocalizationTriangleData.{u, v} A I hI)
    {M N : ModuleCat.{v} A} (f : M ⟶ N) : D.triangle M ⟶ D.triangle N where
  hom₁ := (localCohomologyOnModules A I hI).map f
  hom₂ := (DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).map f
  hom₃ := D.complement.map f
  comm₁ := ((Dualizing.localCohomologyAdjunction A I hI).counit.naturality
    ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).map f)).symm
  comm₂ := (D.restriction.naturality f).symm
  comm₃ := (D.boundary.naturality f).symm

/-- The comparison `H⁰(RΓ(U, M̃|U)) ≃ Γ(U, F)`, transported through an identification `e` of `F`
with the restriction of the associated sheaf. -/
def LocalizationTriangleData.sectionsIsoOfIso
    {I : Ideal A} {hI : I.FG} (D : LocalizationTriangleData.{u, v} A I hI)
    (M : ModuleCat.{v} A)
    (F : SheafOfModules.{max u v} (complementZeroLocus A I : Scheme).ringCatSheaf)
    (e : F ≅ complementTilde A I M) :
    (DerivedCategory.homologyFunctor (ModuleCat.{v} A) 0).obj (D.complement.obj M) ≃ₗ[A]
      complementGlobalSections A I F :=
  (D.sectionsIso M).trans
    ((complementGlobalSectionsFunctor A I).mapIso e.symm).toLinearEquiv

/-- Restriction of sections, transported through the chosen identification with `F`. The field
`LocalizationTriangleData.restriction_eq` specifies its value as `m/1`. -/
def restrictionToComplement
    {I : Ideal A} {hI : I.FG} (D : LocalizationTriangleData.{u, v} A I hI)
    (M : ModuleCat.{v} A)
    (F : SheafOfModules.{max u v} (complementZeroLocus A I : Scheme).ringCatSheaf)
    (e : F ≅ complementTilde A I M) : M →ₗ[A] complementGlobalSections A I F :=
  (D.sectionsIsoOfIso M F e).toLinearMap.comp
    (((DerivedCategory.homologyFunctor (ModuleCat.{v} A) 0).map
      (D.restriction.app M)).hom.comp
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso
          (ModuleCat.{v} A) 0).inv.app M).hom)

/-- The localization boundary: the connecting map of the distinguished triangle, transported
through the canonical degree-zero sections comparison and `e`. -/
def localizationBoundary
    {I : Ideal A} {hI : I.FG} (D : LocalizationTriangleData.{u, v} A I hI)
    (M : ModuleCat.{v} A)
    (F : SheafOfModules.{max u v} (complementZeroLocus A I : Scheme).ringCatSheaf)
    (e : F ≅ complementTilde A I M) :
    complementGlobalSections A I F →ₗ[A] localCohomologyModule A I hI M 1 :=
  (DerivedCategory.HomologySequence.δ (D.triangle M) 0 1).hom.comp
    (D.sectionsIsoOfIso M F e).symm.toLinearMap

/-- The restriction map sends `m` to `m/1`, followed by the identification with `F`. -/
theorem restrictionToComplement_apply
    {I : Ideal A} {hI : I.FG} (D : LocalizationTriangleData.{u, v} A I hI)
    (M : ModuleCat.{v} A)
    (F : SheafOfModules.{max u v} (complementZeroLocus A I : Scheme).ringCatSheaf)
    (e : F ≅ complementTilde A I M) (m : M) :
    restrictionToComplement D M F e m = (e.inv.val.app (op ⊤))
      ⟨fun x ↦ LocalizedModule.mk m (1 : x.1.asIdeal.primeCompl),
        fun x ↦ ⟨_, x.2, 𝟙 _, m, 1, fun y ↦ ⟨by simp [Ideal.IsPrime.one_notMem], rfl⟩⟩⟩ :=
  congrArg (fun s ↦ (e.inv.val.app (op ⊤)) s) (D.restriction_eq M m)

/-- A module placed in degree zero has no cohomology in degree one. -/
theorem isZero_homologyFunctor_one_singleFunctor_obj (M : ModuleCat.{v} A) :
    Limits.IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) 1).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj M)) :=
  Limits.IsZero.of_iso
    (HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ) 0 M 1 one_ne_zero)
    ((DerivedCategory.homologyFunctorFactors (ModuleCat.{v} A) 1).app _)

/-- The sequence `H⁰_I(M) ⟶ M ⟶ Γ(U, F)` is exact: a module element whose restriction to
`U = Spec A \ V(I)` vanishes comes from degree-zero local cohomology. -/
theorem exact_localCohomologyZeroToModule_restrictionToComplement
    {I : Ideal A} {hI : I.FG} (D : LocalizationTriangleData.{u, v} A I hI)
    (M : ModuleCat.{v} A)
    (F : SheafOfModules.{max u v} (complementZeroLocus A I : Scheme).ringCatSheaf)
    (e : F ≅ complementTilde A I M) :
    Function.Exact (localCohomologyZeroToModule A I hI M)
      (restrictionToComplement D M F e) :=
  have h := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
    (DerivedCategory.HomologySequence.exact₂ (D.triangle M) (D.distinguished M) 0)
  (LinearEquiv.conj_exact_iff_exact _ _
      (((DerivedCategory.singleFunctorCompHomologyFunctorIso
        (ModuleCat.{v} A) 0).app M).toLinearEquiv)).2
    ((LinearEquiv.postcomp_exact_iff_exact (e := D.sectionsIsoOfIso M F e)).2 h)

/-- The sequence `M ⟶ Γ(U, F) ⟶ H¹_I(M)` is exact: a section on `U = Spec A \ V(I)` killed by
the connecting map is the restriction of a module element. -/
theorem exact_restrictionToComplement_localizationBoundary
    {I : Ideal A} {hI : I.FG} (D : LocalizationTriangleData.{u, v} A I hI)
    (M : ModuleCat.{v} A)
    (F : SheafOfModules.{max u v} (complementZeroLocus A I : Scheme).ringCatSheaf)
    (e : F ≅ complementTilde A I M) :
    Function.Exact (restrictionToComplement D M F e) (localizationBoundary D M F e) :=
  have h := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
    (DerivedCategory.HomologySequence.exact₃ (D.triangle M) (D.distinguished M) 0 1 rfl)
  have h2 := (LinearEquiv.precomp_exact_iff_exact
    (e := (((DerivedCategory.singleFunctorCompHomologyFunctorIso
      (ModuleCat.{v} A) 0).app M).toLinearEquiv).symm)).2 h
  (LinearEquiv.conj_exact_iff_exact
    (P := localCohomologyModule A I hI M 1) _ _ (D.sectionsIsoOfIso M F e)).2 h2

/-- The connecting map `Γ(U, F) ⟶ H¹_I(M)` is surjective, because a module placed in degree zero
has no cohomology in degree one. -/
theorem localizationBoundary_surjective
    {I : Ideal A} {hI : I.FG} (D : LocalizationTriangleData.{u, v} A I hI)
    (M : ModuleCat.{v} A)
    (F : SheafOfModules.{max u v} (complementZeroLocus A I : Scheme).ringCatSheaf)
    (e : F ≅ complementTilde A I M) :
    Function.Surjective (localizationBoundary D M F e) := by
  have h := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
    (DerivedCategory.HomologySequence.exact₁ (D.triangle M) (D.distinguished M) 0 1 rfl)
  intro x
  have hx := ConcreteCategory.congr_hom
    ((isZero_homologyFunctor_one_singleFunctor_obj M).eq_of_tgt
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) 1).map (D.triangle M).mor₁) 0) x
  simp only [ModuleCat.hom_zero] at hx
  obtain ⟨y, hy⟩ := (h x).1 hx
  refine ⟨D.sectionsIsoOfIso M F e y, ?_⟩
  exact (congrArg (DerivedCategory.HomologySequence.δ (D.triangle M) 0 1).hom
    ((D.sectionsIsoOfIso M F e).symm_apply_apply y)).trans hy

/-- Naturality of the localization boundary, on sections of the associated sheaves. -/
theorem localizationBoundary_naturality
    {I : Ideal A} {hI : I.FG} (D : LocalizationTriangleData.{u, v} A I hI)
    {M N : ModuleCat.{v} A} (f : M ⟶ N)
    (s : complementGlobalSections A I (complementTilde A I M)) :
    localizationBoundary D N (complementTilde A I N) (Iso.refl _)
        ((associatedAbPresheafMap f).app
          (op ((complementZeroLocus A I).ι ''ᵁ ⊤)) s) =
      (DerivedCategory.homologyFunctor (ModuleCat.{v} A) 1).map
        ((localCohomologyOnModules A I hI).map f)
          (localizationBoundary D M (complementTilde A I M) (Iso.refl _) s) := by
  have h := (DerivedCategory.homologyFunctor (ModuleCat.{v} A) 0).homologySequenceδ_naturality
    (D.triangleMap f) 0 1 rfl
  have hs := D.sectionsIso_naturality f ((D.sectionsIso M).symm s)
  simp only [LinearEquiv.apply_symm_apply] at hs
  show (DerivedCategory.HomologySequence.δ (D.triangle N) 0 1)
      ((D.sectionsIso N).symm _) = _
  rw [← hs, LinearEquiv.symm_apply_apply]
  exact ConcreteCategory.congr_hom h ((D.sectionsIso M).symm s)

end Stacks.LocalCohomology
