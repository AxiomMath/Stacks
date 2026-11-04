module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.SingleHomology
public import StacksFrontier.Algebra.Module.Matlis
public import StacksFrontier.RingTheory.LocalCohomology.DepthExtension.DegreeZero
public import StacksFrontier.RingTheory.LocalCohomology.DepthVanishing.Triangulated

/-!
# Modules supported in `T` are acyclic for sections with support in `T`

Let `A` be a commutative ring and `T ⊆ Spec(A)` a subset. Sections with support in `T` come with
a canonical comparison map
$$ \gamma_M \colon \Gamma_T(M) \longrightarrow H^0_T(M), $$
natural in the `A`-module `M`, obtained from the unit of the right derived functor. This file
shows that `γ` is an isomorphism and deduces that a module `N` whose support lies in `T` is
acyclic for sections with support in `T`:

`H^0_T(N) = N` and `H^i_T(N) = 0` for `i > 0`.

## Main definitions

* `Stacks.LocalCohomology.localCohomologyWithSupportInFunctor` — degree-`i` local cohomology with
  support in `T` as a functor on `A`-modules.
* `Stacks.LocalCohomology.sectionsToLocalCohomologyZero` — the comparison `γ`.

## Main results

* `Stacks.LocalCohomology.isIso_sectionsToLocalCohomologyZero` — **`γ_M` is an isomorphism** for
  every `A`-module `M`.
* `Stacks.LocalCohomology.isZero_localCohomologyWithSupportIn_of_support_subset` —
  **`H^i_T(N) = 0` for `i > 0`** when the support of `N` is contained in `T`, with `A` Noetherian
  and `T` stable under specialization.
* `Stacks.LocalCohomology.sectionsIsoLocalCohomologyZero` — the resulting natural isomorphism
  `Γ_T ≅ H^0_T`, which for a module supported in `T` reads `H^0_T(N) ≅ N`.

## Implementation notes

The comparison `γ` is assembled from the canonical comparison
`Stacks.LocalCohomology.derivedSectionsWithSupportInUnit` of the right derived functor, whiskered
on the left with the single-complex functor followed by the homotopy-category quotient and on the
right with the degree-zero homology functor, and sandwiched between the structural isomorphisms
`HomologicalComplex.singleMapHomologicalComplex`,
`CategoryTheory.Functor.mapHomotopyCategoryFactors`,
`DerivedCategory.homologyFunctorFactors`, `DerivedCategory.quotientCompQhIso` and
`HomologicalComplex.homologyFunctorSingleIso`. Building it this way makes naturality in `M`
automatic, which is the only property of `γ` that the degree-zero comparison
`Stacks.LocalCohomology.nonempty_localCohomologyWithSupportIn_zero_iso` does not already supply
and the whole reason for constructing it.

That `γ_M` is invertible is proved in three steps. For `E` injective the single complex `E[0]` is
K-injective, so the whiskered unit is invertible at `E` by
`Stacks.LocalCohomology.isIso_derivedSectionsWithSupportInUnit_app` and `γ_E` is a composite of
isomorphisms. For general `M`, embed `M` in an injective `E`: naturality of `γ` together with
left exactness of `Γ_T` makes `γ_M` a monomorphism. Knowing `γ` to be a monomorphism everywhere,
the same embedding and the two four-term exact sequences — the one coming from left exactness of
`Γ_T` and the one coming from the long exact sequence of local cohomology, whose left-hand
vanishing is `Stacks.LocalCohomology.isZero_localCohomologyWithSupportIn_of_neg` — make `γ_M` an
epimorphism by a diagram chase.

Acyclicity then follows by induction on the degree. For `N` supported in `T` choose, with
`Stacks.LocalCohomology.exists_injective_supported_envelope`, a monomorphism `N ⟶ J` with `J`
injective and supported in `T`; the cokernel `C` is supported in `T` as well, because modules
supported in `T` form a Serre class. In degree one the connecting map `H^0_T(C) ⟶ H^1_T(N)`
vanishes, because `γ` identifies `H^0_T(J) ⟶ H^0_T(C)` with the epimorphism `J ⟶ C`; in higher
degrees the long exact sequence reduces degree `i + 1` for `N` to degree `i` for `C`.

No `@[stacks]` attribute is placed. The assertions proved here are what
[Stacks, Remark 0EF4] means by the construction of `RΓ_T`, and the covering set of that tag in
this library consists of the declarations of
`StacksFrontier/RingTheory/LocalCohomology/SectionsWithSupport.lean`,
`StacksFrontier/RingTheory/LocalCohomology/BoundedComparison.lean` and
`StacksFrontier/RingTheory/LocalCohomology/Sweep/ClosedSupportColimit.lean`, none of which is
restated here.

## References

* [Stacks Project, Tag 0EF4](https://stacks.math.columbia.edu/tag/0EF4)
* [Stacks Project, Tag 0EEZ](https://stacks.math.columbia.edu/tag/0EEZ)
* [Stacks Project, Tag 0AW8](https://stacks.math.columbia.edu/tag/0AW8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.LocalCohomology

variable (A : Type u) [CommRing A] (T : Set (PrimeSpectrum A))

/-! ### The comparison from sections with support to degree-zero local cohomology -/

/-- Degree-`i` local cohomology with support in `T`, as a functor on `A`-modules: place the
module in degree zero, apply derived sections with support in `T`, take the `i`-th homology. -/
abbrev localCohomologyWithSupportInFunctor (i : ℤ) :
    ModuleCat.{max u v} A ⥤ ModuleCat.{max u v} A :=
  DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0 ⋙
    derivedSectionsWithSupportIn.{u, v} A T ⋙
      DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i

/-- Sections with support in `T` are the degree-zero homology of the complex of sections with
support in `T` of a module placed in degree zero. -/
def sectionsWithSupportInIsoSingleHomology :
    sectionsWithSupportInFunctor.{u, v} A T ≅
      CochainComplex.singleFunctor (ModuleCat.{max u v} A) 0 ⋙
        (sectionsWithSupportInFunctor.{u, v} A T).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          DerivedCategory.Q ⋙ DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) 0 :=
  (Functor.rightUnitor (sectionsWithSupportInFunctor.{u, v} A T)).symm ≪≫
    Functor.isoWhiskerLeft (sectionsWithSupportInFunctor.{u, v} A T)
      (HomologicalComplex.homologyFunctorSingleIso (ModuleCat.{max u v} A)
        (ComplexShape.up ℤ) 0).symm ≪≫
    Functor.isoWhiskerRight
      (HomologicalComplex.singleMapHomologicalComplex
        (sectionsWithSupportInFunctor.{u, v} A T) (ComplexShape.up ℤ) 0).symm
      (HomologicalComplex.homologyFunctor (ModuleCat.{max u v} A) (ComplexShape.up ℤ) 0) ≪≫
    Functor.isoWhiskerLeft
      (CochainComplex.singleFunctor (ModuleCat.{max u v} A) 0 ⋙
        (sectionsWithSupportInFunctor.{u, v} A T).mapHomologicalComplex (ComplexShape.up ℤ))
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{max u v} A) 0).symm

/-- Passing from cochain complexes to the homotopy category inside the degree-zero homology of
the complex of sections with support in `T`. -/
def singleHomologyIsoHomotopyCategory :
    CochainComplex.singleFunctor (ModuleCat.{max u v} A) 0 ⋙
        (sectionsWithSupportInFunctor.{u, v} A T).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          DerivedCategory.Q ⋙ DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) 0 ≅
      CochainComplex.singleFunctor (ModuleCat.{max u v} A) 0 ⋙
        HomotopyCategory.quotient (ModuleCat.{max u v} A) (ComplexShape.up ℤ) ⋙
          (sectionsWithSupportInFunctor.{u, v} A T).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
            DerivedCategory.Qh ⋙
              DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) 0 :=
  Functor.isoWhiskerLeft (CochainComplex.singleFunctor (ModuleCat.{max u v} A) 0)
    (Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft
          ((sectionsWithSupportInFunctor.{u, v} A T).mapHomologicalComplex (ComplexShape.up ℤ))
          (DerivedCategory.quotientCompQhIso (ModuleCat.{max u v} A)).symm ≪≫
        Functor.isoWhiskerRight
          ((sectionsWithSupportInFunctor.{u, v} A T).mapHomotopyCategoryFactors
            (ComplexShape.up ℤ)).symm DerivedCategory.Qh)
      (DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) 0))

/-- The derived comparison, whiskered into degree-zero homology of a module placed in degree
zero. -/
def whiskeredDerivedSectionsWithSupportInUnit :
    CochainComplex.singleFunctor (ModuleCat.{max u v} A) 0 ⋙
        HomotopyCategory.quotient (ModuleCat.{max u v} A) (ComplexShape.up ℤ) ⋙
          (sectionsWithSupportInFunctor.{u, v} A T).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
            DerivedCategory.Qh ⋙
              DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) 0 ⟶
      CochainComplex.singleFunctor (ModuleCat.{max u v} A) 0 ⋙
        HomotopyCategory.quotient (ModuleCat.{max u v} A) (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh ⋙ derivedSectionsWithSupportIn.{u, v} A T ⋙
            DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) 0 :=
  Functor.whiskerLeft
    (CochainComplex.singleFunctor (ModuleCat.{max u v} A) 0 ⋙
      HomotopyCategory.quotient (ModuleCat.{max u v} A) (ComplexShape.up ℤ))
    (Functor.whiskerRight (derivedSectionsWithSupportInUnit.{u, v} A T)
      (DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) 0))

/-- Passing back from the homotopy category to the derived category. -/
def homotopyCategoryIsoLocalCohomologyZero :
    CochainComplex.singleFunctor (ModuleCat.{max u v} A) 0 ⋙
        HomotopyCategory.quotient (ModuleCat.{max u v} A) (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh ⋙ derivedSectionsWithSupportIn.{u, v} A T ⋙
            DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) 0 ≅
      localCohomologyWithSupportInFunctor.{u, v} A T 0 :=
  Functor.isoWhiskerLeft (CochainComplex.singleFunctor (ModuleCat.{max u v} A) 0)
      (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso (ModuleCat.{max u v} A))
        (derivedSectionsWithSupportIn.{u, v} A T ⋙
          DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) 0)) ≪≫
    Functor.isoWhiskerRight
      (DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{max u v} A) 0).symm
      (derivedSectionsWithSupportIn.{u, v} A T ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) 0)

/-- The canonical comparison `γ_M : Γ_T(M) ⟶ H^0_T(M)` from the sections of `M` with support in
`T` to the degree-zero local cohomology of `M` with support in `T`, natural in `M`. -/
def sectionsToLocalCohomologyZero :
    sectionsWithSupportInFunctor.{u, v} A T ⟶
      localCohomologyWithSupportInFunctor.{u, v} A T 0 :=
  (sectionsWithSupportInIsoSingleHomology.{u, v} A T).hom ≫
    (singleHomologyIsoHomotopyCategory.{u, v} A T).hom ≫
      whiskeredDerivedSectionsWithSupportInUnit.{u, v} A T ≫
        (homotopyCategoryIsoLocalCohomologyZero.{u, v} A T).hom

/-- The map induced on degree-`i` local cohomology by a map of modules is the one obtained from
the functor `localCohomologyWithSupportInFunctor`. -/
lemma localCohomologyWithSupportInFunctor_map (i : ℤ) {M N : ModuleCat.{max u v} A} (f : M ⟶ N) :
    (localCohomologyWithSupportInFunctor.{u, v} A T i).map f = localCohomologyMap A T i f := rfl

/-- The component of the whiskered comparison at a module is the degree-zero homology of the
canonical comparison at the single complex of that module. -/
lemma whiskeredDerivedSectionsWithSupportInUnit_app (M : ModuleCat.{max u v} A) :
    (whiskeredDerivedSectionsWithSupportInUnit.{u, v} A T).app M =
      (DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) 0).map
        ((derivedSectionsWithSupportInUnit.{u, v} A T).app
          ((HomotopyCategory.quotient (ModuleCat.{max u v} A) (ComplexShape.up ℤ)).obj
            ((CochainComplex.singleFunctor (ModuleCat.{max u v} A) 0).obj M))) := rfl

/-- The component of `γ` at a module, written out as a composite. -/
lemma sectionsToLocalCohomologyZero_app (M : ModuleCat.{max u v} A) :
    (sectionsToLocalCohomologyZero.{u, v} A T).app M =
      (sectionsWithSupportInIsoSingleHomology.{u, v} A T).hom.app M ≫
        (singleHomologyIsoHomotopyCategory.{u, v} A T).hom.app M ≫
          (whiskeredDerivedSectionsWithSupportInUnit.{u, v} A T).app M ≫
            (homotopyCategoryIsoLocalCohomologyZero.{u, v} A T).hom.app M := rfl

/-! ### The comparison is an isomorphism -/

/-- **`γ_E` is invertible for `E` an injective module.** The single complex of an injective module
is K-injective, so the canonical comparison of the derived functor is invertible there. -/
instance isIso_sectionsToLocalCohomologyZero_app_of_injective (E : ModuleCat.{max u v} A)
    [CategoryTheory.Injective E] :
    IsIso ((sectionsToLocalCohomologyZero.{u, v} A T).app E) := by
  have hKI : ((CochainComplex.singleFunctor (ModuleCat.{max u v} A) 0).obj E).IsKInjective :=
    isKInjective_singleFunctor_obj_of_injective.{u, v} E
  have hunit : IsIso ((whiskeredDerivedSectionsWithSupportInUnit.{u, v} A T).app E) := by
    rw [whiskeredDerivedSectionsWithSupportInUnit_app]
    infer_instance
  rw [sectionsToLocalCohomologyZero_app]
  infer_instance

/-- Sections with support in `T` preserve monomorphisms: an injective map does not identify
distinct sections. -/
lemma mono_sectionsWithSupportInFunctor_map {M N : ModuleCat.{max u v} A} (f : M ⟶ N) [Mono f] :
    Mono ((sectionsWithSupportInFunctor.{u, v} A T).map f) := by
  rw [ModuleCat.mono_iff_injective]
  intro x y hxy
  refine Subtype.ext ((ModuleCat.mono_iff_injective f).mp ‹Mono f› ?_)
  rw [← sectionsWithSupportInFunctor_map_val A T f x,
    ← sectionsWithSupportInFunctor_map_val A T f y]
  exact congrArg Subtype.val hxy

/-- Naturality of `γ`, read on elements. -/
lemma sectionsToLocalCohomologyZero_naturality_apply {M N : ModuleCat.{max u v} A} (g : M ⟶ N)
    (y : (sectionsWithSupportInFunctor.{u, v} A T).obj M) :
    ((sectionsToLocalCohomologyZero.{u, v} A T).app N).hom
        (((sectionsWithSupportInFunctor.{u, v} A T).map g).hom y) =
      ((localCohomologyWithSupportInFunctor.{u, v} A T 0).map g).hom
        (((sectionsToLocalCohomologyZero.{u, v} A T).app M).hom y) := by
  simp

/-- **`γ_M` is a monomorphism.** Embed `M` in an injective module `E`; the comparison at `E` is
invertible and `Γ_T` preserves the monomorphism `M ⟶ E`, so naturality exhibits `γ_M` as a factor
of a monomorphism. -/
lemma mono_sectionsToLocalCohomologyZero_app (M : ModuleCat.{max u v} A) :
    Mono ((sectionsToLocalCohomologyZero.{u, v} A T).app M) := by
  have : EnoughInjectives (ModuleCat.{max u v} A) := ModuleCat.enoughInjectives A
  have hmonoF := mono_sectionsWithSupportInFunctor_map.{u, v} A T (Injective.ι M)
  have hcomp : Mono ((sectionsWithSupportInFunctor.{u, v} A T).map (Injective.ι M) ≫
      (sectionsToLocalCohomologyZero.{u, v} A T).app (Injective.under M)) :=
    mono_comp' hmonoF inferInstance
  rw [(sectionsToLocalCohomologyZero.{u, v} A T).naturality (Injective.ι M)] at hcomp
  exact mono_of_mono ((sectionsToLocalCohomologyZero.{u, v} A T).app M)
    ((localCohomologyWithSupportInFunctor.{u, v} A T 0).map (Injective.ι M))

/-- **`γ_M` is an epimorphism,** given a monomorphism from `M` into an injective module `E`. Left
exactness of `Γ_T` and the long exact sequence of local cohomology give two four-term exact
sequences; the comparison is invertible at `E` and a monomorphism at the cokernel, which together
produce a preimage. -/
private lemma epi_sectionsToLocalCohomologyZero_app_of_mono (M E : ModuleCat.{max u v} A)
    [CategoryTheory.Injective E] (f : M ⟶ E) [Mono f] :
    Epi ((sectionsToLocalCohomologyZero.{u, v} A T).app M) := by
  have hepi : Epi (cokernel.π f) := inferInstanceAs (Epi (ShortComplex.cokernelSequence f).g)
  have hS : (ShortComplex.mk f (cokernel.π f) (cokernel.condition f)).ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.cokernelSequence_exact f) ‹Mono f› hepi
  have hFexact : ((ShortComplex.mk f (cokernel.π f) (cokernel.condition f)).map
      (sectionsWithSupportInFunctor.{u, v} A T)).Exact :=
    ((Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono
      (sectionsWithSupportInFunctor.{u, v} A T)).mp inferInstance _ hS).1
  have hδ : localCohomologyδ.{u, v} T hS (-1) 0 (by ring) = 0 :=
    (isZero_localCohomologyWithSupportIn_of_neg.{u, v} T (cokernel f) (-1)
      (by norm_num)).eq_of_src _ _
  have hmonoG : Mono ((localCohomologyWithSupportInFunctor.{u, v} A T 0).map f) :=
    (mono_localCohomologyMap_f_iff.{u, v} T hS (-1) 0 (by ring)).mpr hδ
  have hcompzero : (localCohomologyWithSupportInFunctor.{u, v} A T 0).map f ≫
      (localCohomologyWithSupportInFunctor.{u, v} A T 0).map (cokernel.π f) = 0 :=
    localCohomologyMap_comp_localCohomologyMap.{u, v} T hS 0
  have hmonoC := mono_sectionsToLocalCohomologyZero_app.{u, v} A T (cokernel f)
  rw [ModuleCat.epi_iff_surjective]
  intro x
  obtain ⟨y, hy⟩ := (ModuleCat.epi_iff_surjective
    ((sectionsToLocalCohomologyZero.{u, v} A T).app E)).mp inferInstance
      (((localCohomologyWithSupportInFunctor.{u, v} A T 0).map f).hom x)
  have hkey : ((sectionsToLocalCohomologyZero.{u, v} A T).app (cokernel f)).hom
      (((sectionsWithSupportInFunctor.{u, v} A T).map (cokernel.π f)).hom y) = 0 := by
    rw [sectionsToLocalCohomologyZero_naturality_apply, hy]
    have h := congrArg
      (fun φ : (localCohomologyWithSupportInFunctor.{u, v} A T 0).obj M ⟶
        (localCohomologyWithSupportInFunctor.{u, v} A T 0).obj (cokernel f) => φ.hom x)
      hcompzero
    simpa using h
  have hzero : ((sectionsWithSupportInFunctor.{u, v} A T).map (cokernel.π f)).hom y = 0 := by
    refine (ModuleCat.mono_iff_injective _).mp hmonoC ?_
    rw [hkey, map_zero]
  obtain ⟨z, hz⟩ := (ShortComplex.moduleCat_exact_iff _).mp hFexact y hzero
  have hz' : ((sectionsWithSupportInFunctor.{u, v} A T).map f).hom z = y := hz
  refine ⟨z, (ModuleCat.mono_iff_injective _).mp hmonoG ?_⟩
  rw [← sectionsToLocalCohomologyZero_naturality_apply, hz', hy]

/-- **`γ_M` is an epimorphism.** -/
lemma epi_sectionsToLocalCohomologyZero_app (M : ModuleCat.{max u v} A) :
    Epi ((sectionsToLocalCohomologyZero.{u, v} A T).app M) :=
  have : EnoughInjectives (ModuleCat.{max u v} A) := ModuleCat.enoughInjectives A
  epi_sectionsToLocalCohomologyZero_app_of_mono.{u, v} A T M (Injective.under M) (Injective.ι M)

/-- **The comparison `γ_M : Γ_T(M) ⟶ H^0_T(M)` is an isomorphism.** -/
instance isIso_sectionsToLocalCohomologyZero_app (M : ModuleCat.{max u v} A) :
    IsIso ((sectionsToLocalCohomologyZero.{u, v} A T).app M) :=
  have := mono_sectionsToLocalCohomologyZero_app.{u, v} A T M
  have := epi_sectionsToLocalCohomologyZero_app.{u, v} A T M
  isIso_of_mono_of_epi _

/-- **Sections with support in `T` are degree-zero local cohomology with support in `T`,**
naturally in the module. -/
def sectionsIsoLocalCohomologyZero :
    sectionsWithSupportInFunctor.{u, v} A T ≅
      localCohomologyWithSupportInFunctor.{u, v} A T 0 :=
  have : IsIso (sectionsToLocalCohomologyZero.{u, v} A T) := NatIso.isIso_of_isIso_app _
  asIso (sectionsToLocalCohomologyZero.{u, v} A T)

/-! ### Modules supported in `T` are acyclic -/

/-- If `X ⟶ Y` is an epimorphism and the support of `X` is contained in `T`, then
`Γ_T(X) ⟶ Γ_T(Y)` is an epimorphism: every section of `Y` lifts to `X`, and every element of `X`
is a `T`-supported section. -/
lemma epi_sectionsWithSupportInFunctor_map_of_support_subset {X Y : ModuleCat.{max u v} A}
    (g : X ⟶ Y) [Epi g] (hX : Module.support A X ⊆ T) :
    Epi ((sectionsWithSupportInFunctor.{u, v} A T).map g) := by
  rw [ModuleCat.epi_iff_surjective]
  intro w
  obtain ⟨x, hx⟩ := (ModuleCat.epi_iff_surjective g).mp ‹Epi g› w.val
  refine ⟨⟨x, ?_⟩, Subtype.ext ?_⟩
  · rw [(sectionsWithSupportIn_eq_top_iff A T (X : Type (max u v))).mpr hX]
    exact Submodule.mem_top
  · exact (sectionsWithSupportInFunctor_map_val A T g _).trans hx

/-- The vanishing `H^{k+1}_T(N) = 0` for a module `N` supported in `T`, by induction on `k`. -/
private lemma isZero_localCohomologyWithSupportIn_succ_of_support_subset [IsNoetherianRing A]
    (hT : StableUnderSpecialization T) (k : ℕ) :
    ∀ N : ModuleCat.{max u v} A, Module.support A N ⊆ T →
      IsZero (localCohomologyWithSupportIn A T
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj N) ((k : ℤ) + 1)) := by
  induction k with
  | zero =>
    intro N hN
    obtain ⟨J, hJsupp, i, hi, hJinj⟩ := exists_injective_supported_envelope.{u, v} T hT ⟨N, hN⟩
    have hJinj' : CategoryTheory.Injective J := hJinj
    have hmono : Mono i := hi
    have hepi : Epi (cokernel.π i) := inferInstanceAs (Epi (ShortComplex.cokernelSequence i).g)
    have hS : (ShortComplex.mk i (cokernel.π i) (cokernel.condition i)).ShortExact :=
      ShortComplex.ShortExact.mk' (ShortComplex.cokernelSequence_exact i) hi hepi
    have hepiF : Epi ((sectionsWithSupportInFunctor.{u, v} A T).map (cokernel.π i)) :=
      epi_sectionsWithSupportInFunctor_map_of_support_subset.{u, v} A T (cokernel.π i) hJsupp
    have hcomp : Epi ((sectionsToLocalCohomologyZero.{u, v} A T).app J ≫
        (localCohomologyWithSupportInFunctor.{u, v} A T 0).map (cokernel.π i)) := by
      rw [← (sectionsToLocalCohomologyZero.{u, v} A T).naturality (cokernel.π i)]
      exact epi_comp' hepiF inferInstance
    have hepiG : Epi ((localCohomologyWithSupportInFunctor.{u, v} A T 0).map (cokernel.π i)) :=
      epi_of_epi ((sectionsToLocalCohomologyZero.{u, v} A T).app J) _
    rw [show ((0 : ℕ) : ℤ) + 1 = 1 from by norm_num]
    refine (localCohomology_exact₁.{u, v} T hS 0 1 (by ring)).isZero_X₂
      ((epi_localCohomologyMap_g_iff.{u, v} T hS 0 1 (by ring)).mp hepiG) ?_
    exact (isZero_localCohomologyWithSupportIn_of_injective.{u, v} T J 1 one_ne_zero).eq_of_tgt _ _
  | succ k ih =>
    intro N hN
    obtain ⟨J, hJsupp, i, hi, hJinj⟩ := exists_injective_supported_envelope.{u, v} T hT ⟨N, hN⟩
    have hJinj' : CategoryTheory.Injective J := hJinj
    have hmono : Mono i := hi
    have hepi : Epi (cokernel.π i) := inferInstanceAs (Epi (ShortComplex.cokernelSequence i).g)
    have hS : (ShortComplex.mk i (cokernel.π i) (cokernel.condition i)).ShortExact :=
      ShortComplex.ShortExact.mk' (ShortComplex.cokernelSequence_exact i) hi hepi
    have hC : Module.support A (cokernel i : ModuleCat.{max u v} A) ⊆ T :=
      (supportModuleProperty A T : ObjectProperty (ModuleCat.{max u v} A)).prop_of_epi
        (cokernel.π i) hJsupp
    rw [show ((k + 1 : ℕ) : ℤ) + 1 = (k : ℤ) + 1 + 1 from by push_cast; ring]
    refine isZero_localCohomology_X₁.{u, v} T hS ((k : ℤ) + 1) ((k : ℤ) + 1 + 1) rfl
      (ih (cokernel i) hC) ?_
    exact isZero_localCohomologyWithSupportIn_of_injective.{u, v} T J ((k : ℤ) + 1 + 1)
      (by omega)

/-- **A module supported in `T` is acyclic for sections with support in `T`:** `H^i_T(N) = 0` for
every `i > 0`, when `A` is Noetherian and `T` is stable under specialization.

Embed `N` in an injective module `J` supported in `T`. In degree one the connecting map out of
`H^0_T(J/N)` vanishes, because degree-zero local cohomology is sections with support and
`Γ_T(J) ⟶ Γ_T(J/N)` is surjective; in higher degrees the long exact sequence reduces the degree
for `N` to the previous degree for `J/N`, which is again supported in `T`. -/
theorem isZero_localCohomologyWithSupportIn_of_support_subset [IsNoetherianRing A]
    (hT : StableUnderSpecialization T) (N : ModuleCat.{max u v} A)
    (hN : Module.support A N ⊆ T) (i : ℤ) (hi : 0 < i) :
    IsZero (localCohomologyWithSupportIn A T
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj N) i) := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, i = (k : ℤ) + 1 := ⟨(i - 1).toNat, by omega⟩
  exact isZero_localCohomologyWithSupportIn_succ_of_support_subset.{u, v} A T hT k N hN

end Stacks.LocalCohomology

end
