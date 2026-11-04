module

public import StacksFrontier.RingTheory.LocalCohomology.BaseChangeGeneralSupport
public import StacksFrontier.RingTheory.LocalCohomology.SupportedModulesAcyclic

/-!
# Derived sections with support in `T` of an object with `T`-supported cohomology

Let `A` be a Noetherian ring and `T ⊆ Spec(A)` stable under specialization. For a bounded-below
object `K` all of whose cohomology modules are supported in `T`, the augmentation
$$ R\Gamma_T(K) \longrightarrow K $$
is an isomorphism; equivalently `H^i_T(K) = H^i(K)` for every `i`.

## Main results

* `Stacks.LocalCohomology.nonempty_localCohomologyWithSupportIn_iso_sectionsWithSupportIn` — for
  `K` concentrated in degrees `≥ b`, `H^b_T(K) ≅ Γ_T(H^b(K))`.
* `Stacks.LocalCohomology.isIso_map_derivedSectionsWithSupportInAugmentation_app` — the
  augmentation becomes invertible after applying `RΓ_T` to it, at every bounded-below object.
* `Stacks.LocalCohomology.isIso_derivedSectionsWithSupportInAugmentation_app_of_support_subset`
  — **the augmentation is an isomorphism** at a bounded-below object with `T`-supported
  cohomology.
* `Stacks.LocalCohomology.isIso_derivedSectionsWithSupportInPlusAugmentation_app_of_support_subset`
  — the same statement for the bounded-below derived functor.
* `Stacks.LocalCohomology.localCohomologyWithSupportInPlusIsoHomology` and
  `Stacks.LocalCohomology.finite_localCohomologyWithSupportInPlus_of_support_subset` — the
  degreewise consequence `H^i_T(K) ≅ H^i(K)`, and the finiteness it transports.

## Implementation notes

Everything is computed on a bounded-below complex `L` of injectives representing `K`. Such an `L`
is K-injective, so the canonical comparison `derivedSectionsWithSupportInUnit` is invertible at
it and `RΓ_T(K)` is the complex `Γ_T(L)`; the defining property of the augmentation then
identifies it with the degreewise inclusion `Γ_T(L) ⟶ L`.

Two facts about `Γ_T` drive the argument. It takes injective modules to injective modules
supported in `T` ([Stacks, Tag 08YA], `Stacks.LocalCohomology.injective_sectionsWithSupportIn`),
so `Γ_T(L)` is again a bounded-below complex of injectives and `RΓ_T(RΓ_T(K)) = RΓ_T(K)`
with the augmentation inducing the identity — this is
`isIso_map_derivedSectionsWithSupportInAugmentation_app`, which needs no hypothesis on the
cohomology of `K`. And it is left exact
(`Stacks.LocalCohomology.sectionsWithSupportInFunctor_preservesFiniteLimits`), so in the lowest
degree where `L` lives it commutes with cycles, which gives `H^b_T(K) = Γ_T(H^b(K))`.

The main theorem is then the vanishing of the cone `X` of the augmentation. The cone is
bounded below, its cohomology is supported in `T` because that of `K` and that of `RΓ_T(K)` is,
and `RΓ_T(X) = 0` because `RΓ_T` is exact and inverts the augmentation. An object with those
three properties is zero: in its lowest degree `b` one has `H^b(X) = Γ_T(H^b(X)) = H^b_T(X) = 0`,
which pushes the lowest degree up by one, and iterating reaches every degree.

No `@[stacks]` attribute is placed. Tag 0EF4 is carried in this library by two part-labels, and
neither is restated or strengthened here: `"local_cohomology_with_support_in_t"`, the
construction of `RΓ_T` in
`StacksFrontier/RingTheory/LocalCohomology/SectionsWithSupport.lean`, and
`"cohomology_calculation"`, the agreement of the bounded-below and the unbounded right derived
functor in `StacksFrontier/RingTheory/LocalCohomology/BoundedComparison.lean`. What is proved below
is a property of the construction, not the construction or that comparison.

## References

* [Stacks Project, Tag 0EF4](https://stacks.math.columbia.edu/tag/0EF4)
* [Stacks Project, Tag 0EEZ](https://stacks.math.columbia.edu/tag/0EEZ)
* [Stacks Project, Tag 08YA](https://stacks.math.columbia.edu/tag/08YA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.LocalCohomology

/-! ### The support of the middle term of an exact sequence -/

/-- The support of the middle term of an exact sequence `M ⟶ N ⟶ P` of modules is contained in
the union of the supports of the outer terms. -/
theorem support_subset_union_of_exact {A : Type u} [CommRing A] {M N P : Type*}
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] [AddCommGroup P] [Module A P]
    (f : M →ₗ[A] N) (g : N →ₗ[A] P) (hfg : Function.Exact f g) :
    Module.support A N ⊆ Module.support A M ∪ Module.support A P := by
  intro p
  contrapose
  simp only [Set.mem_union, not_or, and_imp, Module.notMem_support_iff']
  intro hM hP m
  obtain ⟨r, hr, h₁⟩ := hP (g m)
  rw [← map_smul, hfg] at h₁
  obtain ⟨m', hm'⟩ := h₁
  obtain ⟨s, hs, h₂⟩ := hM m'
  exact ⟨s * r, p.asIdeal.primeCompl.mul_mem hs hr, by
    rw [mul_smul, ← hm', ← map_smul, h₂, map_zero]⟩

variable (A : Type u) [CommRing A] (T : Set (PrimeSpectrum A))

/-! ### The inclusion of the `T`-supported sections -/

/-- The inclusion `Γ_T(M) ⟶ M` is invertible when the support of `M` lies in `T`. -/
theorem isIso_sectionsWithSupportInSubtype_app (M : ModuleCat.{max u v} A)
    (hM : Module.support A M ⊆ T) :
    IsIso ((sectionsWithSupportInSubtype.{u, v} A T).app M) := by
  have htop : sectionsWithSupportIn A T (M : Type (max u v)) = ⊤ :=
    (sectionsWithSupportIn_eq_top_iff A T (M : Type (max u v))).mpr hM
  have hmono : Mono ((sectionsWithSupportInSubtype.{u, v} A T).app M) :=
    (ModuleCat.mono_iff_injective _).mpr Subtype.val_injective
  have hepi : Epi ((sectionsWithSupportInSubtype.{u, v} A T).app M) :=
    (ModuleCat.epi_iff_surjective _).mpr fun m ↦
      ⟨⟨m, by rw [htop]; exact Submodule.mem_top⟩, rfl⟩
  exact isIso_of_mono_of_epi _

/-- A module supported in `T` with no nonzero `T`-supported sections is zero. -/
theorem isZero_of_isZero_sectionsWithSupportIn (M : ModuleCat.{max u v} A)
    (hM : Module.support A M ⊆ T)
    (h : IsZero ((sectionsWithSupportInFunctor.{u, v} A T).obj M)) : IsZero M :=
  have := isIso_sectionsWithSupportInSubtype_app.{u, v} A T M hM
  h.of_iso (asIso ((sectionsWithSupportInSubtype.{u, v} A T).app M)).symm

/-- Applying `Γ_T` to the inclusion `Γ_T(M) ⟶ M` gives the inclusion of the `T`-supported
sections of `Γ_T(M)`. -/
theorem map_sectionsWithSupportInSubtype_app (M : ModuleCat.{max u v} A) :
    (sectionsWithSupportInFunctor.{u, v} A T).map
        ((sectionsWithSupportInSubtype.{u, v} A T).app M) =
      (sectionsWithSupportInSubtype.{u, v} A T).app
        ((sectionsWithSupportInFunctor.{u, v} A T).obj M) :=
  rfl

/-- `Γ_T` is idempotent: applying it to the inclusion `Γ_T(M) ⟶ M` gives an isomorphism. -/
theorem isIso_map_sectionsWithSupportInSubtype_app (M : ModuleCat.{max u v} A) :
    IsIso ((sectionsWithSupportInFunctor.{u, v} A T).map
      ((sectionsWithSupportInSubtype.{u, v} A T).app M)) := by
  rw [map_sectionsWithSupportInSubtype_app.{u, v} A T M]
  exact isIso_sectionsWithSupportInSubtype_app.{u, v} A T _
    (support_sectionsWithSupportIn_subset T M)

/-! ### The inclusion of the complex of `T`-supported sections -/

/-- The degreewise inclusion of the complex of `T`-supported sections of a cochain complex. -/
def supportedSectionsComplexι (L : CochainComplex (ModuleCat.{max u v} A) ℤ) :
    (Functor.mapHomologicalComplex (sectionsWithSupportInFunctor.{u, v} A T)
        (ComplexShape.up ℤ)).obj L ⟶ L where
  f n := (sectionsWithSupportInSubtype.{u, v} A T).app (L.X n)
  comm' i j _ := ((sectionsWithSupportInSubtype.{u, v} A T).naturality (L.d i j)).symm

/-- On the homotopy category the inclusion of the complex of `T`-supported sections is the class
of the degreewise inclusion. -/
theorem homotopySectionsWithSupportInSubtype_app_quotient
    (L : CochainComplex (ModuleCat.{max u v} A) ℤ) :
    (homotopySectionsWithSupportInSubtype.{u, v} A T).app
        ((HomotopyCategory.quotient (ModuleCat.{max u v} A) (ComplexShape.up ℤ)).obj L) =
      (HomotopyCategory.quotient (ModuleCat.{max u v} A) (ComplexShape.up ℤ)).map
        (supportedSectionsComplexι.{u, v} A T L) :=
  rfl

/-- Applying `Γ_T` degreewise to the inclusion of the complex of `T`-supported sections gives an
isomorphism of complexes. -/
theorem isIso_mapHomologicalComplex_map_supportedSectionsComplexι
    (L : CochainComplex (ModuleCat.{max u v} A) ℤ) :
    IsIso ((Functor.mapHomologicalComplex (sectionsWithSupportInFunctor.{u, v} A T)
      (ComplexShape.up ℤ)).map (supportedSectionsComplexι.{u, v} A T L)) := by
  have : ∀ n : ℤ, IsIso (((Functor.mapHomologicalComplex
      (sectionsWithSupportInFunctor.{u, v} A T) (ComplexShape.up ℤ)).map
        (supportedSectionsComplexι.{u, v} A T L)).f n) := fun n ↦
    isIso_map_sectionsWithSupportInSubtype_app.{u, v} A T (L.X n)
  exact HomologicalComplex.Hom.isIso_of_components _

/-! ### The augmentation at a bounded-below complex of injectives -/

/-- Up to the canonical comparison, the augmentation at a cochain complex is the degreewise
inclusion of the complex of `T`-supported sections. -/
theorem derivedSectionsWithSupportInUnit_app_comp_augmentation_app
    (L : CochainComplex (ModuleCat.{max u v} A) ℤ) :
    (derivedSectionsWithSupportInUnit.{u, v} A T).app
          ((HomotopyCategory.quotient (ModuleCat.{max u v} A) (ComplexShape.up ℤ)).obj L) ≫
        (derivedSectionsWithSupportInAugmentation.{u, v} A T).app
          (DerivedCategory.Qh.obj ((HomotopyCategory.quotient (ModuleCat.{max u v} A)
            (ComplexShape.up ℤ)).obj L)) =
      DerivedCategory.Qh.map ((HomotopyCategory.quotient (ModuleCat.{max u v} A)
        (ComplexShape.up ℤ)).map (supportedSectionsComplexι.{u, v} A T L)) := by
  rw [← homotopySectionsWithSupportInSubtype_app_quotient.{u, v} A T L]
  exact derivedSectionsWithSupportInUnit_augmentation.{u, v} A T _

/-- The class in the derived category of the degreewise inclusion of `T`-supported sections is
invertible after applying `Γ_T` once more. -/
private theorem isIso_mapHomotopyCategory_comp_Qh_map
    (L : CochainComplex (ModuleCat.{max u v} A) ℤ) :
    IsIso ((((sectionsWithSupportInFunctor.{u, v} A T).mapHomotopyCategory
          (ComplexShape.up ℤ)) ⋙ DerivedCategory.Qh).map
      ((HomotopyCategory.quotient (ModuleCat.{max u v} A) (ComplexShape.up ℤ)).map
        (supportedSectionsComplexι.{u, v} A T L))) := by
  have h₀ := isIso_mapHomologicalComplex_map_supportedSectionsComplexι.{u, v} A T L
  have h₁ : IsIso ((HomotopyCategory.quotient (ModuleCat.{max u v} A) (ComplexShape.up ℤ)).map
      ((Functor.mapHomologicalComplex (sectionsWithSupportInFunctor.{u, v} A T)
        (ComplexShape.up ℤ)).map (supportedSectionsComplexι.{u, v} A T L))) :=
    Functor.map_isIso _ _
  have h₂ : IsIso (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient (ModuleCat.{max u v} A) (ComplexShape.up ℤ)).map
        ((Functor.mapHomologicalComplex (sectionsWithSupportInFunctor.{u, v} A T)
          (ComplexShape.up ℤ)).map (supportedSectionsComplexι.{u, v} A T L)))) :=
    Functor.map_isIso _ _
  exact h₂

/-- A bounded-below object of the derived category is represented by a bounded-below cochain
complex of injectives, which is K-injective. -/
private theorem exists_injective_isStrictlyGE_iso
    (K : DerivedCategory (ModuleCat.{max u v} A)) (b : ℤ) [K.IsGE b] :
    ∃ L : CochainComplex (ModuleCat.{max u v} A) ℤ,
      (∀ n : ℤ, Injective (L.X n)) ∧ L.IsStrictlyGE b ∧ L.IsKInjective ∧
        Nonempty (DerivedCategory.Qh.obj ((HomotopyCategory.quotient (ModuleCat.{max u v} A)
          (ComplexShape.up ℤ)).obj L) ≅ K) := by
  have : EnoughInjectives (ModuleCat.{max u v} A) := ModuleCat.enoughInjectives A
  obtain ⟨L₀, hL₀, ⟨e₀⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isGE K b
  obtain ⟨L, q, hq, hinj, hGE⟩ :=
    CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective L₀ b
  exact ⟨L, hinj, hGE, CochainComplex.isKInjective_of_injective L b,
    ⟨(DerivedCategory.quotientCompQhIso (ModuleCat.{max u v} A)).app L ≪≫
    (asIso (DerivedCategory.Q.map q)).symm ≪≫ e₀.symm⟩⟩

/-- The complex of `T`-supported sections of a bounded-below complex of injectives is again a
bounded-below complex of injectives, hence K-injective. -/
private theorem isKInjective_mapHomologicalComplex [IsNoetherianRing A]
    (hT : StableUnderSpecialization T) (L : CochainComplex (ModuleCat.{max u v} A) ℤ) (b : ℤ)
    [L.IsStrictlyGE b] (hinj : ∀ n : ℤ, Injective (L.X n)) :
    CochainComplex.IsKInjective ((Functor.mapHomologicalComplex
      (sectionsWithSupportInFunctor.{u, v} A T) (ComplexShape.up ℤ)).obj L) := by
  have hGE : CochainComplex.IsStrictlyGE ((Functor.mapHomologicalComplex
      (sectionsWithSupportInFunctor.{u, v} A T) (ComplexShape.up ℤ)).obj L) b := inferInstance
  have : ∀ n : ℤ, Injective (((Functor.mapHomologicalComplex
      (sectionsWithSupportInFunctor.{u, v} A T) (ComplexShape.up ℤ)).obj L).X n) := fun n ↦ by
    have := hinj n
    exact (Module.injective_iff_injective_object A
      (sectionsWithSupportIn A T (L.X n))).mp (injective_sectionsWithSupportIn T hT (L.X n))
  exact CochainComplex.isKInjective_of_injective _ b

/-- **`RΓ_T` inverts its own augmentation** at a bounded-below object: `Γ_T` is idempotent, so
applying `RΓ_T` to the augmentation `RΓ_T(K) ⟶ K` gives an isomorphism. No hypothesis on the
cohomology of `K` is needed. -/
theorem isIso_map_derivedSectionsWithSupportInAugmentation_app [IsNoetherianRing A]
    (hT : StableUnderSpecialization T) (K : DerivedCategory (ModuleCat.{max u v} A)) (b : ℤ)
    [K.IsGE b] :
    IsIso ((derivedSectionsWithSupportIn.{u, v} A T).map
      ((derivedSectionsWithSupportInAugmentation.{u, v} A T).app K)) := by
  obtain ⟨L, hinj, hGE, hK, ⟨e⟩⟩ := exists_injective_isStrictlyGE_iso.{u, v} A K b
  have : CochainComplex.IsKInjective ((Functor.mapHomologicalComplex
      (sectionsWithSupportInFunctor.{u, v} A T) (ComplexShape.up ℤ)).obj L) :=
    isKInjective_mapHomologicalComplex.{u, v} A T hT L b hinj
  have h₁ := isIso_mapHomotopyCategory_comp_Qh_map.{u, v} A T L
  have h₂ : IsIso ((derivedSectionsWithSupportIn.{u, v} A T).map
      (DerivedCategory.Qh.map ((HomotopyCategory.quotient (ModuleCat.{max u v} A)
        (ComplexShape.up ℤ)).map (supportedSectionsComplexι.{u, v} A T L)))) :=
    IsIso.of_isIso_fac_left ((derivedSectionsWithSupportInUnit.{u, v} A T).naturality
      ((HomotopyCategory.quotient (ModuleCat.{max u v} A) (ComplexShape.up ℤ)).map
        (supportedSectionsComplexι.{u, v} A T L))).symm
  have h₃ : IsIso ((derivedSectionsWithSupportIn.{u, v} A T).map
      ((derivedSectionsWithSupportInAugmentation.{u, v} A T).app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient (ModuleCat.{max u v} A)
          (ComplexShape.up ℤ)).obj L)))) := by
    have h₅ : IsIso ((derivedSectionsWithSupportIn.{u, v} A T).map
          ((derivedSectionsWithSupportInUnit.{u, v} A T).app
            ((HomotopyCategory.quotient (ModuleCat.{max u v} A) (ComplexShape.up ℤ)).obj L)) ≫
        (derivedSectionsWithSupportIn.{u, v} A T).map
          ((derivedSectionsWithSupportInAugmentation.{u, v} A T).app
            (DerivedCategory.Qh.obj ((HomotopyCategory.quotient (ModuleCat.{max u v} A)
              (ComplexShape.up ℤ)).obj L)))) := by
      rw [← Functor.map_comp,
        derivedSectionsWithSupportInUnit_app_comp_augmentation_app.{u, v} A T L]
      exact h₂
    exact IsIso.of_isIso_comp_left ((derivedSectionsWithSupportIn.{u, v} A T).map
      ((derivedSectionsWithSupportInUnit.{u, v} A T).app
        ((HomotopyCategory.quotient (ModuleCat.{max u v} A) (ComplexShape.up ℤ)).obj L))) _
  have h₆ : IsIso ((Functor.whiskerRight (derivedSectionsWithSupportInAugmentation.{u, v} A T)
      (derivedSectionsWithSupportIn.{u, v} A T)).app
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient (ModuleCat.{max u v} A)
        (ComplexShape.up ℤ)).obj L))) := h₃
  exact (NatTrans.isIso_app_iff_of_iso
    (Functor.whiskerRight (derivedSectionsWithSupportInAugmentation.{u, v} A T)
      (derivedSectionsWithSupportIn.{u, v} A T)) e).1 h₆

/-! ### Local cohomology in the lowest degree -/

/-- Sections with support in `T` commute with the cycles of a cochain complex in any degree:
both are the kernel of the differential out of that degree, and `Γ_T` preserves that kernel.
This is `Stacks.LocalCohomology.sectionsWithSupportInObjCyclesIso` in an arbitrary degree. -/
def sectionsWithSupportInCyclesIso (b : ℤ) (L : CochainComplex (ModuleCat.{max u v} A) ℤ) :
    (sectionsWithSupportInFunctor.{u, v} A T).obj (HomologicalComplex.cycles L b) ≅
      HomologicalComplex.cycles ((Functor.mapHomologicalComplex
        (sectionsWithSupportInFunctor.{u, v} A T) (ComplexShape.up ℤ)).obj L) b :=
  IsLimit.conePointUniqueUpToIso
    (KernelFork.mapIsLimit _ (L.cyclesIsKernel b (b + 1) (by simp))
      (sectionsWithSupportInFunctor.{u, v} A T))
    (((Functor.mapHomologicalComplex (sectionsWithSupportInFunctor.{u, v} A T)
      (ComplexShape.up ℤ)).obj L).cyclesIsKernel b (b + 1) (by simp))

/-- **The lowest local cohomology with support in `T`.** For an object concentrated in degrees
`≥ b`, the degree-`b` local cohomology with support in `T` is the module of `T`-supported
sections of the degree-`b` cohomology. -/
theorem nonempty_localCohomologyWithSupportIn_iso_sectionsWithSupportIn
    (K : DerivedCategory (ModuleCat.{max u v} A)) (b : ℤ) [K.IsGE b] :
    Nonempty (localCohomologyWithSupportIn A T K b ≅
      (sectionsWithSupportInFunctor.{u, v} A T).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) b).obj K)) := by
  obtain ⟨L, hinj, hGE, hK, ⟨e⟩⟩ := exists_injective_isStrictlyGE_iso.{u, v} A K b
  obtain ⟨iso⟩ := nonempty_localCohomology_iso_homology_of_isKInjective.{u, v} T K b L e
  have hLzero : IsZero (L.X (b - 1)) := L.isZero_of_isStrictlyGE b (b - 1) (by omega)
  have hLd : L.d (b - 1) b = 0 := hLzero.eq_of_src _ _
  have hCd : ((Functor.mapHomologicalComplex (sectionsWithSupportInFunctor.{u, v} A T)
      (ComplexShape.up ℤ)).obj L).d (b - 1) b = 0 :=
    ((sectionsWithSupportInFunctor.{u, v} A T).map_isZero hLzero).eq_of_src _ _
  exact ⟨iso ≪≫ (((Functor.mapHomologicalComplex (sectionsWithSupportInFunctor.{u, v} A T)
      (ComplexShape.up ℤ)).obj L).isoHomologyπ (b - 1) b (by simp) hCd).symm ≪≫
    (sectionsWithSupportInCyclesIso.{u, v} A T b L).symm ≪≫
    (sectionsWithSupportInFunctor.{u, v} A T).mapIso
      (L.isoHomologyπ (b - 1) b (by simp) hLd ≪≫
        ((DerivedCategory.homologyFunctorFactors (ModuleCat.{max u v} A) b).app L).symm ≪≫
        (DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) b).mapIso
          (((DerivedCategory.quotientCompQhIso (ModuleCat.{max u v} A)).app L).symm ≪≫ e))⟩

/-- **Local cohomology with support in `T` vanishes below any degree bounding the object
below.** -/
theorem isZero_localCohomologyWithSupportIn_of_isGE
    (K : DerivedCategory (ModuleCat.{max u v} A)) (b : ℤ) [K.IsGE b] (i : ℤ) (hi : i < b) :
    IsZero (localCohomologyWithSupportIn A T K i) := by
  obtain ⟨L, hinj, hGE, hK, ⟨e⟩⟩ := exists_injective_isStrictlyGE_iso.{u, v} A K b
  obtain ⟨iso⟩ := nonempty_localCohomology_iso_homology_of_isKInjective.{u, v} T K i L e
  refine IsZero.of_iso ?_ iso
  exact (HomologicalComplex.ExactAt.of_isZero
    ((sectionsWithSupportInFunctor.{u, v} A T).map_isZero
      (L.isZero_of_isStrictlyGE b i hi))).isZero_homology

/-- **`RΓ_T` preserves a bound below.** -/
theorem isGE_derivedSectionsWithSupportIn_obj
    (K : DerivedCategory (ModuleCat.{max u v} A)) (b : ℤ) [K.IsGE b] :
    ((derivedSectionsWithSupportIn.{u, v} A T).obj K).IsGE b := by
  rw [DerivedCategory.isGE_iff]
  exact isZero_localCohomologyWithSupportIn_of_isGE.{u, v} A T K b

/-! ### Three facts about a distinguished triangle of the derived category -/

/-- The cohomology of the third vertex of a distinguished triangle is supported in `T` as soon as
the cohomology of the other two vertices is. -/
private theorem support_homology_obj₃_subset
    (Tr : Triangle (DerivedCategory (ModuleCat.{max u v} A))) (hTr : Tr ∈ distTriang _)
    (h₁ : ∀ i : ℤ, Module.support A
      ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).obj Tr.obj₁) ⊆ T)
    (h₂ : ∀ i : ℤ, Module.support A
      ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).obj Tr.obj₂) ⊆ T) (i : ℤ) :
    Module.support A
      ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).obj Tr.obj₃) ⊆ T := by
  have hex := DerivedCategory.HomologySequence.exact₃ Tr hTr i (i + 1) rfl
  refine (support_subset_union_of_exact _ _
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp hex)).trans
    (Set.union_subset (h₂ i) (h₁ (i + 1)))

/-- If the first map of a distinguished triangle is invertible, the cohomology of the third
vertex vanishes. -/
private theorem isZero_homology_obj₃_of_isIso_mor₁
    (Tr : Triangle (DerivedCategory (ModuleCat.{max u v} A))) (hTr : Tr ∈ distTriang _)
    [IsIso Tr.mor₁] (i : ℤ) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).obj Tr.obj₃) :=
  (DerivedCategory.HomologySequence.exact₃ Tr hTr i (i + 1) rfl).isZero_X₂
    ((DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff Tr hTr i).mp inferInstance)
    ((DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff Tr hTr i (i + 1) rfl).mp
      inferInstance)

/-- If the cohomology of the third vertex of a distinguished triangle vanishes, the first map is
invertible. -/
private theorem isIso_mor₁_of_isZero_homology_obj₃
    (Tr : Triangle (DerivedCategory (ModuleCat.{max u v} A))) (hTr : Tr ∈ distTriang _)
    (h : ∀ i : ℤ, IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).obj Tr.obj₃)) :
    IsIso Tr.mor₁ := by
  rw [DerivedCategory.isIso_iff]
  intro n
  have hmono := (DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff Tr hTr (n - 1) n
    (by omega)).mpr ((h (n - 1)).eq_of_src _ _)
  have hepi := (DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff Tr hTr n).mpr
    ((h n).eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

/-! ### Objects with `T`-supported cohomology -/

/-- An object of the derived category whose cohomology is supported in `T` and whose local
cohomology with support in `T` vanishes is bounded below by every degree: in the lowest degree
`b` where it lives, `H^b = Γ_T(H^b) = H^b_T = 0`. -/
theorem isGE_add_of_isZero_localCohomologyWithSupportIn
    (K : DerivedCategory (ModuleCat.{max u v} A))
    (hsupp : ∀ i : ℤ, Module.support A
      ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).obj K) ⊆ T)
    (hvan : ∀ i : ℤ, IsZero (localCohomologyWithSupportIn A T K i)) :
    ∀ (n : ℕ) (b : ℤ), K.IsGE b → K.IsGE (b + (n : ℤ)) := by
  intro n
  induction n with
  | zero => intro b hb; simpa using hb
  | succ n ih =>
    intro b hb
    have h₁ : K.IsGE (b + (n : ℤ)) := ih b hb
    obtain ⟨iso⟩ := nonempty_localCohomologyWithSupportIn_iso_sectionsWithSupportIn.{u, v}
      A T K (b + (n : ℤ))
    have hzero : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A)
        (b + (n : ℤ))).obj K) :=
      isZero_of_isZero_sectionsWithSupportIn.{u, v} A T _ (hsupp (b + (n : ℤ)))
        ((hvan (b + (n : ℤ))).of_iso iso.symm)
    rw [show b + ((n + 1 : ℕ) : ℤ) = b + (n : ℤ) + 1 from by push_cast; ring,
      DerivedCategory.isGE_iff]
    intro i hi
    rcases lt_or_eq_of_le (show i ≤ b + (n : ℤ) by omega) with h | h
    · exact DerivedCategory.isZero_of_isGE K (b + (n : ℤ)) i h
    · rw [h]; exact hzero

/-- **The augmentation `RΓ_T(K) ⟶ K` is an isomorphism** when `K` is bounded below and every
cohomology module of `K` is supported in `T`. Equivalently, `H^i_T(K) = H^i(K)` for all `i`:
derived sections with support in `T` act as the identity on objects supported in `T`. -/
theorem isIso_derivedSectionsWithSupportInAugmentation_app_of_support_subset
    [IsNoetherianRing A] (hT : StableUnderSpecialization T)
    (K : DerivedCategory (ModuleCat.{max u v} A)) (b : ℤ) [K.IsGE b]
    (hsupp : ∀ i : ℤ, Module.support A
      ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).obj K) ⊆ T) :
    IsIso ((derivedSectionsWithSupportInAugmentation.{u, v} A T).app K) := by
  obtain ⟨X, g, h, hTr⟩ := Pretriangulated.distinguished_cocone_triangle
    ((derivedSectionsWithSupportInAugmentation.{u, v} A T).app K)
  have hRGGE : ((derivedSectionsWithSupportIn.{u, v} A T).obj K).IsGE b :=
    isGE_derivedSectionsWithSupportIn_obj.{u, v} A T K b
  have hRGsupp : ∀ i : ℤ, Module.support A
      ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).obj
        ((derivedSectionsWithSupportIn.{u, v} A T).obj K)) ⊆ T := fun i ↦
    support_localCohomologyWithSupportIn_subset T K i
  have hXsupp := support_homology_obj₃_subset.{u, v} A T _ hTr hRGsupp hsupp
  have hXGE : X.IsGE (b - 1) :=
    DerivedCategory.TStructure.t.isGE₂ _ (Pretriangulated.rot_of_distTriang _ hTr) (b - 1)
      (DerivedCategory.TStructure.t.isGE_of_ge K (b - 1) b (by omega))
      (DerivedCategory.TStructure.t.isGE_shift
        ((derivedSectionsWithSupportIn.{u, v} A T).obj K) b 1 (b - 1) (by omega))
  have hRGiso : IsIso ((derivedSectionsWithSupportIn.{u, v} A T).mapTriangle.obj
      (Triangle.mk ((derivedSectionsWithSupportInAugmentation.{u, v} A T).app K) g h)).mor₁ :=
    isIso_map_derivedSectionsWithSupportInAugmentation_app.{u, v} A T hT K b
  have hXvan : ∀ i : ℤ, IsZero (localCohomologyWithSupportIn A T X i) := fun i ↦
    isZero_homology_obj₃_of_isIso_mor₁.{u, v} A
      ((derivedSectionsWithSupportIn.{u, v} A T).mapTriangle.obj
        (Triangle.mk ((derivedSectionsWithSupportInAugmentation.{u, v} A T).app K) g h))
      ((derivedSectionsWithSupportIn.{u, v} A T).map_distinguished _ hTr) i
  refine isIso_mor₁_of_isZero_homology_obj₃.{u, v} A _ hTr fun i ↦ ?_
  have hge := isGE_add_of_isZero_localCohomologyWithSupportIn.{u, v} A T X hXsupp hXvan
    (i - (b - 1) + 1).toNat (b - 1) hXGE
  exact DerivedCategory.isZero_of_isGE X (b - 1 + ((i - (b - 1) + 1).toNat : ℤ)) i (by omega)

/-! ### The bounded-below derived functor -/

/-- **The augmentation `RΓ_T(K) ⟶ K` is an isomorphism on `D⁺`** when every cohomology module of
`K` is supported in `T`. This is the bounded-below form of
`isIso_derivedSectionsWithSupportInAugmentation_app_of_support_subset`, transported along the
comparison of the two right derived functors. -/
theorem isIso_derivedSectionsWithSupportInPlusAugmentation_app_of_support_subset
    [IsNoetherianRing A] (hT : StableUnderSpecialization T)
    (K : DerivedCategory.Plus (ModuleCat.{max u v} A))
    (hsupp : ∀ i : ℤ, Module.support A
      ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{max u v} A) i).obj K) ⊆ T) :
    IsIso ((derivedSectionsWithSupportInPlusAugmentation.{u, v} A T).app K) := by
  obtain ⟨b, hbObj⟩ := K.property
  have hb : (DerivedCategory.Plus.ι.obj K).IsGE b := hbObj
  have hsupp' : ∀ i : ℤ, Module.support A
      ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).obj
        (DerivedCategory.Plus.ι.obj K)) ⊆ T := hsupp
  have hiso : IsIso ((derivedSectionsWithSupportInAugmentation.{u, v} A T).app
      (DerivedCategory.Plus.ι.obj K)) :=
    isIso_derivedSectionsWithSupportInAugmentation_app_of_support_subset.{u, v} A T hT
      (DerivedCategory.Plus.ι.obj K) b hsupp'
  have heq := NatTrans.congr_app
    (derivedSectionsWithSupportInPlusIso_augmentation.{u, v} A T) K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at heq
  have hι : IsIso (DerivedCategory.Plus.ι.map
      ((derivedSectionsWithSupportInPlusAugmentation.{u, v} A T).app K)) := by
    rw [← heq]
    infer_instance
  exact isIso_of_fully_faithful DerivedCategory.Plus.ι _

/-- **`H^i_T(K) = H^i(K)`** for a bounded-below object whose cohomology is supported in `T`: the
augmentation induces the comparison. -/
def localCohomologyWithSupportInPlusIsoHomology [IsNoetherianRing A]
    (hT : StableUnderSpecialization T) (K : DerivedCategory.Plus (ModuleCat.{max u v} A))
    (hsupp : ∀ i : ℤ, Module.support A
      ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{max u v} A) i).obj K) ⊆ T) (i : ℤ) :
    localCohomologyWithSupportInPlus.{u, v} A T K i ≅
      (DerivedCategory.Plus.homologyFunctor (ModuleCat.{max u v} A) i).obj K :=
  have := isIso_derivedSectionsWithSupportInPlusAugmentation_app_of_support_subset.{u, v}
    A T hT K hsupp
  (DerivedCategory.Plus.homologyFunctor (ModuleCat.{max u v} A) i).mapIso
    (asIso ((derivedSectionsWithSupportInPlusAugmentation.{u, v} A T).app K))

/-- Finiteness of the cohomology of a bounded-below object supported in `T` passes to its local
cohomology with support in `T`. -/
theorem finite_localCohomologyWithSupportInPlus_of_support_subset [IsNoetherianRing A]
    (hT : StableUnderSpecialization T) (K : DerivedCategory.Plus (ModuleCat.{max u v} A))
    (hsupp : ∀ i : ℤ, Module.support A
      ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{max u v} A) i).obj K) ⊆ T) (i : ℤ)
    [Module.Finite A ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{max u v} A) i).obj K)] :
    Module.Finite A (localCohomologyWithSupportInPlus.{u, v} A T K i) :=
  Module.Finite.equiv
    (localCohomologyWithSupportInPlusIsoHomology.{u, v} A T hT K hsupp i).toLinearEquiv.symm

end Stacks.LocalCohomology

end
