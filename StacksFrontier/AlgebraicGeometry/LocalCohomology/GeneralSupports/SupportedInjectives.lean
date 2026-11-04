module

public import StacksFrontier.Algebra.Module.Matlis
public import Mathlib.Algebra.Category.ModuleCat.Subobject
public import Mathlib.CategoryTheory.Limits.Preserves.Opposites
public import StacksFrontier.Algebra.Module.Essential
public import StacksFrontier.Algebra.Module.InjectiveHull.Basic
public import StacksFrontier.RingTheory.LocalCohomology.ModulesSupportedIn
public import StacksFrontier.RingTheory.LocalCohomology.SectionsWithSupport

/-!
# Injective hulls of modules supported in a subset of the spectrum

Over a Noetherian ring, a module supported in a specialization-closed subset `T` of the spectrum
embeds into an injective module that is again supported in `T`: the sections with support in `T`
of an ambient injective hull. This is what lets the category of supported modules be compared
with the ambient category of all modules.

## Main results

* `Module.sectionsWithSupportIn_injective_ambient`: the sections with support in `T` of an
  injective module are injective.
* `Module.sectionsWithSupportIn_supported`: those sections are supported in `T`.
* `Module.supportedModule_has_ambientInjective_envelope`: a module supported in `T` admits a
  monomorphism into a module supported in `T` which is injective in the ambient category.

## Implementation notes

An injective module over a Noetherian ring decomposes as a direct sum of injective hulls of
residue fields; the hull of the residue field of `p` has support `{p}` or is killed by taking
sections with support in `T`, depending on whether `p ∈ T`. Stability of `T` under specialization
is what makes that dichotomy exhaustive, and it is the only place that hypothesis is used. The
summand of a direct sum obtained this way is cut out by an idempotent, which is why injectivity
is transported along `Module.injective_range_of_idempotent`.

The module universe is enlarged to `max u v` so that the decomposition results apply while the
interface stays universe-polymorphic.

## References

* [Stacks Project, Tag 0EF2](https://stacks.math.columbia.edu/tag/0EF2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped DirectSum
open Stacks.LocalCohomology

universe u v w

namespace Module

private lemma essentialMono_of_subobject_le
    {C : Type*} [Category C] [HasZeroObject C] [HasPullbacks C]
    {K P E : C} (i : K ⟶ E) (j : P ⟶ E) [Mono i] [Mono j]
    (hi : IsEssentialMono i)
    (hij : Subobject.mk i ≤ Subobject.mk j) :
    IsEssentialMono j :=
  fun q hq hj => hi q hq (le_bot_iff.mp ((inf_le_inf_left q hij).trans hj.le))

private lemma residueFieldHull_primaryComponent_eq_top
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (p : Ideal R) [hp : p.IsPrime] (K E : ModuleCat.{v} R)
    (e : K ≃ₗ[R] p.ResidueField) (i : K ⟶ E) [Mono i]
    (hE : IsInjectiveHull i) :
    Ideal.primaryComponent E p = ⊤ :=
  primaryComponent_eq_top_of_isInjectiveHull_residueField p K E e i hE

-- The support criterion expands annihilators and primary components.
private lemma residueFieldHull_support_subset
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (p : Ideal R) [p.IsPrime] (K E : ModuleCat.{v} R)
    (e : K ≃ₗ[R] p.ResidueField) (i : K ⟶ E) [Mono i]
    (hE : IsInjectiveHull i) (T : Set (PrimeSpectrum R))
    (hT : StableUnderSpecialization T) (hpT : (⟨p, ‹p.IsPrime›⟩ : PrimeSpectrum R) ∈ T) :
    Module.support R E ⊆ T :=
  support_subset_of_isInjectiveHull_residueField p K E e i hE T hT hpT

private lemma residueFieldHull_sections_eq_top
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (p : Ideal R) [p.IsPrime] (K E : ModuleCat.{v} R)
    (e : K ≃ₗ[R] p.ResidueField) (i : K ⟶ E) [Mono i]
    (hE : IsInjectiveHull i) (T : Set (PrimeSpectrum R))
    (hT : StableUnderSpecialization T) (hpT : (⟨p, ‹p.IsPrime›⟩ : PrimeSpectrum R) ∈ T) :
    sectionsWithSupportIn R T E = ⊤ :=
  sectionsWithSupportIn_eq_top_of_isInjectiveHull_residueField p K E e i hE T hT hpT

-- Comparing annihilators in a residue field requires additional elaboration time.
private lemma residueFieldHull_sections_eq_bot
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (p : Ideal R) [p.IsPrime] (K E : ModuleCat.{v} R)
    (e : K ≃ₗ[R] p.ResidueField) (i : K ⟶ E) [Mono i]
    (hE : IsInjectiveHull i) (T : Set (PrimeSpectrum R))
    (hpT : (⟨p, ‹p.IsPrime›⟩ : PrimeSpectrum R) ∉ T) :
    sectionsWithSupportIn R T E = ⊥ :=
  sectionsWithSupportIn_eq_bot_of_isInjectiveHull_residueField p K E e i hE T hpT

private lemma supportedModule_map_mem_sectionsWithSupportIn
    {R : Type u} [CommRing R] (T : Set (PrimeSpectrum R))
    (M E : ModuleCat.{v} R) (i : M ⟶ E)
    (hM : Module.support R M ⊆ T) (x : M) :
    i.hom x ∈ sectionsWithSupportIn R T E :=
  mem_sectionsWithSupportIn_of_support_subset T M E i hM x

private lemma sectionsWithSupportIn_supported
    {R : Type u} [CommRing R] (T : Set (PrimeSpectrum R)) (E : ModuleCat.{v} R) :
    Module.support R (sectionsWithSupportIn R T E) ⊆ T :=
  support_sectionsWithSupportIn_subset T E

/-- The inclusion of the full subcategory of `A`-modules supported in `T` preserves finite
limits. -/
local instance (A : Type u) [CommRing A] (T : Set (PrimeSpectrum A)) :
    PreservesFiniteLimits (supportModuleProperty A T :
      ObjectProperty (ModuleCat.{v} A)).ι :=
  ObjectProperty.preservesFiniteLimits_ι_of_isWeakSerreClass _

/-- The inclusion of the full subcategory of `A`-modules supported in `T` preserves finite
colimits. -/
local instance (A : Type u) [CommRing A] (T : Set (PrimeSpectrum A)) :
    PreservesFiniteColimits (supportModuleProperty A T :
      ObjectProperty (ModuleCat.{v} A)).ι :=
  ObjectProperty.preservesFiniteColimits_ι_of_isWeakSerreClass _

private lemma injective_range_of_idempotent
    {R : Type u} [Ring R] {M : Type v} [AddCommGroup M] [Module R M]
    [Module.Injective R M] (p : M →ₗ[R] M) (hp : p.comp p = p) :
    Module.Injective R p.range := by
  let j : p.range →ₗ[R] M := p.range.subtype
  let r : M →ₗ[R] p.range := p.codRestrict p.range fun x => ⟨x, rfl⟩
  have hrj : r.comp j = LinearMap.id := by
    ext ⟨_, x, rfl⟩
    exact LinearMap.congr_fun hp x
  refine ⟨fun X Y _ _ _ _ f hf g => ?_⟩
  obtain ⟨g', hg'⟩ := Module.Injective.out (R := R) (Q := M) f hf (j.comp g)
  refine ⟨r.comp g', fun x => ?_⟩
  rw [LinearMap.comp_apply, hg' x]
  exact LinearMap.congr_fun hrj (g x)

private structure ResidueHullWitness {R : Type u} [CommRing R]
    (E : ModuleCat.{max u v} R) where
  p : Ideal R
  hp : p.IsPrime
  K : ModuleCat.{max u v} R
  e : K ≃ₗ[R] p.ResidueField
  i : K ⟶ E
  hi : Mono i
  hull : letI : Mono i := hi; IsInjectiveHull i

private lemma exists_residueHullWitness
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (E : ModuleCat.{max u v} R) [CategoryTheory.Injective E] (hE : Indecomposable E) :
    Nonempty (ResidueHullWitness E) :=
  let ⟨p, hp, K, e, i, hi, hh⟩ := exists_residueField_injectiveHull R E hE
  ⟨⟨p, hp, K, e, i, hi, hh⟩⟩

private lemma sectionsWithSupportIn_directSum_iff
    {R : Type u} [CommRing R] {ι : Type v} (T : Set (PrimeSpectrum R))
    (M : ι → Type (max u v)) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    (x : ⨁ i, M i) :
    x ∈ sectionsWithSupportIn R T (⨁ i, M i) ↔
      ∀ i, x i ∈ sectionsWithSupportIn R T (M i) :=
  mem_sectionsWithSupportIn_directSum_iff T M x

private lemma sectionsWithSupportIn_injective_ambient
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (T : Set (PrimeSpectrum R)) (hT : StableUnderSpecialization T)
    (E : ModuleCat.{max u v} R) [CategoryTheory.Injective E] :
    Module.Injective R (sectionsWithSupportIn R T E) :=
  injective_sectionsWithSupportIn.{u, v} T hT E

/-- A module supported in `T` embeds into a module supported in `T` which is injective as an
object of the ambient category of all modules. -/
lemma supportedModule_has_ambientInjective_envelope
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (T : Set (PrimeSpectrum R)) (hT : StableUnderSpecialization T)
    (X : ModulesSupportedIn.{u, max u v} R T) :
    ∃ (J : ModuleCat.{max u v} R),
      supportModuleProperty.{u, max u v} R T J ∧
      ∃ (i : X.1 ⟶ J), Mono i ∧ CategoryTheory.Injective (ModuleCat.of R (↑J)) :=
  exists_injective_supported_envelope.{u, v} T hT X

end Module
