module

public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackStalkColimit
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.RelativeAssassinValuationRing
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.Defs
import StacksFrontier.AlgebraicGeometry.Fibres.AssociatedPrimesCover
import StacksCore.Tactic.EgaSgaAttribute
import StacksFrontier.AlgebraicGeometry.Fibres.AssociatedPrimesCover

/-!
# Associated primes of a reduction, and of a module read along a surjection

This file collects the commutative algebra needed to turn the geometric statement "`p` is an
associated point of the restriction of a module to a scheme-theoretic fibre" into a statement
about the stalk of that module at the image of `p` and the ideal cutting out the fibre.

Two notions of associated prime are in play and both are needed. The Stacks Project (Tag 00LA),
and hence `IsAssociatedPrimeStacks`, asks for an element whose annihilator *equals* the prime;
Mathlib's `associatedPrimes` asks for an element whose annihilator has the prime as its
*radical*. The strict condition implies Mathlib's — a prime is its own radical — and the two
agree over a Noetherian ring (`Submodule.isAssociatedPrime_iff`).

The geometric situation is that of `AlgebraicGeometry.Scheme.Hom.ker_stalkMap_fiberι`: the stalk
map `𝒪_{X,x} ⟶ 𝒪_{X_y,p}` of a fibre inclusion is *surjective* with kernel `𝔪_y·𝒪_{X,x}`, and
the stalk of the restricted module is correspondingly the reduction `F_x/𝔪_y·F_x`. Everything
below is therefore stated for a surjective ring homomorphism and an additive equivalence
semilinear over it, rather than for a ring isomorphism; that is what lets it be applied without
committing to either of the two definitionally equal spellings of the stalk ring
(`X.presheaf.stalk x`, and the `sheafToPresheaf`-expanded form that
`Stacks.ModuleSkyscraper.stalkObj` produces), which have different instance keys.

## Main definitions

* `Stacks.FibreStalkModule.quotSMulTopModule`: the `R ⧸ I`-module structure on the reduction
  `M ⧸ I·M`, together with `Stacks.FibreStalkModule.isScalarTower_quotSMulTop`.

## Main results

* `Stacks.FibreStalkModule.isAssociatedPrimeStacks_maximalIdeal_congr`: the strict condition
  that the maximal ideal is an associated prime transfers across a surjection of local rings
  and a semilinear additive equivalence of modules, in both directions.
* `Stacks.FibreStalkModule.mem_associatedPrimes_of_isAssociatedPrimeStacks` and
  `Stacks.FibreStalkModule.isAssociatedPrimeStacks_of_mem_associatedPrimes`: the strict notion
  implies Mathlib's, and the two agree over a Noetherian ring.
* `Stacks.FibreStalkModule.map_mem_associatedPrimes_quotient` and
  `Stacks.FibreStalkModule.comap_mem_associatedPrimes_quotient`: Mathlib's associated primes of
  a module killed by `I` correspond under contraction along `R ⟶ R ⧸ I` (Tag 05BY, for the
  radical convention).
* `Stacks.FibreStalkModule.isAssociatedPrimeStacks_maximalIdeal_of_mem_associatedPrimes_quotient`:
  the combination used downstream — Mathlib's radical condition over `R` upgrades to the strict
  condition over `R` as soon as the *reduction* `R ⧸ I` is Noetherian, which is the only
  Noetherian hypothesis available when `R` is merely essentially of finite type over a
  valuation ring.

## References

* [Stacks Project, Tag 00LA](https://stacks.math.columbia.edu/tag/00LA)
* [Stacks Project, Tag 05BY](https://stacks.math.columbia.edu/tag/05BY)
* [Stacks Project, Tag 02OJ](https://stacks.math.columbia.edu/tag/02OJ)
-/

@[expose] public section

open CategoryTheory IsLocalRing TopologicalSpace

namespace Stacks.FibreStalkModule

/-! ### Maximal ideals under a surjection -/

section Surjective

variable {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
  (π : R →+* S) [IsLocalHom π]

/-- The maximal ideal of a local ring is the contraction of the maximal ideal of a local
quotient along a local homomorphism. -/
@[ega "0 1.0.7" "local implies φ⁻¹(n)=m"]
theorem comap_maximalIdeal : (maximalIdeal S).comap π = maximalIdeal R := by
  ext r
  rw [Ideal.mem_comap]
  simp only [mem_maximalIdeal, mem_nonunits_iff]
  exact not_congr ⟨fun h ↦ isUnit_of_map_unit π r h, fun h ↦ h.map π⟩

/-- A surjective local homomorphism of local rings carries the maximal ideal onto the maximal
ideal. -/
theorem map_maximalIdeal (hπ : Function.Surjective π) :
    (maximalIdeal R).map π = maximalIdeal S := by
  rw [← comap_maximalIdeal π, Ideal.map_comap_of_surjective _ hπ]

end Surjective

/-! ### Transport of the strict associated-prime condition along a surjection -/

section Transport

variable {R S : Type*} [CommRing R] [CommRing S] {M N : Type*}
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]
  (π : R →+* S) (φ : M ≃+ N) (hφ : ∀ (r : R) (m : M), φ (r • m) = π r • φ m)

include hφ

/-- The annihilator of an element is the contraction of the annihilator of its image. -/
private theorem comap_colon_singleton_aux (m : M) :
    ((⊥ : Submodule S N).colon {φ m}).comap π = (⊥ : Submodule R M).colon {m} := by
  ext r
  simp only [Ideal.mem_comap, Submodule.mem_colon_singleton, Submodule.mem_bot, ← hφ,
    AddEquiv.map_eq_zero_iff]

/-- The annihilator of a transported element is the image of the annihilator. -/
theorem colon_singleton_map (hπ : Function.Surjective π) (m : M) :
    (⊥ : Submodule S N).colon {φ m} = ((⊥ : Submodule R M).colon {m}).map π := by
  rw [← comap_colon_singleton_aux π φ hφ m, Ideal.map_comap_of_surjective _ hπ]

/-- The annihilator of an element is the contraction of the annihilator of its image. -/
theorem colon_singleton_comap (m : M) :
    ((⊥ : Submodule S N).colon {φ m}).comap π = (⊥ : Submodule R M).colon {m} :=
  comap_colon_singleton_aux π φ hφ m

/-- **The strict (Stacks Tag 00LA) condition that the maximal ideal is an associated prime is
the same on both sides of a surjection of local rings**, for modules matched by an additive
equivalence which is semilinear over it. -/
theorem isAssociatedPrimeStacks_maximalIdeal_congr [IsLocalRing R] [IsLocalRing S]
    [IsLocalHom π] (hπ : Function.Surjective π) :
    IsAssociatedPrimeStacks R M (maximalIdeal R) ↔
      IsAssociatedPrimeStacks S N (maximalIdeal S) := by
  refine ⟨fun ⟨_, m, hm⟩ ↦ ⟨(maximalIdeal.isMaximal S).isPrime, φ m, ?_⟩,
    fun ⟨_, n, hn⟩ ↦ ⟨(maximalIdeal.isMaximal R).isPrime, φ.symm n, ?_⟩⟩
  · rw [Submodule.colon_span, colon_singleton_map π φ hφ hπ m,
      ← Submodule.colon_span (R := R) (N := (⊥ : Submodule R M)), hm,
      map_maximalIdeal π hπ]
  · rw [Submodule.colon_span, ← colon_singleton_comap π φ hφ (φ.symm n),
      AddEquiv.apply_symm_apply, ← Submodule.colon_span (R := S) (N := (⊥ : Submodule S N)),
      hn, comap_maximalIdeal π]

end Transport

/-! ### The strict and the radical notions of associated prime -/

section Strict

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] {p : Ideal R}

/-- A prime which is literally the annihilator of an element is its own radical, so the
Stacks Project's associated primes are among Mathlib's. -/
alias mem_associatedPrimes_of_isAssociatedPrimeStacks :=
  Stacks.Divisors.mem_associatedPrimes_of_isAssociatedPrimeStacks

/-- Over a Noetherian ring the radical in Mathlib's definition may be dropped, so Mathlib's
associated primes are the Stacks Project's. -/
theorem isAssociatedPrimeStacks_of_mem_associatedPrimes [IsNoetherianRing R]
    (h : p ∈ associatedPrimes R M) : IsAssociatedPrimeStacks R M p := by
  obtain ⟨hprime, m, hm⟩ := Submodule.isAssociatedPrime_iff.mp h
  exact ⟨hprime, m, by rw [Submodule.colon_span]; exact hm.symm⟩

end Strict

/-! ### The reduction of a module as a module over the quotient ring -/

section Reduction

variable {R : Type*} [CommRing R] (I : Ideal R) (M : Type*) [AddCommGroup M] [Module R M]

/-- The ideal `I` annihilates the reduction `M ⧸ I·M`. -/
theorem isTorsionBySet_quotSMulTop :
    Module.IsTorsionBySet R (M ⧸ (I • (⊤ : Submodule R M))) (I : Set R) := by
  intro z a
  obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule R M)) z
  rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact Submodule.smul_mem_smul a.2 Submodule.mem_top

/-- The `R ⧸ I`-module structure on the reduction `M ⧸ I·M`. -/
@[instance_reducible]
noncomputable def quotSMulTopModule :
    Module (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M))) :=
  (isTorsionBySet_quotSMulTop I M).module

/-- Acting through `R ⧸ I` on the reduction is acting through `R`. -/
theorem isScalarTower_quotSMulTop :
    letI := quotSMulTopModule I M
    IsScalarTower R (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M))) :=
  (isTorsionBySet_quotSMulTop I M).isScalarTower

end Reduction

/-! ### Associated primes over a quotient of the base ring -/

section QuotientBase

variable {R : Type*} [CommRing R] (I : Ideal R) {N : Type*} [AddCommGroup N]
  [Module R N] [Module (R ⧸ I) N] [IsScalarTower R (R ⧸ I) N]

/-- The annihilator over `R` of an element of an `R ⧸ I`-module is the contraction of its
annihilator over `R ⧸ I`. -/
theorem colon_singleton_comap_mk (z : N) :
    (⊥ : Submodule R N).colon {z}
      = ((⊥ : Submodule (R ⧸ I) N).colon {z}).comap (Ideal.Quotient.mk I) := by
  ext r
  rw [Ideal.mem_comap]
  simp only [Submodule.mem_colon_singleton, Submodule.mem_bot]
  rw [← IsScalarTower.algebraMap_smul (R ⧸ I) r z, Ideal.Quotient.algebraMap_eq]

/-- Every associated prime over `R` of a module on which `I` acts as zero contains `I`. -/
theorem le_of_mem_associatedPrimes {p : Ideal R} (hp : p ∈ associatedPrimes R N) : I ≤ p := by
  obtain ⟨-, z, hz⟩ := hp
  intro i hi
  rw [hz]
  refine Ideal.le_radical ?_
  rw [colon_singleton_comap_mk I z, Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hi]
  exact Ideal.zero_mem _

/-- **Stacks Tag 05BY for Mathlib's radical convention, one direction.** Associated primes over
`R` of an `R ⧸ I`-module push forward to associated primes over `R ⧸ I`. -/
theorem map_mem_associatedPrimes_quotient {p : Ideal R} (hp : p ∈ associatedPrimes R N) :
    p.map (Ideal.Quotient.mk I) ∈ associatedPrimes (R ⧸ I) N := by
  have hsurj := Ideal.Quotient.mk_surjective (I := I)
  obtain ⟨hprime, z, hz⟩ := hp
  have := hprime
  have hker : RingHom.ker (Ideal.Quotient.mk I) ≤ p := by
    rw [Ideal.mk_ker]
    exact le_of_mem_associatedPrimes I ⟨hprime, z, hz⟩
  refine ⟨Ideal.map_isPrime_of_surjective hsurj hker, z, ?_⟩
  have hcomap : p = (((⊥ : Submodule (R ⧸ I) N).colon {z}).radical).comap
      (Ideal.Quotient.mk I) := by
    rw [Ideal.comap_radical, ← colon_singleton_comap_mk I z, hz]
  rw [hcomap, Ideal.map_comap_of_surjective _ hsurj]

/-- **Stacks Tag 05BY for Mathlib's radical convention, the other direction.** -/
theorem comap_mem_associatedPrimes_quotient {q : Ideal (R ⧸ I)}
    (hq : q ∈ associatedPrimes (R ⧸ I) N) :
    q.comap (Ideal.Quotient.mk I) ∈ associatedPrimes R N := by
  obtain ⟨hprime, z, hz⟩ := hq
  have := hprime
  refine ⟨Ideal.comap_isPrime _ _, z, ?_⟩
  rw [hz, Ideal.comap_radical, ← colon_singleton_comap_mk I z]

/-- **The upgrade used downstream.** For a module killed by `I` over a local ring `R`, Mathlib's
radical condition on `𝔪_R` becomes the Stacks Project's strict condition as soon as the
*quotient* `R ⧸ I` is Noetherian. This matters because the ring of interest is a stalk which is
only essentially of finite type over a valuation ring, hence not Noetherian, while its reduction
is of finite type over a field. -/
theorem isAssociatedPrimeStacks_maximalIdeal_of_mem_associatedPrimes [IsLocalRing R]
    [IsLocalRing (R ⧸ I)] [IsNoetherianRing (R ⧸ I)]
    (h : maximalIdeal R ∈ associatedPrimes R N) :
    IsAssociatedPrimeStacks R N (maximalIdeal R) := by
  have hsurj := Ideal.Quotient.mk_surjective (I := I)
  have hlh : IsLocalHom (Ideal.Quotient.mk I) :=
    IsLocalHom.of_surjective (Ideal.Quotient.mk I) hsurj
  have h2 := map_mem_associatedPrimes_quotient I h
  rw [map_maximalIdeal (Ideal.Quotient.mk I) hsurj] at h2
  refine (isAssociatedPrimeStacks_maximalIdeal_congr (Ideal.Quotient.mk I) (AddEquiv.refl N)
    (fun r z ↦ ?_) hsurj).mpr (isAssociatedPrimeStacks_of_mem_associatedPrimes h2)
  exact (IsScalarTower.algebraMap_smul (R ⧸ I) r z).symm

end QuotientBase

end Stacks.FibreStalkModule
