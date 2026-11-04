module

public import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.Defs

/-!
# Associated primes of a localization, seen in the spectrum of the base ring

Let `R` be a ring, `M` an `R`-module and `S ⊆ R` a multiplicative subset. The canonical map
`Spec(S⁻¹R) → Spec(R)`, `𝔮 ↦ 𝔮 ∩ R`, is injective, with image the primes of `R` disjoint
from `S`. Through it, the associated primes of `S⁻¹M` and of `M` compare as follows
(Stacks, Tag 05BZ):

1. `Ass_R(S⁻¹M) = Ass_{S⁻¹R}(S⁻¹M)`;
2. `Ass_R(M) ∩ Spec(S⁻¹R) ⊆ Ass_R(S⁻¹M)`;
3. if `R` is Noetherian, the inclusion of (2) is an equality.

Associated primes are taken in the Stacks sense (Tag 00LA): a prime equal to the annihilator of
a single element, `Stacks.AssociatedPrimes.assPrimes`. This is *not* Mathlib's
`associatedPrimes`, which only asks for the radical of such an annihilator; the two agree over
a Noetherian ring, which is how Mathlib's Tag 0310 enters the proof of (3).

The localization is encoded by its universal properties: `R'` is a ring with
`IsLocalization S R'`, and `S⁻¹M` is any `R`-module `M'` with an `R`-linear map
`f : M →ₗ[R] M'` satisfying `IsLocalizedModule S f`, carrying an `R'`-module structure compatible
with its `R`-module structure. The subset `Spec(S⁻¹R) ⊆ Spec(R)` is the image under
`Ideal.comap (algebraMap R R')` of the prime ideals of `R'`.

## Main results

* `Stacks.AssociatedPrimes.torsionOf_eq_comap_algebraMap`: the annihilator in `R` of an element
  of an `R'`-module is the contraction of its annihilator in `R'`.
* `Stacks.AssociatedPrimes.assPrimes_eq_image_comap_assPrimes` (part (1)), which in fact holds
  for every `R'`-module.
* `Stacks.AssociatedPrimes.mem_assPrimes_of_disjoint`: an associated prime of `M` disjoint
  from `S` is an associated prime of `S⁻¹M`.
* `Stacks.AssociatedPrimes.assPrimes_inter_image_comap_subset` (part (2)).
* `Stacks.AssociatedPrimes.assPrimes_inter_image_comap_eq` (part (3)).

## References

* [Stacks Project, Tag 05BZ](https://stacks.math.columbia.edu/tag/05BZ)
* [Stacks Project, Tag 0310](https://stacks.math.columbia.edu/tag/0310)
-/

@[expose] public section

namespace Stacks.AssociatedPrimes

variable {R : Type*} [CommRing R]

/-- The annihilator of an element of a module, written with `Ideal.torsionOf`, is the colon
ideal used in Mathlib's `IsAssociatedPrime`. -/
private theorem torsionOf_eq_colon {M : Type*} [AddCommGroup M] [Module R M] (m : M) :
    Ideal.torsionOf R M m = (⊥ : Submodule R M).colon {m} := by
  ext r
  rw [Ideal.mem_torsionOf_iff, Submodule.mem_colon_singleton, Submodule.mem_bot]

/-- A Stacks associated prime is a Mathlib associated prime. -/
private theorem mem_associatedPrimes_of_mem_assPrimes {M : Type*} [AddCommGroup M] [Module R M]
    {p : Ideal R} (hp : p ∈ assPrimes R M) : p ∈ associatedPrimes R M := by
  obtain ⟨hpr, m, rfl⟩ := hp
  exact ⟨hpr, m, by rw [← torsionOf_eq_colon, hpr.radical]⟩

/-- Over a Noetherian ring, a Mathlib associated prime is a Stacks associated prime. -/
private theorem mem_assPrimes_of_mem_associatedPrimes [IsNoetherianRing R] {M : Type*}
    [AddCommGroup M] [Module R M] {p : Ideal R} (hp : p ∈ associatedPrimes R M) :
    p ∈ assPrimes R M := by
  obtain ⟨hpr, m, hm⟩ := isAssociatedPrime_iff.mp hp
  exact ⟨hpr, m, by rw [torsionOf_eq_colon, hm]⟩

/-- For an `R`-algebra `R'` and an `R'`-module `M` (viewed as an `R`-module through
`R → R'`), the annihilator in `R` of `m : M` is the contraction of its annihilator in `R'`. -/
theorem torsionOf_eq_comap_algebraMap {R' M : Type*} [CommRing R'] [Algebra R R']
    [AddCommGroup M] [Module R M] [Module R' M] [IsScalarTower R R' M] (m : M) :
    Ideal.torsionOf R M m = (Ideal.torsionOf R' M m).comap (algebraMap R R') := by
  ext r
  rw [Ideal.mem_comap, Ideal.mem_torsionOf_iff, Ideal.mem_torsionOf_iff, algebraMap_smul]

variable (S : Submonoid R) (R' : Type*) [CommRing R'] [Algebra R R'] [IsLocalization S R']

section AnyModule

variable {M' : Type*} [AddCommGroup M'] [Module R M'] [Module R' M'] [IsScalarTower R R' M']

include S in
/-- **Stacks 05BZ (1).** For `R'` a localization `S⁻¹R` and any `R'`-module `M'` (in particular
`M' = S⁻¹M`), the associated primes of `M'` over `R` are the contractions along
`Spec(S⁻¹R) → Spec(R)` of its associated primes over `R'`:
`Ass_R(M') = Ass_{S⁻¹R}(M')`. -/
@[stacks 05BZ "(1)"]
theorem assPrimes_eq_image_comap_assPrimes :
    assPrimes R M' = Ideal.comap (algebraMap R R') '' assPrimes R' M' := by
  ext p
  constructor
  · rintro ⟨hp, m, rfl⟩
    refine ⟨Ideal.torsionOf R' M' m, ⟨?_, m, rfl⟩, (torsionOf_eq_comap_algebraMap m).symm⟩
    rw [torsionOf_eq_comap_algebraMap (R' := R') m] at hp
    refine (IsLocalization.isPrime_iff_isPrime_disjoint S R' _).mpr
      ⟨hp, (IsLocalization.disjoint_under_iff S R' _).mpr fun htop => hp.ne_top ?_⟩
    rw [htop, Ideal.comap_top]
  · rintro ⟨J, ⟨hJ, m, rfl⟩, rfl⟩
    exact ⟨hJ.comap _, m, torsionOf_eq_comap_algebraMap m⟩

end AnyModule

section Localization

variable {M M' : Type*} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
  (f : M →ₗ[R] M') [IsLocalizedModule S f]

include f in
/-- An associated prime of `M` which is disjoint from `S` is an associated prime of the
localization `S⁻¹M` (as an `R`-module): if `p = Ann_R(m)`, then `p = Ann_R(m / 1)`. -/
theorem mem_assPrimes_of_disjoint {p : Ideal R} (hp : p ∈ assPrimes R M)
    (hS : Disjoint (S : Set R) p) : p ∈ assPrimes R M' := by
  obtain ⟨hpr, m, rfl⟩ := hp
  refine ⟨hpr, f m, le_antisymm (fun r hr => ?_) fun r hr => ?_⟩
  · rw [Ideal.mem_torsionOf_iff, ← map_smul, IsLocalizedModule.eq_zero_iff S f] at hr
    obtain ⟨s, hs⟩ := hr
    have hsr : (s : R) * r ∈ Ideal.torsionOf R M m := by
      rw [Ideal.mem_torsionOf_iff, mul_smul, ← Submonoid.smul_def]
      exact hs
    exact (hpr.mem_or_mem hsr).resolve_left (Set.disjoint_left.mp hS s.2)
  · rw [Ideal.mem_torsionOf_iff] at hr ⊢
    rw [← map_smul, hr, map_zero]

include S f in
/-- **Stacks 05BZ (2).** Via the canonical injection `Spec(S⁻¹R) → Spec(R)`, whose image is
`Ideal.comap (algebraMap R R') '' {J | J.IsPrime}`, we have
`Ass_R(M) ∩ Spec(S⁻¹R) ⊆ Ass_R(S⁻¹M)`. -/
@[stacks 05BZ "(2)"]
theorem assPrimes_inter_image_comap_subset :
    assPrimes R M ∩ Ideal.comap (algebraMap R R') '' {J | J.IsPrime} ⊆ assPrimes R M' := by
  rintro p ⟨hp, J, hJ, rfl⟩
  exact mem_assPrimes_of_disjoint S f hp
    ((IsLocalization.disjoint_under_iff S R' J).mpr hJ.ne_top)

variable [Module R' M'] [IsScalarTower R R' M']

open Module.associatedPrimes in
include S f in
/-- **Stacks 05BZ (3).** If `R` is Noetherian, the inclusion of Stacks 05BZ (2) is an equality:
`Ass_R(M) ∩ Spec(S⁻¹R) = Ass_R(S⁻¹M)`. -/
@[stacks 05BZ "(3)"]
theorem assPrimes_inter_image_comap_eq [IsNoetherianRing R] :
    assPrimes R M ∩ Ideal.comap (algebraMap R R') '' {J | J.IsPrime} = assPrimes R M' := by
  refine (assPrimes_inter_image_comap_subset S R' f).antisymm fun p hp => ?_
  rw [assPrimes_eq_image_comap_assPrimes S R'] at hp
  obtain ⟨J, hJ, rfl⟩ := hp
  refine ⟨mem_assPrimes_of_mem_associatedPrimes ?_, J, hJ.1, rfl⟩
  exact comap_mem_associatedPrimes_of_mem_associatedPrimes_of_isLocalizedModule_of_fg
    S f J (mem_associatedPrimes_of_mem_assPrimes hJ) ((isNoetherianRing_iff_ideal_fg R).mp ‹_› _)

end Localization

end Stacks.AssociatedPrimes
