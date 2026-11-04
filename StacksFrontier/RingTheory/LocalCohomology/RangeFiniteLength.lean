module

public import Mathlib.RingTheory.FiniteLength
public import StacksFrontier.RingTheory.LocalCohomology.UniformVanishingSpread
public import StacksFrontier.RingTheory.Support.Finite

/-!
# The image of a map that vanishes away from the closed point has finite length

Let `A` be a Noetherian local ring with maximal ideal `𝔪` and let `h : M → N` be an `A`-linear
map into a finite `A`-module.  If the localization of `h` at every prime other than `𝔪` is zero,
then the image of `h` has finite length.

This is the step with which the proof of [Stacks, Tag 0DXU] passes from "this map is zero after
localization at a prime `𝔮` containing `f` and different from `𝔪`" to "the image has finite
length": the image is a finite module, so its support is the zero locus of its annihilator, and
a finite module supported at the closed point alone has finite length.

## Main results

* `Stacks.LocalCohomology.isFiniteLength_range_of_forall_exists_smul_eq_zero` — the statement
  above, with the vanishing of the localized map written elementwise.
* `Stacks.LocalCohomology.isFiniteLength_range_of_forall_isLocalizedModule_map_eq_zero` — the
  same with the vanishing written as `IsLocalizedModule.map 𝔮ᶜ f g h = 0`, which is the form the
  localization of a map of `Ext` modules produces.

## Implementation notes

`Stacks.LocalCohomology.notMem_support_range_iff` already identifies the primes outside the
support of the image with the primes at which every value of `h` is annihilated, and
`Stacks.LocalCohomology.isLocalizedModule_map_eq_zero_iff` rewrites the vanishing of a localized
map elementwise, so the only content here is the dichotomy "support empty or the closed point":
`isFiniteLength_of_support` asks for the support to *equal* the singleton, while a zero image has
empty support and is handled by `IsFiniteLength.of_subsingleton`.

## References

* [Stacks Project, Tag 0DXU](https://stacks.math.columbia.edu/tag/0DXU)
* [Stacks Project, Tag 00L5](https://stacks.math.columbia.edu/tag/00L5), a finite module
  supported at the closed point has finite length.
-/

@[expose] public section

universe u v

namespace Stacks.LocalCohomology

/-- **The image of a map vanishing away from the closed point has finite length.**  Let `A` be a
Noetherian local ring and let `h : M → N` be an `A`-linear map into a finite `A`-module.  If for
every prime `𝔭 ≠ 𝔪` and every `m : M` some element outside `𝔭` annihilates `h m` — that is, if
the localization of `h` at every prime other than the closed point vanishes — then the image of
`h` has finite length as an `A`-module.

This is the reduction "the modules in question are finite `A`-modules supported at `V(f)`, thus
it suffices to show that this map is zero after localization at a prime `𝔮` containing `f` and
different from `𝔪`" of the proof of [Stacks, Tag 0DXU], read in the direction that produces the
finite length. -/
theorem isFiniteLength_range_of_forall_exists_smul_eq_zero {A : Type u} [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] {M N : Type v} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] [Module.Finite A N] (h : M →ₗ[A] N)
    (hvan : ∀ p : PrimeSpectrum A, p ≠ IsLocalRing.closedPoint A →
      ∀ m : M, ∃ r ∉ p.asIdeal, r • h m = 0) :
    IsFiniteLength A ↥(LinearMap.range h) := by
  have : IsNoetherian A N := isNoetherian_of_isNoetherianRing_of_finite A N
  have hfin : Module.Finite A ↥(LinearMap.range h) :=
    Module.Finite.iff_fg.mpr (IsNoetherian.noetherian _)
  have hsub : Module.support A ↥(LinearMap.range h) ⊆ {IsLocalRing.closedPoint A} := by
    intro p hp
    by_contra hne
    exact (notMem_support_range_iff h p).mpr (hvan p (by simpa using hne)) hp
  rcases Set.subset_singleton_iff_eq.mp hsub with hempty | heq
  · have : Subsingleton ↥(LinearMap.range h) := Module.support_eq_empty_iff.mp hempty
    exact IsFiniteLength.of_subsingleton
  · exact isFiniteLength_of_support heq

/-- **The image of a map vanishing away from the closed point has finite length**, with the
vanishing hypothesis written as the vanishing of the localized map.  For every prime `𝔭 ≠ 𝔪` the
localization of `h` along arbitrary models `f` of `M_𝔭` and `g` of `N_𝔭` is assumed zero; the
image of `h` then has finite length.

This is the form the proof of [Stacks, Tag 0DXU] produces, the localized map being the one
obtained from `Dualizing.localizedExtLinearEquivOfDerivedHom` and its naturality. -/
theorem isFiniteLength_range_of_forall_isLocalizedModule_map_eq_zero {A : Type u} [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] {M N : Type v} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] [Module.Finite A N]
    (M' N' : PrimeSpectrum A → Type v)
    [∀ p, AddCommGroup (M' p)] [∀ p, Module A (M' p)]
    [∀ p, AddCommGroup (N' p)] [∀ p, Module A (N' p)]
    (f : ∀ p : PrimeSpectrum A, M →ₗ[A] M' p)
    [∀ p, IsLocalizedModule p.asIdeal.primeCompl (f p)]
    (g : ∀ p : PrimeSpectrum A, N →ₗ[A] N' p)
    [∀ p, IsLocalizedModule p.asIdeal.primeCompl (g p)]
    (h : M →ₗ[A] N)
    (hvan : ∀ p : PrimeSpectrum A, p ≠ IsLocalRing.closedPoint A →
      IsLocalizedModule.map p.asIdeal.primeCompl (f p) (g p) h = 0) :
    IsFiniteLength A ↥(LinearMap.range h) :=
  isFiniteLength_range_of_forall_exists_smul_eq_zero h fun p hp =>
    (isLocalizedModule_map_eq_zero_iff p.asIdeal.primeCompl (f p) (g p) h).mp (hvan p hp)

end Stacks.LocalCohomology

end
