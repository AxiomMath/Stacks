module

public import Mathlib.RingTheory.Spectrum.Prime.Chevalley
public import StacksFrontier.RingTheory.Flat.ProjectiveOfIntegralFibres
public import StacksFrontier.RingTheory.GeometricallyIntegral.GenericFibre
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Spreading out a bad generic fibre, and Stacks 05FT from the good halves alone

`StacksFrontier.RingTheory.GeometricallyIntegral.IrreducibleLocus` reduces Stacks 05FT to one
statement about a single generic fibre: over a Noetherian domain `D` with a finite type algebra
`T`, some nonempty basic open of `Spec D` either lies in or misses
`Algebra.geometricallyIntegralFibreLocus D T`. Which of the two alternatives can hold is decided
by the generic point `(0)`, which belongs to every nonempty basic open: if `(0)` lies in the
locus only the inclusion is possible, and if it does not, only the disjointness.

**This file proves the second alternative**, for the geometrically integral fibre locus and for
the geometrically reduced fibre locus alike. If the generic fibre fails to be geometrically
integral (respectively geometrically reduced) then some nonempty basic open of `Spec D` misses the
locus entirely. For the reduced locus this is the affine case of Stacks 0577 at the generic point.
What remains of Stacks 05FT is therefore the *good* halves: if the generic fibre is geometrically
reduced, respectively geometrically irreducible, so are the fibres over a nonempty basic open,
which are the affine cases of Stacks 0578 and Stacks 055A at the generic point. Those two, and
nothing else, are the hypotheses of
`Algebra.projective_of_geometricallyIntegral_fibres_of_good_halves`.

**The argument.** A failure of geometric integrality of the generic fibre is a field `K` with
`D → K` injective and two nonzero elements of `T ⊗[D] K` with product zero (or the degenerate
failure that `T ⊗[D] K` is the zero ring); a failure of geometric reducedness is a nonzero
nilpotent element of `T ⊗[D] K`. Finitely many elements of `T ⊗[D] K` involve only finitely many
elements of `K`, so they come from `E ⊗[D] T` for a finite type `D`-subalgebra `E ⊆ K`; enlarging
`E` by the inverse of one element of `D` makes `E ⊗[D] T` a free `E`-module, by generic freeness
over `D` (Stacks 051Z, `Module.Free.exists_ne_zero_of_isReduced`) and base change. Freeness is
what makes the failure spread: it makes `E ⊗[D] T → K ⊗[D] T` injective, so the relations hold
already in `E ⊗[D] T`, and it provides coordinate functionals which keep the witnesses nonzero in
the fibre `κ(q) ⊗[E] (E ⊗[D] T) = T ⊗[D] κ(q)` for every prime `q` of `E` in a suitable basic
open, so that fibre fails the property too. Finally Chevalley's theorem makes the image in
`Spec D` of that basic open of `Spec E` constructible; it contains the generic point, hence a
nonempty basic open of `Spec D`, every prime of which is the contraction of a prime of `E` with a
bad fibre.

Note that `T` is not assumed flat and the primes of `E` are not assumed to lie over the generic
point of `D`: the whole argument runs over `Spec E`, and the only thing asked of
`Spec E → Spec D` is Chevalley's theorem.

## Main definitions

* `Algebra.subalgebraTensorMap`: the map `E ⊗[D] T → K ⊗[D] T` induced by a `D`-subalgebra
  `E ⊆ K`.

## Main results

* `PrimeSpectrum.exists_ne_zero_basicOpen_subset_of_isConstructible`: a constructible subset of
  the spectrum of a domain containing the generic point contains a nonempty basic open.
* `Algebra.subalgebraTensorMap_injective`: if `E ⊗[D] T` is free over `E` then
  `E ⊗[D] T → K ⊗[D] T` is injective.
* `Algebra.exists_subalgebra_finiteType_free`: **the auxiliary algebra.** Any finite subset of a
  field `K` over `D` lies in a finite type `D`-subalgebra `E ⊆ K` for which `E ⊗[D] T` is a free
  `E`-module.
* `Algebra.exists_ne_zero_disjoint_of_forall_not_mem_comap`: the Chevalley step — a set of primes
  of `D` avoided by the contractions of a nonempty basic open of `Spec E` is disjoint from a
  nonempty basic open of `Spec D`.
* `Algebra.exists_ne_zero_disjoint_geometricallyIntegralFibreLocus`: **the bad half of the
  generic-fibre dichotomy for geometric integrality.** If the generic point of `Spec D` is outside
  the geometrically integral fibre locus of `T`, then some nonempty basic open of `Spec D` is
  disjoint from it.
* `Algebra.exists_ne_zero_disjoint_geometricallyReducedFibreLocus`: **the affine case of Stacks
  0577 at the generic point**, the same statement for the geometrically reduced fibre locus.
* `Algebra.exists_basicOpen_geometricallyIntegral_of_goodGeneric`: the generic-fibre dichotomy
  needed by Stacks 05FT, granted only its good half.
* `Algebra.exists_basicOpen_subset_geometricallyIntegralFibreLocus_of_good_halves`: that good half
  from the good halves for the reduced and the irreducible locus separately, which are the affine
  cases of Stacks 0578 and Stacks 055A.
* `Algebra.projective_of_geometricallyIntegral_fibres_of_goodGeneric`: Stacks 05FT granted only
  that good half.
* `Algebra.projective_of_geometricallyIntegral_fibres_of_good_halves`: **Stacks 05FT granted only
  the affine cases of Stacks 0578 and Stacks 055A at the generic point.**
* `Algebra.isConstructible_geometricallyReducedFibreLocus_of_goodGeneric`: the affine case of
  Stacks 0579 granted only the good half of Stacks 0577.

## Implementation notes

The auxiliary algebra `E` is realized as a `Subalgebra D K` rather than as an abstract finite type
`D`-algebra with a map to `K`: then `E → K` is `Subalgebra.val`, which is injective by
construction and needs no hypothesis, and `Algebra D ↥E` and `IsScalarTower D ↥E K` are
instances. The single localization that the argument needs, the inversion of the element `g` of
`D` produced by generic freeness, is accordingly performed inside `K`, by adjoining
`(algebraMap D K g)⁻¹` to `E`; the `Localization.Away g`-algebra structure on `↥E` that transports
freeness is then obtained from `IsLocalization.Away.lift`.

Generic freeness is applied over `D` and not over `E`, with the resulting localization absorbed
into the choice of `E`; this is possible because freeness of `E ⊗[D] T` over `E` for `E` a
`D_g`-algebra follows from freeness of `D_g ⊗[D] T` over `D_g` by base change, and it is what
keeps the number of localizations at one.

The degenerate failure — `T ⊗[D] K` the zero ring — is carried along as the left alternative of
the witness disjunction, and is where the argument needs no witnesses at all: freeness makes
`E ⊗[D] T` the zero ring too, so *every* fibre of `E` is the zero ring and any nonzero element of
`E` serves. It does not arise for the reduced locus, the zero ring being reduced.

Nothing here carries a `@[stacks 05FT]` or `@[stacks 0577]` attribute. The statements proved are
the affine, Noetherian case of one half of Stacks 0577 and of its analogue for geometric
integrality, and Stacks 05FT conditional on the other halves.

The remaining good halves have since been supplied — the irreducible one in
`StacksFrontier.RingTheory.Flat.GeometricallyIrreducibleFibreLocus`, the reduced one in
`StacksFrontier.RingTheory.GeometricallyIntegral.ReducedFibreFromSmoothLocus` — so the conditional
statements below are all discharged downstream, and Stacks 05FT is proved and tagged there as
`Algebra.projective_of_geometricallyIntegral_fibres`. They are kept in conditional form because
they are what the discharging files import. Stacks 0577 is still untagged *here*, and for a
reason unaffected by that: this file proves only the affine Noetherian case, whereas Stacks 0577
is a statement about an arbitrary finite type morphism to an irreducible scheme, which is
`AlgebraicGeometry.exists_open_forall_not_geometricallyReduced_fiber`.

## References

* [Stacks Project, Tag 05FT](https://stacks.math.columbia.edu/tag/05FT)
* [Stacks Project, Tag 0577](https://stacks.math.columbia.edu/tag/0577)
* [Stacks Project, Tag 0578](https://stacks.math.columbia.edu/tag/0578)
* [Stacks Project, Tag 0579](https://stacks.math.columbia.edu/tag/0579)
* [Stacks Project, Tag 055A](https://stacks.math.columbia.edu/tag/055A)
* [Stacks Project, Tag 051Z](https://stacks.math.columbia.edu/tag/051Z)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CommRingCat PrimeSpectrum Topology

open scoped TensorProduct

universe u

namespace PrimeSpectrum

/-- **A constructible set containing the generic point contains a nonempty basic open.** Let `R`
be a domain and let `E ⊆ Spec R` be constructible with `(0) ∈ E`. Then `D(f) ⊆ E` for some
nonzero `f : R`.

Writing `E` as a finite union of pieces `V(g₁, …, gₙ) \ V(f)`, the generic point lies in one of
them; there every `gᵢ` lies in `(0)`, hence is zero, so that piece is all of `D(f)`, and `f` does
not lie in `(0)`, hence is nonzero. -/
theorem exists_ne_zero_basicOpen_subset_of_isConstructible {R : Type u} [CommRing R] [IsDomain R]
    {E : Set (PrimeSpectrum R)} (hE : IsConstructible E)
    (hbot : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R) ∈ E) :
    ∃ f : R, f ≠ 0 ∧ (basicOpen f : Set (PrimeSpectrum R)) ⊆ E := by
  obtain ⟨C, hC⟩ := exists_constructibleSetData_iff.mpr hE
  subst hC
  obtain ⟨c, hcC, hc1, hc2⟩ := Set.mem_iUnion₂.mp hbot
  refine ⟨c.f, fun h0 => hc2 (by simp [h0]), fun p hp => Set.mem_biUnion hcC ⟨?_, ?_⟩⟩
  · rw [mem_zeroLocus] at hc1 ⊢
    intro x hx
    have hx0 := hc1 hx
    simp only [SetLike.mem_coe, Ideal.mem_bot] at hx0
    exact hx0 ▸ p.asIdeal.zero_mem
  · simpa [mem_zeroLocus] using (mem_basicOpen _ _).mp hp

end PrimeSpectrum

namespace Algebra

section Subalgebra

variable (D T K : Type u) [CommRing D] [CommRing T] [Algebra D T] [CommRing K] [Algebra D K]

/-- The map `↥E ⊗[D] T → K ⊗[D] T` induced by a `D`-subalgebra `E` of `K`. It exhibits the base
change of `T` to `E` inside the base change of `T` to `K`. -/
noncomputable def subalgebraTensorMap (E : Subalgebra D K) : ↥E ⊗[D] T →ₐ[D] K ⊗[D] T :=
  TensorProduct.map E.val (AlgHom.id D T)

/-- `subalgebraTensorMap` sends a pure tensor `e ⊗ₜ t` to `(e : K) ⊗ₜ t`. -/
@[simp]
theorem subalgebraTensorMap_tmul (E : Subalgebra D K) (e : ↥E) (t : T) :
    subalgebraTensorMap D T K E (e ⊗ₜ t) = (e : K) ⊗ₜ t := rfl

/-- The structure map of a `D`-subalgebra of `K` is injective as soon as `D → K` is: it is a
factor of `D → K`. -/
theorem injective_algebraMap_subalgebra (hDK : Function.Injective (algebraMap D K))
    (E : Subalgebra D K) : Function.Injective (algebraMap D ↥E) := fun x y hxy => by
  refine hDK ?_
  rw [IsScalarTower.algebraMap_apply D ↥E K, IsScalarTower.algebraMap_apply D ↥E K, hxy]

/-- **An element of `K ⊗[D] T` written as a sum of pure tensors whose left factors lie in a
subalgebra `E` comes from `↥E ⊗[D] T`.** This is how a finite amount of data in `K ⊗[D] T` is
pushed down to a finite type `D`-subalgebra of `K`. -/
theorem mem_range_subalgebraTensorMap {E : Subalgebra D K} {x : K ⊗[D] T}
    {s : Finset (K × T)} (hmem : ∀ i ∈ s, i.1 ∈ E) (hx : x = ∑ i ∈ s, i.1 ⊗ₜ i.2) :
    x ∈ Set.range (subalgebraTensorMap D T K E) := by
  have hrange : x ∈ LinearMap.range (subalgebraTensorMap D T K E).toLinearMap := by
    rw [hx]
    refine Submodule.sum_mem _ fun i hi => ⟨(⟨i.1, hmem i hi⟩ : ↥E) ⊗ₜ i.2, ?_⟩
    simp
  obtain ⟨z, hz⟩ := hrange
  exact ⟨z, hz⟩

/-- **A free base change injects into the base change to the ambient field.** If `K` is a field,
`E ⊆ K` a `D`-subalgebra and `↥E ⊗[D] T` is free as an `↥E`-module, then
`↥E ⊗[D] T → K ⊗[D] T` is injective.

The map is the composite of `z ↦ 1 ⊗ₜ z : ↥E ⊗[D] T → K ⊗[↥E] (↥E ⊗[D] T)` with the cancellation
isomorphism `K ⊗[↥E] (↥E ⊗[D] T) ≃ K ⊗[D] T`; the first is injective by
`Module.Free.one_tmul_ne_zero`, the inclusion `↥E → K` being injective, and the second is an
isomorphism. -/
theorem subalgebraTensorMap_injective {K : Type u} [Field K] [Algebra D K] (E : Subalgebra D K)
    [Module.Free ↥E (↥E ⊗[D] T)] : Function.Injective (subalgebraTensorMap D T K E) := by
  have hkey : ∀ z : ↥E ⊗[D] T,
      TensorProduct.cancelBaseChange D ↥E ↥E K T ((1 : K) ⊗ₜ[↥E] z) =
        subalgebraTensorMap D T K E z := by
    intro z
    induction z with
    | zero => simp
    | tmul e t => simp [Algebra.smul_def]
    | add z w hz hw => rw [TensorProduct.tmul_add, map_add, hz, hw, map_add]
  rw [injective_iff_map_eq_zero]
  intro z hz
  by_contra hz0
  refine Module.Free.one_tmul_ne_zero ↥E K Subtype.val_injective hz0 ?_
  have hzz := hkey z
  rw [hz] at hzz
  exact (map_eq_zero_iff _ (AlgEquiv.injective _)).mp hzz

end Subalgebra

variable {D T : Type u} [CommRing D] [IsDomain D] [IsNoetherianRing D] [CommRing T] [Algebra D T]

omit [IsNoetherianRing D] in
/-- **The auxiliary algebra of the spreading argument.** Let `D` be a Noetherian domain, `T` a
finite type `D`-algebra and `K` a field over `D` with `D → K` injective. Every finite subset `c`
of `K` is contained in a finite type `D`-subalgebra `E` of `K` such that the base change
`E ⊗[D] T` is a free `E`-module.

Generic freeness over `D` (Stacks 051Z) gives a nonzero `g : D` with `D_g ⊗[D] T` free over
`D_g`; take `E` to be the `D`-subalgebra of `K` generated by `c` together with
`(algebraMap D K g)⁻¹`. Then `g` is invertible in `E`, so `E` is an algebra over `D_g`, and
`E ⊗[D] T = E ⊗[D_g] (D_g ⊗[D] T)` is free over `E` as the base change of a free module. -/
theorem exists_subalgebra_finiteType_free [Algebra.FiniteType D T] (K : Type u) [Field K]
    [Algebra D K] (hDK : Function.Injective (algebraMap D K)) (c : Finset K) :
    ∃ (E : Subalgebra D K) (_ : Algebra.FiniteType D ↥E) (_ : Module.Free ↥E (↥E ⊗[D] T)),
      ∀ x ∈ c, x ∈ E := by
  obtain ⟨g, hg0, hgfree⟩ := Module.Free.exists_ne_zero_of_isReduced D T
  have hgK : algebraMap D K g ≠ 0 := fun h0 => hg0 (hDK (by rw [h0, map_zero]))
  set E : Subalgebra D K := Algebra.adjoin D (↑c ∪ {(algebraMap D K g)⁻¹}) with hE
  have hginv : (algebraMap D K g)⁻¹ ∈ E := Algebra.subset_adjoin (Set.mem_union_right _ rfl)
  have hft : Algebra.FiniteType D ↥E :=
    Algebra.FiniteType.adjoin_of_finite (c.finite_toSet.union (Set.finite_singleton _))
  have hunit : IsUnit (algebraMap D ↥E g) := by
    refine IsUnit.of_mul_eq_one ⟨(algebraMap D K g)⁻¹, hginv⟩ (Subtype.ext ?_)
    rw [Subalgebra.coe_mul, Subalgebra.coe_one,
      show ((algebraMap D ↥E g : ↥E) : K) = algebraMap D K g from rfl]
    exact mul_inv_cancel₀ hgK
  let : Algebra (Localization.Away g) ↥E := (IsLocalization.Away.lift g hunit).toAlgebra
  have : IsScalarTower D (Localization.Away g) ↥E :=
    IsScalarTower.of_algebraMap_eq' (IsLocalization.lift_comp _).symm
  exact ⟨E, hft, Module.Free.of_equiv
    (TensorProduct.cancelBaseChange D (Localization.Away g) ↥E ↥E T).toLinearEquiv,
    fun _ hx => Algebra.subset_adjoin (Set.mem_union_left _ hx)⟩

/-- **The Chevalley step.** Let `D` be a Noetherian domain and `E` a finite type `D`-algebra which
is a domain with `D → E` injective. If a nonzero `h : E` is such that no prime of `D(h) ⊆ Spec E`
contracts into a set `Z ⊆ Spec D`, then `Z` is disjoint from a nonempty basic open of `Spec D`.

The image of `D(h)` in `Spec D` is constructible by Chevalley's theorem, `D → E` being of finite
presentation because `D` is Noetherian, and it contains the generic point of `Spec D` because
`(0)` is a prime of the domain `E` avoiding `h` and contracting to `(0)`. So it contains a
nonempty basic open, by
`PrimeSpectrum.exists_ne_zero_basicOpen_subset_of_isConstructible`, and every prime of that basic
open is the contraction of a prime of `D(h)`, hence outside `Z`. -/
@[ega "IV 10.5.1" "c) ⇒ d)"]
theorem exists_ne_zero_disjoint_of_forall_not_mem_comap (E : Type u) [CommRing E] [IsDomain E]
    [Algebra D E] [Algebra.FiniteType D E] (hDE : Function.Injective (algebraMap D E))
    {Z : Set (PrimeSpectrum D)} {h : E} (hh0 : h ≠ 0)
    (hh : ∀ q : PrimeSpectrum E, h ∉ q.asIdeal → comap (algebraMap D E) q ∉ Z) :
    ∃ f : D, f ≠ 0 ∧ Disjoint (basicOpen f : Set (PrimeSpectrum D)) Z := by
  have hfp : (algebraMap D E).FinitePresentation :=
    RingHom.finitePresentation_algebraMap.mpr (Algebra.FinitePresentation.of_finiteType.mp ‹_›)
  have hcon : IsConstructible (comap (algebraMap D E) '' (basicOpen h : Set (PrimeSpectrum E))) :=
    isConstructible_comap_image hfp isConstructible_basicOpen
  have hbot : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum D) ∈
      comap (algebraMap D E) '' (basicOpen h : Set (PrimeSpectrum E)) := by
    refine ⟨⟨⊥, Ideal.isPrime_bot⟩, by simpa using hh0, PrimeSpectrum.ext ?_⟩
    rw [comap_asIdeal, ← RingHom.ker_eq_comap_bot]
    exact (RingHom.injective_iff_ker_eq_bot _).mp hDE
  obtain ⟨f, hf0, hfsub⟩ := exists_ne_zero_basicOpen_subset_of_isConstructible hcon hbot
  refine ⟨f, hf0, Set.disjoint_left.mpr fun p hp hpl => ?_⟩
  obtain ⟨q, hq, rfl⟩ := hfsub hp
  exact hh q (by simpa using hq) hpl

/-- Spreading out a failure over finite type subalgebras of a field: if every free finite type
subalgebra `E ⊆ K` containing `c` has a nonzero `h` with all fibres of `E` outside `D(h)` avoiding
`Z`, then `Z` misses a nonempty basic open of `Spec D`. -/
private theorem exists_ne_zero_disjoint_of_forall_free_subalgebra [Algebra.FiniteType D T]
    (K : Type u) [Field K] [Algebra D K] (hDK : Function.Injective (algebraMap D K))
    (c : Finset K) {Z : Set (PrimeSpectrum D)}
    (H : ∀ E : Subalgebra D K, Module.Free ↥E (↥E ⊗[D] T) → (∀ x ∈ c, x ∈ E) →
      Function.Injective (subalgebraTensorMap D T K E) →
      ∃ h : ↥E, h ≠ 0 ∧ ∀ q : PrimeSpectrum ↥E, h ∉ q.asIdeal →
        comap (algebraMap D ↥E) q ∉ Z) :
    ∃ f : D, f ≠ 0 ∧ Disjoint (basicOpen f : Set (PrimeSpectrum D)) Z := by
  obtain ⟨E, hft, hfree, hcE⟩ := exists_subalgebra_finiteType_free (T := T) K hDK c
  obtain ⟨h, hh0, hh⟩ := H E hfree hcE (subalgebraTensorMap_injective D T E)
  exact exists_ne_zero_disjoint_of_forall_not_mem_comap ↥E
    (injective_algebraMap_subalgebra D K hDK E) hh0 hh

/-- **The bad half of the generic-fibre dichotomy for geometric integrality, with the witness
field named.** Let `D` be a Noetherian domain and `T` a finite type `D`-algebra. If there is a
field `K` with `D → K` injective for which `T ⊗[D] K` is not a domain, then some nonempty basic
open of `Spec D` is disjoint from the geometrically integral fibre locus of `T`.

The failure in `K ⊗[D] T` is either the vanishing of that ring or a pair of nonzero elements with
product zero. In the second case the two elements are finite sums of pure tensors, and
`Algebra.exists_subalgebra_finiteType_free` provides a finite type `D`-subalgebra `E ⊆ K`
containing their left factors with `E ⊗[D] T` free over `E`. Freeness makes
`E ⊗[D] T → K ⊗[D] T` injective by `Algebra.subalgebraTensorMap_injective`, so the two elements
come from nonzero elements of `E ⊗[D] T` whose product is zero, and the spreading step
`Algebra.exists_ne_zero_forall_not_mem_geometricallyIntegralFibreLocus_of_free` followed by
`Algebra.exists_ne_zero_disjoint_of_forall_not_mem_comap` finishes. In the first case injectivity
makes `E ⊗[D] T` the zero ring and
`Algebra.forall_not_mem_geometricallyIntegralFibreLocus_of_subsingleton` applies to every prime
of `E`. -/
theorem exists_ne_zero_disjoint_geometricallyIntegralFibreLocus_of_not_isDomain
    [Algebra.FiniteType D T] (K : Type u) [Field K] [Algebra D K]
    (hDK : Function.Injective (algebraMap D K)) (hK : ¬ IsDomain (T ⊗[D] K)) :
    ∃ f : D, f ≠ 0 ∧ Disjoint (basicOpen f : Set (PrimeSpectrum D))
      (geometricallyIntegralFibreLocus D T) := by
  classical
  have hK' : ¬ IsDomain (K ⊗[D] T) := fun hdom =>
    hK ((TensorProduct.comm D T K).toRingEquiv.isDomain_iff.mpr hdom)
  -- the witnesses, and the finite set of elements of `K` they involve
  obtain ⟨c, hwit⟩ : ∃ c : Finset K, Subsingleton (K ⊗[D] T) ∨
      ∃ (x y : K ⊗[D] T) (s t : Finset (K × T)), x ≠ 0 ∧ y ≠ 0 ∧ x * y = 0 ∧
        x = ∑ i ∈ s, i.1 ⊗ₜ i.2 ∧ y = ∑ i ∈ t, i.1 ⊗ₜ i.2 ∧
        s.image Prod.fst ⊆ c ∧ t.image Prod.fst ⊆ c := by
    rcases subsingleton_or_nontrivial (K ⊗[D] T) with hsub | hnt
    · exact ⟨∅, Or.inl hsub⟩
    have hnzd : ¬ NoZeroDivisors (K ⊗[D] T) := fun hnzd =>
      hK' ((isDomain_iff_noZeroDivisors_and_nontrivial _).mpr ⟨hnzd, hnt⟩)
    obtain ⟨x, y, hxy, hx, hy⟩ : ∃ x y : K ⊗[D] T, x * y = 0 ∧ x ≠ 0 ∧ y ≠ 0 := by
      by_contra hc
      refine hnzd ⟨fun {x y} hxy => ?_⟩
      by_cases hx : x = 0
      · exact Or.inl hx
      · exact Or.inr (by by_contra hy; exact hc ⟨x, y, hxy, hx, hy⟩)
    obtain ⟨s, hs⟩ := TensorProduct.exists_finset x
    obtain ⟨t, ht⟩ := TensorProduct.exists_finset y
    exact ⟨s.image Prod.fst ∪ t.image Prod.fst, Or.inr
      ⟨x, y, s, t, hx, hy, hxy, hs, ht, Finset.subset_union_left, Finset.subset_union_right⟩⟩
  refine exists_ne_zero_disjoint_of_forall_free_subalgebra (T := T) K hDK c fun E _ hcE hinj => ?_
  rcases hwit with hsub | ⟨x, y, s, t, hx, hy, hxy, hxs, hyt, hsc, htc⟩
  · exact ⟨1, one_ne_zero, fun q _ =>
      forall_not_mem_geometricallyIntegralFibreLocus_of_subsingleton ↥E hinj.subsingleton q⟩
  obtain ⟨a, ha⟩ := mem_range_subalgebraTensorMap D T K
    (fun i hi => hcE _ (hsc (Finset.mem_image_of_mem _ hi))) hxs
  obtain ⟨b, hb⟩ := mem_range_subalgebraTensorMap D T K
    (fun i hi => hcE _ (htc (Finset.mem_image_of_mem _ hi))) hyt
  exact exists_ne_zero_forall_not_mem_geometricallyIntegralFibreLocus_of_free ↥E (a := a)
    (b := b) (fun h0 => hx (by rw [← ha, h0, map_zero]))
    (fun h0 => hy (by rw [← hb, h0, map_zero])) (hinj (by rw [map_mul, ha, hb, hxy, map_zero]))

/-- **The affine case of Stacks 0577 at the generic point, with the witness field named.** Let `D`
be a Noetherian domain and `T` a finite type `D`-algebra. If there is a field `K` with `D → K`
injective for which `T ⊗[D] K` is not reduced, then some nonempty basic open of `Spec D` is
disjoint from the geometrically reduced fibre locus of `T`.

The failure in `K ⊗[D] T` is a nonzero nilpotent element, which is a finite sum of pure tensors;
`Algebra.exists_subalgebra_finiteType_free` provides a finite type `D`-subalgebra `E ⊆ K`
containing its left factors with `E ⊗[D] T` free over `E`, freeness makes
`E ⊗[D] T → K ⊗[D] T` injective, so the element comes from a nonzero nilpotent of `E ⊗[D] T`, and
the spreading step
`Algebra.exists_ne_zero_forall_not_mem_geometricallyReducedFibreLocus_of_free` followed by
`Algebra.exists_ne_zero_disjoint_of_forall_not_mem_comap` finishes. -/
theorem exists_ne_zero_disjoint_geometricallyReducedFibreLocus_of_not_isReduced
    [Algebra.FiniteType D T] (K : Type u) [Field K] [Algebra D K]
    (hDK : Function.Injective (algebraMap D K)) (hK : ¬ IsReduced (T ⊗[D] K)) :
    ∃ f : D, f ≠ 0 ∧ Disjoint (basicOpen f : Set (PrimeSpectrum D))
      (geometricallyReducedFibreLocus D T) := by
  classical
  have hK' : ¬ IsReduced (K ⊗[D] T) := fun hred =>
    hK ((isReduced_congr (TensorProduct.comm D T K).toRingEquiv).mpr hred)
  obtain ⟨x, hnil, hx⟩ : ∃ x : K ⊗[D] T, IsNilpotent x ∧ x ≠ 0 := by
    by_contra hc
    exact hK' ⟨fun x hxnil => by by_contra hx0; exact hc ⟨x, hxnil, hx0⟩⟩
  obtain ⟨s, hs⟩ := TensorProduct.exists_finset x
  refine exists_ne_zero_disjoint_of_forall_free_subalgebra (T := T) K hDK (s.image Prod.fst)
    fun E _ hcE hinj => ?_
  obtain ⟨a, ha⟩ := mem_range_subalgebraTensorMap D T K
    (fun i hi => hcE _ (Finset.mem_image_of_mem _ hi)) hs
  obtain ⟨n, hn⟩ := hnil
  exact exists_ne_zero_forall_not_mem_geometricallyReducedFibreLocus_of_free ↥E
    (a := a) (fun h0 => hx (by rw [← ha, h0, map_zero]))
    ⟨n, hinj (by rw [map_pow, ha, hn, map_zero])⟩

/-- **The bad half of the generic-fibre dichotomy for geometric integrality.** Let `D` be a
Noetherian domain and `T` a finite type `D`-algebra. If the generic point of `Spec D` does not lie
in the geometrically integral fibre locus of `T`, then some nonempty basic open of `Spec D` is
disjoint from that locus.

The hypothesis names a field `K` with `ker (D → K) = (0)` whose fibre `T ⊗[D] K` is not a domain,
and `Algebra.exists_ne_zero_disjoint_geometricallyIntegralFibreLocus_of_not_isDomain` spreads that
failure out. -/
theorem exists_ne_zero_disjoint_geometricallyIntegralFibreLocus [Algebra.FiniteType D T]
    (hgen : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum D) ∉ geometricallyIntegralFibreLocus D T) :
    ∃ f : D, f ≠ 0 ∧ Disjoint (basicOpen f : Set (PrimeSpectrum D))
      (geometricallyIntegralFibreLocus D T) := by
  obtain ⟨K, hfield, halg, hker, hnd⟩ := (not_mem_geometricallyIntegralFibreLocus_iff _).mp hgen
  exact exists_ne_zero_disjoint_geometricallyIntegralFibreLocus_of_not_isDomain K
    ((RingHom.injective_iff_ker_eq_bot _).mpr hker) hnd

/-- **The affine case of Stacks 0577 at the generic point.** Let `D` be a Noetherian domain and
`T` a finite type `D`-algebra. If the generic point of `Spec D` does not lie in the geometrically
reduced fibre locus of `T`, then some nonempty basic open of `Spec D` is disjoint from that locus.

The hypothesis names a field `K` with `ker (D → K) = (0)` whose fibre `T ⊗[D] K` is not reduced,
and `Algebra.exists_ne_zero_disjoint_geometricallyReducedFibreLocus_of_not_isReduced` spreads that
failure out. -/
theorem exists_ne_zero_disjoint_geometricallyReducedFibreLocus [Algebra.FiniteType D T]
    (hgen : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum D) ∉ geometricallyReducedFibreLocus D T) :
    ∃ f : D, f ≠ 0 ∧ Disjoint (basicOpen f : Set (PrimeSpectrum D))
      (geometricallyReducedFibreLocus D T) := by
  obtain ⟨K, hfield, halg, hker, hnd⟩ := (not_mem_geometricallyReducedFibreLocus_iff _).mp hgen
  exact exists_ne_zero_disjoint_geometricallyReducedFibreLocus_of_not_isReduced K
    ((RingHom.injective_iff_ker_eq_bot _).mpr hker) hnd

/-- A good half and a bad half at the generic point give a nonempty basic open inside or missing
any set of primes. -/
private theorem exists_ne_zero_subset_or_disjoint {A : Type u} [CommRing A] [IsDomain A]
    {Z : Set (PrimeSpectrum A)}
    (hgood : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum A) ∈ Z →
      ∃ f : A, f ≠ 0 ∧ (basicOpen f : Set (PrimeSpectrum A)) ⊆ Z)
    (hbad : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum A) ∉ Z →
      ∃ f : A, f ≠ 0 ∧ Disjoint (basicOpen f : Set (PrimeSpectrum A)) Z) :
    ∃ f : A, f ≠ 0 ∧
      ((basicOpen f : Set (PrimeSpectrum A)) ⊆ Z ∨
        Disjoint (basicOpen f : Set (PrimeSpectrum A)) Z) := by
  by_cases hgen : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum A) ∈ Z
  · obtain ⟨f, hf0, hf⟩ := hgood hgen
    exact ⟨f, hf0, Or.inl hf⟩
  · obtain ⟨f, hf0, hf⟩ := hbad hgen
    exact ⟨f, hf0, Or.inr hf⟩

/-- **The generic-fibre dichotomy of Stacks 05FT from its good half alone.** Suppose that over
every Noetherian domain `D` and finite type `D`-algebra `T` whose *generic* fibre is geometrically
integral some nonempty basic open of `Spec D` is contained in the geometrically integral fibre
locus. Then over every Noetherian domain and finite type algebra some nonempty basic open either
lies in or misses the locus.

If the generic point lies in the locus this is the hypothesis; if it does not, it is
`Algebra.exists_ne_zero_disjoint_geometricallyIntegralFibreLocus`. No other case can occur, and no
other input is needed: the bad half of the dichotomy is proved. -/
theorem exists_basicOpen_geometricallyIntegral_of_goodGeneric
    (hgood : ∀ (D T : Type u) [CommRing D] [IsDomain D] [IsNoetherianRing D] [CommRing T]
      [Algebra D T] [Algebra.FiniteType D T],
      (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum D) ∈ geometricallyIntegralFibreLocus D T →
        ∃ f : D, f ≠ 0 ∧ (basicOpen f : Set (PrimeSpectrum D)) ⊆
          geometricallyIntegralFibreLocus D T)
    (D T : Type u) [CommRing D] [IsDomain D] [IsNoetherianRing D] [CommRing T] [Algebra D T]
    [Algebra.FiniteType D T] :
    ∃ f : D, f ≠ 0 ∧
      ((basicOpen f : Set (PrimeSpectrum D)) ⊆ geometricallyIntegralFibreLocus D T ∨
        Disjoint (basicOpen f : Set (PrimeSpectrum D)) (geometricallyIntegralFibreLocus D T)) := by
  exact exists_ne_zero_subset_or_disjoint (hgood D T)
    exists_ne_zero_disjoint_geometricallyIntegralFibreLocus

/-- **Stacks 05FT granted only the good half of the generic-fibre dichotomy.** Let `R → S` be flat
of finite presentation and suppose `S ⊗[R] κ(p)` is geometrically integral over `κ(p)` for every
prime `p` of `R`. Then `S` is a projective `R`-module, provided that over every Noetherian domain
`D` and finite type `D`-algebra `T` *whose generic fibre is geometrically integral* some nonempty
basic open of `Spec D` lies in the geometrically integral fibre locus of `T`.

This is `Algebra.projective_of_geometricallyIntegral_fibres_of_spreadOut` with its hypothesis
weakened to that one half, by `Algebra.exists_basicOpen_geometricallyIntegral_of_goodGeneric`. See
`Algebra.projective_of_geometricallyIntegral_fibres_of_good_halves` for the form in which the
remaining hypothesis is split into the affine cases of Stacks 0578 and Stacks 055A. -/
theorem projective_of_geometricallyIntegral_fibres_of_goodGeneric
    (hgood : ∀ (D T : Type u) [CommRing D] [IsDomain D] [IsNoetherianRing D] [CommRing T]
      [Algebra D T] [Algebra.FiniteType D T],
      (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum D) ∈ geometricallyIntegralFibreLocus D T →
        ∃ f : D, f ≠ 0 ∧ (basicOpen f : Set (PrimeSpectrum D)) ⊆
          geometricallyIntegralFibreLocus D T)
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S] [Module.Flat R S]
    (h : ∀ (p : Ideal R) [p.IsPrime],
      letI : Algebra p.ResidueField (S ⊗[R] p.ResidueField) :=
        Algebra.TensorProduct.rightAlgebra
      Algebra.IsGeometricallyIntegral p.ResidueField (S ⊗[R] p.ResidueField)) :
    Module.Projective R S :=
  projective_of_geometricallyIntegral_fibres_of_spreadOut
    (fun D T _ _ _ _ _ _ => exists_basicOpen_geometricallyIntegral_of_goodGeneric hgood D T) h

/-- **The affine case of Stacks 0579 from the good half of Stacks 0577.** Over a Noetherian ring
`A` the geometrically reduced fibre locus of a finite type algebra `C` is constructible, granted
only that over a Noetherian domain whose generic fibre is geometrically reduced some nonempty
basic open lies in the geometrically reduced fibre locus.

This is `Algebra.isConstructible_geometricallyReducedFibreLocus` with its dichotomy hypothesis
supplied by the hypothesis here together with
`Algebra.exists_ne_zero_disjoint_geometricallyReducedFibreLocus`. -/
theorem isConstructible_geometricallyReducedFibreLocus_of_goodGeneric
    (hgood : ∀ (D T : Type u) [CommRing D] [IsDomain D] [IsNoetherianRing D] [CommRing T]
      [Algebra D T] [Algebra.FiniteType D T],
      (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum D) ∈ geometricallyReducedFibreLocus D T →
        ∃ f : D, f ≠ 0 ∧ (basicOpen f : Set (PrimeSpectrum D)) ⊆
          geometricallyReducedFibreLocus D T)
    (A C : Type u) [CommRing A] [IsNoetherianRing A] [CommRing C] [Algebra A C]
    [Algebra.FiniteType A C] :
    IsConstructible (geometricallyReducedFibreLocus A C) := by
  refine isConstructible_geometricallyReducedFibreLocus (fun D T _ _ _ _ _ _ => ?_) A C
  exact exists_ne_zero_subset_or_disjoint (hgood D T)
    exists_ne_zero_disjoint_geometricallyReducedFibreLocus

end Algebra

namespace Algebra

variable {D T : Type u} [CommRing D] [IsDomain D] [CommRing T] [Algebra D T]

/-- **The good half for geometric integrality from the good halves for its two factors.** If the
generic fibre of `T` is geometrically integral and, separately, a good generic fibre forces a
nonempty basic open inside the geometrically reduced locus and inside the geometrically
irreducible locus, then a nonempty basic open lies inside the geometrically integral locus.

By Stacks 05DY, `Algebra.geometricallyIntegralFibreLocus_eq_inter`, the integral locus is the
intersection of the other two, so the generic point lies in both; the two hypotheses then give
`D(f)` inside the reduced locus and `D(g)` inside the irreducible locus, and `D(f ⬝ g)`, the
intersection of the two, lies in both. -/
theorem exists_basicOpen_subset_geometricallyIntegralFibreLocus_of_good_halves
    (hred : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum D) ∈ geometricallyReducedFibreLocus D T →
      ∃ f : D, f ≠ 0 ∧ (basicOpen f : Set (PrimeSpectrum D)) ⊆
        geometricallyReducedFibreLocus D T)
    (hirr : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum D) ∈
        geometricallyIrreducibleFibreLocus D T →
      ∃ g : D, g ≠ 0 ∧ (basicOpen g : Set (PrimeSpectrum D)) ⊆
        geometricallyIrreducibleFibreLocus D T)
    (hgen : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum D) ∈ geometricallyIntegralFibreLocus D T) :
    ∃ f : D, f ≠ 0 ∧ (basicOpen f : Set (PrimeSpectrum D)) ⊆
      geometricallyIntegralFibreLocus D T := by
  rw [geometricallyIntegralFibreLocus_eq_inter] at hgen ⊢
  obtain ⟨f, hf0, hf⟩ := hred hgen.2
  obtain ⟨g, hg0, hg⟩ := hirr hgen.1
  refine ⟨f * g, mul_ne_zero hf0 hg0, fun p hp => ?_⟩
  rw [SetLike.mem_coe, mem_basicOpen] at hp
  exact ⟨hg (mem_basicOpen g p |>.mpr fun hgp => hp (p.asIdeal.mul_mem_left f hgp)),
    hf (mem_basicOpen f p |>.mpr fun hfp => hp (p.asIdeal.mul_mem_right g hfp))⟩

/-- **Stacks 05FT granted only the affine cases of Stacks 0578 and Stacks 055A at the generic
point.** Let `R → S` be flat of finite presentation and suppose `S ⊗[R] κ(p)` is geometrically
integral over `κ(p)` for every prime `p` of `R`. Then `S` is a projective `R`-module, provided
that over every Noetherian domain `D` and finite type `D`-algebra `T`:

* if the generic fibre of `T` is geometrically reduced then some nonempty basic open of `Spec D`
  lies in the geometrically reduced fibre locus (the affine case of Stacks 0578), and
* if the generic fibre of `T` is geometrically irreducible then some nonempty basic open of
  `Spec D` lies in the geometrically irreducible fibre locus (the affine case of Stacks 055A).

Those two statements are all that is missing. The bad halves — the generic fibre failing the
property forces a nonempty basic open where every fibre fails it — are proved in
`Algebra.exists_ne_zero_disjoint_geometricallyIntegralFibreLocus`, and everything above the
dichotomy (the criterion of Stacks 053Z, the reduction to an integral base, the limit argument of
Stacks 05F4 and the Noetherian case of Stacks 05FS) is already in the library. -/
theorem projective_of_geometricallyIntegral_fibres_of_good_halves
    (hred : ∀ (D T : Type u) [CommRing D] [IsDomain D] [IsNoetherianRing D] [CommRing T]
      [Algebra D T] [Algebra.FiniteType D T],
      (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum D) ∈ geometricallyReducedFibreLocus D T →
        ∃ f : D, f ≠ 0 ∧ (basicOpen f : Set (PrimeSpectrum D)) ⊆
          geometricallyReducedFibreLocus D T)
    (hirr : ∀ (D T : Type u) [CommRing D] [IsDomain D] [IsNoetherianRing D] [CommRing T]
      [Algebra D T] [Algebra.FiniteType D T],
      (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum D) ∈ geometricallyIrreducibleFibreLocus D T →
        ∃ f : D, f ≠ 0 ∧ (basicOpen f : Set (PrimeSpectrum D)) ⊆
          geometricallyIrreducibleFibreLocus D T)
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S] [Module.Flat R S]
    (h : ∀ (p : Ideal R) [p.IsPrime],
      letI : Algebra p.ResidueField (S ⊗[R] p.ResidueField) :=
        Algebra.TensorProduct.rightAlgebra
      Algebra.IsGeometricallyIntegral p.ResidueField (S ⊗[R] p.ResidueField)) :
    Module.Projective R S :=
  projective_of_geometricallyIntegral_fibres_of_spreadOut
    (fun D T _ _ _ _ _ _ => exists_basicOpen_geometricallyIntegral_of_goodGeneric
      (fun D T _ _ _ _ _ _ => exists_basicOpen_subset_geometricallyIntegralFibreLocus_of_good_halves
        (hred D T) (hirr D T)) D T) h

end Algebra

end
