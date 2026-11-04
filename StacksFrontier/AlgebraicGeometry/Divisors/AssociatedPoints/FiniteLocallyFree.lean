module

public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Finiteness
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.StructureSheafStalk
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Sheaf
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.CodimensionOneObstruction.AssociatedPointTransfer
public import StacksFrontier.AlgebraicGeometry.StalkFreeBridge.StalkFree
public import StacksFrontier.RingTheory.LocalCohomology.LowDegree

/-!
# Associated points of a finite locally free module

Let `X` be a scheme and let `ℰ` be a finite locally free `𝒪_X`-module. Every associated point of
`ℰ` is an associated point of `X`: `Ass(ℰ) ⊆ Ass(𝒪_X)`. When `X` is an open subscheme of the
spectrum of a Noetherian ring `A`, the associated points of `X` are the points whose prime is an
associated prime of `A`, so every associated point of `ℰ` has an associated prime of `A` for its
prime.

The second statement is the input by which Stacks 0EKU passes from its hypothesis, which refers
only to the associated primes of `A`, to the hypothesis of Stacks 0EIV on the associated points
of a finite locally free module on an open `V ⊆ Spec(A) ∖ V(𝔞)`.

## Main results

* `Stacks.Divisors.IsAssociatedPrimeStacks.of_free` — a prime associated to a free module is
  associated to the ring.
* `Stacks.Divisors.mem_schemeAssociatedPoints_of_isAssociatedPoint_of_free` — an associated point
  of a module whose stalk there is free is an associated point of the scheme.
* `Stacks.Divisors.associatedPoints_subset_schemeAssociatedPoints_of_isFiniteLocallyFree` —
  `Ass(ℰ) ⊆ Ass(X)` for a finite locally free `ℰ`.
* `Stacks.Divisors.isAssociatedPrimeStacks_of_mem_schemeAssociatedPoints` — for an open
  immersion `j : X ⟶ Spec(A)` with `A` Noetherian, the prime of `j x` is an associated prime of
  `A` for every associated point `x` of `X`.
* `Stacks.Divisors.isAssociatedPrimeStacks_of_mem_associatedPoints_complementZeroLocus` — the
  statement for a finite locally free module on `Spec(A) ∖ V(𝔞)`.

## Implementation notes

The first result is proved for an arbitrary prime: if `p` is the annihilator of `v` in a free
module, then `p` is the intersection of the annihilators of the finitely many nonzero coordinates
of `v`, each of which contains `p`; a prime containing a finite intersection of ideals contains one
of them (`Ideal.IsPrime.inf_le'`), which is then equal to `p`. No Noetherian hypothesis is needed.

## References

* [Stacks Project, Tag 02OJ](https://stacks.math.columbia.edu/tag/02OJ)
* [Stacks Project, Tag 0EKU](https://stacks.math.columbia.edu/tag/0EKU)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Stacks.LocalCohomology
open Stacks.AlgebraicGeometry.CodimensionOneObstruction (isAssociatedPrimeStacks_map_ringEquiv)
open Module.associatedPrimes
  (preimage_comap_associatedPrimes_eq_associatedPrimes_of_isLocalizedModule)

universe u

namespace Stacks.Divisors

/-- **A prime associated to a free module is associated to the ring.** If `p` is the annihilator
of an element `v` of a free `R`-module, then `p` is the annihilator of one of the coordinates of
`v`. -/
theorem IsAssociatedPrimeStacks.of_free {R N : Type*} [CommRing R] [AddCommGroup N] [Module R N]
    [Module.Free R N] {p : Ideal R} (h : IsAssociatedPrimeStacks R N p) :
    IsAssociatedPrimeStacks R R p := by
  classical
  obtain ⟨hp, v, hv⟩ := h
  set c := (Module.Free.chooseBasis R N).repr v
  have hmem : ∀ r : R, r ∈ p ↔ ∀ i ∈ c.support, r * c i = 0 := by
    intro r
    rw [← hv, Submodule.mem_colon_span_singleton, Submodule.mem_bot,
      ← (Module.Free.chooseBasis R N).repr.injective.eq_iff, map_smul, map_zero]
    refine ⟨fun h i _ => by simpa using DFunLike.congr_fun h i, fun h => ?_⟩
    ext i
    by_cases hi : i ∈ c.support
    · simpa using h i hi
    · rw [Finsupp.smul_apply, Finsupp.notMem_support_iff.mp hi, smul_zero, Finsupp.zero_apply]
  let J : _ → Ideal R := fun i => (⊥ : Submodule R R).colon (Submodule.span R {c i})
  have hJ : ∀ i (r : R), r ∈ J i ↔ r * c i = 0 := fun i r => by
    simp [J, Submodule.mem_colon_span_singleton]
  have hinf : c.support.inf J ≤ p := fun r hr => by
    rw [Submodule.mem_finsetInf] at hr
    exact (hmem r).2 fun i hi => (hJ i r).1 (hr i hi)
  obtain ⟨i, hi, hle⟩ := hp.inf_le'.1 hinf
  exact ⟨hp, c i, le_antisymm hle fun r hr => (hJ i r).2 ((hmem r).1 hr i hi)⟩

/-- **Associated primes are invariant under linear equivalence.** -/
private theorem IsAssociatedPrimeStacks.of_linearEquiv {R M N : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) {p : Ideal R}
    (h : IsAssociatedPrimeStacks R M p) : IsAssociatedPrimeStacks R N p := by
  obtain ⟨hp, m, hm⟩ := h
  refine ⟨hp, e m, ?_⟩
  rw [← hm]
  ext r
  simp only [Submodule.mem_colon_span_singleton, Submodule.mem_bot, ← LinearEquiv.map_smul,
    LinearEquiv.map_eq_zero_iff]

/-- **An associated point at which the stalk is free is an associated point of the scheme.** The
maximal ideal of `𝒪_{X, x}` is associated to the free `𝒪_{X, x}`-module `F_x`, hence to
`𝒪_{X, x}` itself, which is the stalk of the structure sheaf. -/
theorem mem_schemeAssociatedPoints_of_isAssociatedPoint_of_free {X : Scheme.{u}}
    {F : X.Modules} {x : X}
    [Module.Free (X.presheaf.stalk x) (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x)]
    (h : IsAssociatedPoint F x) : x ∈ schemeAssociatedPoints X :=
  IsAssociatedPrimeStacks.of_linearEquiv (structureSheafStalkLinearEquiv X x).symm
    (IsAssociatedPrimeStacks.of_free h)

/-- **The associated points of a finite locally free module are associated points of the
scheme**: `Ass(ℰ) ⊆ Ass(X)`. The stalks of `ℰ` are free over the local rings. -/
theorem associatedPoints_subset_schemeAssociatedPoints_of_isFiniteLocallyFree {X : Scheme.{u}}
    (F : X.Modules) (hF : Scheme.Modules.IsFiniteLocallyFree F) :
    associatedPoints F ⊆ schemeAssociatedPoints X := by
  intro x hx
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F :=
    (Scheme.Modules.isFiniteLocallyFree_iff F).1 hF
  have : Module.Free (X.presheaf.stalk x)
      (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x) :=
    (Stacks.StalkFreeBridge.freeAndFinite_stalk_of_isFiniteLocallyFree F x).1
  exact mem_schemeAssociatedPoints_of_isAssociatedPoint_of_free hx

/-- **On an open subscheme of the spectrum of a Noetherian ring, associated points are associated
primes.** For an open immersion `j : X ⟶ Spec(A)` with `A` Noetherian and an associated point
`x` of `X`, the prime of `j x` is an associated prime of `A`: the local ring `𝒪_{X, x}` is
`A_𝔭` for that prime `𝔭`, and over a Noetherian ring `𝔭 A_𝔭 ∈ Ass(A_𝔭)` exactly when
`𝔭 ∈ Ass(A)`. -/
theorem isAssociatedPrimeStacks_of_mem_schemeAssociatedPoints {A : Type u} [CommRing A]
    [IsNoetherianRing A] {X : Scheme.{u}} (j : X ⟶ Spec (CommRingCat.of A)) [IsOpenImmersion j]
    {x : X} (hx : x ∈ schemeAssociatedPoints X) :
    IsAssociatedPrimeStacks A A (j.base x).asIdeal := by
  generalize hy : j.base x = y
  have : y.asIdeal.IsPrime := y.isPrime
  let e : X.presheaf.stalk x ≃+* Localization.AtPrime y.asIdeal :=
    ((asIso (j.stalkMap x)).symm ≪≫ eqToIso (by rw [hy]) ≪≫
      Spec.stalkIso (CommRingCat.of A) y).commRingCatIsoToRingEquiv
  have h₁ := isAssociatedPrimeStacks_map_ringEquiv e
    (IsAssociatedPrimeStacks.of_linearEquiv (structureSheafStalkLinearEquiv X x) hx)
  have hmax : Ideal.map e.toRingHom (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) =
      IsLocalRing.maximalIdeal (Localization.AtPrime y.asIdeal) :=
    IsLocalRing.map_ringEquiv_maximalIdeal e
  rw [hmax] at h₁
  rw [isAssociatedPrimeStacks_iff_mem_associatedPrimes] at h₁ ⊢
  have hp : (IsLocalRing.maximalIdeal (Localization.AtPrime y.asIdeal)).comap
      (algebraMap A (Localization.AtPrime y.asIdeal)) = y.asIdeal := by
    ext r
    exact IsLocalization.AtPrime.to_map_mem_maximal_iff
      (Localization.AtPrime y.asIdeal) y.asIdeal r
  rw [← preimage_comap_associatedPrimes_eq_associatedPrimes_of_isLocalizedModule
    y.asIdeal.primeCompl (Localization.AtPrime y.asIdeal)
    (Algebra.linearMap A (Localization.AtPrime y.asIdeal)), Set.mem_preimage] at h₁
  rwa [← hp]

/-- **The associated points of a finite locally free module on `Spec(A) ∖ V(𝔞)` have associated
primes of `A` for their primes**, for `A` Noetherian. This is the input by which Stacks 0EKU
reduces its hypothesis on the associated primes of `A` to the hypothesis of Stacks 0EIV on the
associated points of a finite locally free module. -/
theorem isAssociatedPrimeStacks_of_mem_associatedPoints_complementZeroLocus (A : Type u)
    [CommRing A] [IsNoetherianRing A] (a : Ideal A)
    (F : (complementZeroLocus A a : Scheme).Modules)
    (hF : Scheme.Modules.IsFiniteLocallyFree F) {x : complementZeroLocus A a}
    (hx : x ∈ associatedPoints F) : IsAssociatedPrimeStacks A A x.1.asIdeal :=
  isAssociatedPrimeStacks_of_mem_schemeAssociatedPoints (complementZeroLocus A a).ι
    (associatedPoints_subset_schemeAssociatedPoints_of_isFiniteLocallyFree F hF hx)

end Stacks.Divisors

end
