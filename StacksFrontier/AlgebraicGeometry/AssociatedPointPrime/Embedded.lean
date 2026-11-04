module

public import StacksFrontier.AlgebraicGeometry.AssociatedPointPrime.Basic

/-!
# No embedded points, read on an affine open

The absence of embedded points is a condition on the specialization order between the associated
points of a sheaf of modules (Stacks Tag 05AK). This file reads that condition on an affine open
`U` of a locally Noetherian scheme: it says exactly that no associated prime of `Γ(F, U)` is
properly contained in another.

## Main results

* `specializes_iff_primeIdealOf_le`: for two points of an affine open `U`, one specializes to the
  other exactly when the corresponding primes of `Γ(X, U)` are nested. This is the dictionary
  entry translating the topology of `U` into the order on `Spec Γ(X, U)`.
* `isAssociatedPoint_iff_mem_associatedPrimes_of_primeIdealOf`: the bridge of
  `AssociatedPointPrime.Basic` with the prime of the point named, which is the form in which a
  point produced from a prime is fed to it.
* `eq_of_le_of_mem_associatedPrimes`: if a quasi-coherent module has no embedded associated
  points, then its associated primes over an affine open are pairwise incomparable, i.e. each is
  minimal among them.
* `eq_of_le_of_mem_associatedPrimes_of_hasNoEmbeddedPoints`: the structure-sheaf case, the form in
  which Tag 0BXL's "no embedded points" hypothesis is used.

## Route

A point of an affine open `U` specializes to another exactly when their primes are nested: the
open immersion `Spec Γ(X, U) ⟶ X` of `IsAffineOpen.fromSpec` is inducing, so it reflects
specialization, and on `Spec` of a ring specialization is inclusion of primes
(`PrimeSpectrum.le_iff_specializes`). Combining this with the bridge
`isAssociatedPoint_iff_mem_associatedPrimes` of `AssociatedPointPrime.Basic` turns "no associated
point is a proper specialization of another associated point" into "no associated prime of
`Γ(F, U)` is properly contained in another", because every prime of `Γ(X, U)` is the prime of a
point of `U` (`IsAffineOpen.isoSpec`).

## Implementation notes

The conclusion is minimality *among the associated primes*, not minimality over an ideal. Passing
to `Ideal.minimalPrimes`, which is what the engine of Tag 0BXL consumes, additionally needs that
the minimal primes of an ideal `I` of a Noetherian ring are exactly the minimal members of
`associatedPrimes R (R ⧸ I)`; that is not proved here.

## References

* [Stacks Project, Tag 05AK](https://stacks.math.columbia.edu/tag/05AK)
* [Stacks Project, Tag 0BXL](https://stacks.math.columbia.edu/tag/0BXL)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Stacks.AlgebraicGeometry.AssociatedPointsMono

universe u

namespace Stacks.AlgebraicGeometry.AssociatedPointPrime

variable {X : Scheme.{u}}

/-- **The specialization order on an affine open is the order on primes.** For two points of an
affine open `U`, the first specializes to the second exactly when the prime of the first is
contained in the prime of the second. -/
theorem specializes_iff_primeIdealOf_le {U : X.Opens} (hU : IsAffineOpen U) (y z : U) :
    (y : X) ⤳ (z : X) ↔ (hU.primeIdealOf y).asIdeal ≤ (hU.primeIdealOf z).asIdeal := by
  have hind : Topology.IsInducing hU.fromSpec.base := hU.fromSpec.isOpenEmbedding.isInducing
  have h1 : hU.fromSpec (hU.primeIdealOf y) ⤳ hU.fromSpec (hU.primeIdealOf z)
      ↔ hU.primeIdealOf y ⤳ hU.primeIdealOf z := hind.specializes_iff
  rw [hU.fromSpec_primeIdealOf y, hU.fromSpec_primeIdealOf z] at h1
  rw [h1, ← PrimeSpectrum.le_iff_specializes, PrimeSpectrum.asIdeal_le_asIdeal]

/-- A point of an affine open whose prime is `q` is an associated point of a quasi-coherent
module exactly when `q` is an associated prime of the sections over the open. This is the bridge
of `AssociatedPointPrime.Basic` with the prime named. -/
theorem isAssociatedPoint_iff_mem_associatedPrimes_of_primeIdealOf [IsLocallyNoetherian X]
    (F : X.Modules) [F.IsQuasicoherent] {U : X.Opens} (hU : IsAffineOpen U) (u : U)
    {q : Ideal Γ(X, U)} (hu : (hU.primeIdealOf u).asIdeal = q) :
    IsAssociatedPoint F (u : X) ↔ q ∈ associatedPrimes Γ(X, U) Γ(F, U) := by
  have hu' : (hU.primeIdealOf ⟨(u : X), u.2⟩).asIdeal = q := hu
  rw [isAssociatedPoint_iff_mem_associatedPrimes F hU u.2, hu']

/-- **No embedded associated points, read on an affine open.** If a quasi-coherent module on a
locally Noetherian scheme has no embedded associated points, then no associated prime of its
sections over an affine open is properly contained in another: each is minimal among them. -/
theorem eq_of_le_of_mem_associatedPrimes [IsLocallyNoetherian X] (F : X.Modules)
    [F.IsQuasicoherent] (hF : EmbeddedPoints.HasNoEmbeddedAssociatedPoints F) {U : X.Opens}
    (hU : IsAffineOpen U) {p q : Ideal Γ(X, U)} (hp : p ∈ associatedPrimes Γ(X, U) Γ(F, U))
    (hq : q ∈ associatedPrimes Γ(X, U) Γ(F, U)) (hle : q ≤ p) :
    q = p := by
  have key : ∀ r ∈ associatedPrimes Γ(X, U) Γ(F, U), ∃ y : U,
      (hU.primeIdealOf y).asIdeal = r ∧ IsAssociatedPoint F (y : X) := fun r hr =>
    have h := congrArg PrimeSpectrum.asIdeal (primeIdealOf_isoSpec_inv hU ⟨r, hr.1⟩)
    ⟨_, h, (isAssociatedPoint_iff_mem_associatedPrimes_of_primeIdealOf F hU _ h).mpr hr⟩
  obtain ⟨yp, hep, hap⟩ := key p hp
  obtain ⟨yq, heq, haq⟩ := key q hq
  have hspec : (yq : X) ⤳ (yp : X) := by
    rw [specializes_iff_primeIdealOf_le hU yq yp, heq, hep]
    exact hle
  have hpts : (yq : X) = (yp : X) := by
    by_contra hne
    exact hF (yp : X) ⟨hap, (yq : X), haq, hspec, hne⟩
  rw [← heq, ← hep]
  exact congrArg (fun w : U => (hU.primeIdealOf w).asIdeal) (Subtype.ext hpts)

/-- **The structure-sheaf case.** On a locally Noetherian scheme with no embedded points, no
associated prime of the ring of functions on an affine open is properly contained in another.

The structure sheaf is passed as a module `F` together with the hypothesis that it *is* the unit
module, because neither its quasi-coherence nor the module structure on its sections is found by
instance search; see `isSchemeAssociatedPoint_iff_mem_associatedPrimes`. -/
theorem eq_of_le_of_mem_associatedPrimes_of_hasNoEmbeddedPoints [IsLocallyNoetherian X]
    (F : X.Modules) [F.IsQuasicoherent] (hFu : F = SheafOfModules.unit X.ringCatSheaf)
    (hF : EmbeddedPoints.HasNoEmbeddedPoints X) {U : X.Opens} (hU : IsAffineOpen U)
    {p q : Ideal Γ(X, U)} (hp : p ∈ associatedPrimes Γ(X, U) Γ(F, U))
    (hq : q ∈ associatedPrimes Γ(X, U) Γ(F, U)) (hle : q ≤ p) :
    q = p := by
  subst hFu
  exact eq_of_le_of_mem_associatedPrimes _ hF hU hp hq hle

end Stacks.AlgebraicGeometry.AssociatedPointPrime

end
