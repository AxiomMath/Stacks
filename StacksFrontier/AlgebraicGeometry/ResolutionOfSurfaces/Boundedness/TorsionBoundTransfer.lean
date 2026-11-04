module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.ModificationATorsion
public import StacksFrontier.RingTheory.Length.TorsionBy

/-!
# Transferring a uniform bound on torsion in the first cohomology

Let `A` be a commutative ring and let `a` divide a power `cⁿ` of an element `c`. Then a bound on
the lengths of the `c`-torsion submodules of `H¹(X, 𝒪_X)`, uniform over the normal modifications
`X → Spec A`, gives one on the lengths of the `a`-torsion submodules. Through the identification
of the `a`-torsion with the cokernel of `A → H⁰(Z, 𝒪_Z)` for `Z ⊂ X` cut out by `a`, the same
transfer holds for those cokernels.

## Main results

* `AlgebraicGeometry.exists_bound_length_torsionBy_firstCohomology_of_dvd_pow`: the transfer of a
  uniform bound from `c` to a divisor of a power of `c`.
* `AlgebraicGeometry.exists_bound_length_quotient_baseToZeroSchemeSections_of_dvd_pow`: the same
  transfer for the cokernels of `A → H⁰(Z, 𝒪_Z)`.
* `AlgebraicGeometry.exists_bound_length_torsionBy_firstCohomology_of_isReduced_quotient`: the
  transfer applied to an element whose principal quotient is reduced.

## Implementation notes

The bound is transferred by `Module.length_torsionBy_le_of_dvd_pow`, and translated between the
torsion submodules and the cokernels by `length_quotient_baseToZeroSchemeSections_eq`, which asks
that the element be nonzero.

The last statement takes the existence of a nonzero `c` with `A ⧸ cA` reduced and `a ∣ cⁿ` as a
hypothesis. The corresponding result [Stacks, Tag 0AXI] for a Noetherian normal local domain of
dimension two concludes only with `A ⧸ cA` reduced and `a ∣ cⁿ`, which `c = 0` already satisfies,
so it does not by itself supply the nonzero `c` that the translation to cokernels needs.

## References

* [Stacks Project, Tag 0AXJ](https://stacks.math.columbia.edu/tag/0AXJ)
* [Stacks Project, Tag 0AXK](https://stacks.math.columbia.edu/tag/0AXK)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {A : Type u} [CommRing A] [IsDomain A]

/-- If `a` divides `cⁿ`, a bound on the lengths of the `c`-torsion submodules of `H¹(X, 𝒪_X)`
uniform over the normal modifications `X → Spec A` gives one on the lengths of the `a`-torsion
submodules. -/
theorem exists_bound_length_torsionBy_firstCohomology_of_dvd_pow {a c : A} {n : ℕ}
    (hac : a ∣ c ^ n)
    (h : ∃ N : ℕ, ∀ (X : Scheme.{u}) [IsNormal X] (f : X ⟶ Spec (.of A)), IsModification f →
      Module.length A ↥(Submodule.torsionBy A (firstCohomologyAsBaseModule X f) c) ≤ N) :
    ∃ N : ℕ, ∀ (X : Scheme.{u}) [IsNormal X] (f : X ⟶ Spec (.of A)), IsModification f →
      Module.length A ↥(Submodule.torsionBy A (firstCohomologyAsBaseModule X f) a) ≤ N := by
  obtain ⟨N, hN⟩ := h
  refine ⟨n * N, fun X _ f hf => ?_⟩
  refine (Module.length_torsionBy_le_of_dvd_pow A _ hac).trans ?_
  rw [Nat.cast_mul]
  gcongr
  exact hN X f hf

/-- If `a` and `c` are nonzero and `a` divides `cⁿ`, a bound on the lengths of the cokernels of
`A → H⁰(Z, 𝒪_Z)` for `Z ⊂ X` cut out by `c`, uniform over the normal modifications
`X → Spec A`, gives one on the lengths of those cokernels for `Z` cut out by `a`. -/
theorem exists_bound_length_quotient_baseToZeroSchemeSections_of_dvd_pow [IsNormalDomain A]
    {a c : A} (ha : a ≠ 0) (hc : c ≠ 0) {n : ℕ} (hac : a ∣ c ^ n)
    (h : ∃ N : ℕ, ∀ (X : Scheme.{u}) [IsNormal X] (f : X ⟶ Spec (.of A)), IsModification f →
      Module.length A (globalSectionsAsBaseModule X f (zeroSchemeStructureSheaf X f c) ⧸
        LinearMap.range (baseToZeroSchemeSections X f c)) ≤ N) :
    ∃ N : ℕ, ∀ (X : Scheme.{u}) [IsNormal X] (f : X ⟶ Spec (.of A)), IsModification f →
      Module.length A (globalSectionsAsBaseModule X f (zeroSchemeStructureSheaf X f a) ⧸
        LinearMap.range (baseToZeroSchemeSections X f a)) ≤ N := by
  obtain ⟨N, hN⟩ := h
  obtain ⟨M, hM⟩ := exists_bound_length_torsionBy_firstCohomology_of_dvd_pow hac
    ⟨N, fun X _ f hf => by
      rw [← length_quotient_baseToZeroSchemeSections_eq X f hf hc]
      exact hN X f hf⟩
  refine ⟨M, fun X _ f hf => ?_⟩
  rw [length_quotient_baseToZeroSchemeSections_eq X f hf ha]
  exact hM X f hf

/-- A bound on the lengths of the `c`-torsion submodules of `H¹(X, 𝒪_X)` for every nonzero `c`
with `A ⧸ cA` reduced, uniform over the normal modifications `X → Spec A`, gives one for every
element dividing a power of such a `c`. -/
theorem exists_bound_length_torsionBy_firstCohomology_of_isReduced_quotient {a : A}
    (hred : ∀ c : A, c ≠ 0 → _root_.IsReduced (A ⧸ Ideal.span {c}) →
      ∃ N : ℕ, ∀ (X : Scheme.{u}) [IsNormal X] (f : X ⟶ Spec (.of A)), IsModification f →
        Module.length A ↥(Submodule.torsionBy A (firstCohomologyAsBaseModule X f) c) ≤ N)
    (hc : ∃ c : A, c ≠ 0 ∧ _root_.IsReduced (A ⧸ Ideal.span {c}) ∧ ∃ n : ℕ, a ∣ c ^ n) :
    ∃ N : ℕ, ∀ (X : Scheme.{u}) [IsNormal X] (f : X ⟶ Spec (.of A)), IsModification f →
      Module.length A ↥(Submodule.torsionBy A (firstCohomologyAsBaseModule X f) a) ≤ N := by
  obtain ⟨c, hc0, hcred, n, hac⟩ := hc
  exact exists_bound_length_torsionBy_firstCohomology_of_dvd_pow hac (hred c hc0 hcred)

end AlgebraicGeometry

end
