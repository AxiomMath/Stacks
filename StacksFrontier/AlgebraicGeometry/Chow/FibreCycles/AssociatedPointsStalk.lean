module

public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.CoefficientColength
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.StructureSheafStalk

/-!
# The associated-point hypothesis of the local multiplicity comparison

The local comparison of multiplicities underlying Stacks Tag 02S5,
`Stacks.Chow.length_quotient_span_sup_eq_sum_minimalPrimes_of_notMem_associatedPrimes`, carries a
hypothesis on the local ring `A = 𝒪_{X, ξ}` of the ambient scheme: that the maximal ideal of `A`
is not an associated prime of `A/I`, for `I` the stalk at `ξ` of the ideal sheaf of the closed
subscheme `Z`. That is not a statement a consumer can read off the geometry as written.

This file supplies it from the geometric hypothesis the source states, namely that `ξ` is not an
associated point of `Z`. Being an associated point of `Z` is a condition on the local ring of `Z`
at that point (Stacks Tag 02OJ), and the local ring of `Z` is `A/I`
(`Stacks.Chow.ringKrullDim_quotient_idealStalk_eq` reads the same identification for Krull
dimensions), so the two conditions are two spellings of one thing — once the two notions of
associated prime in play are reconciled.

## Main results

* `Stacks.Chow.notMem_associatedPrimes_idealStalk_of_notMem_schemeAssociatedPoints` — if a point
  of a closed subscheme `Z ⊆ X` of a locally Noetherian scheme is not an associated point of `Z`,
  then the maximal ideal of the local ring of `X` there is not an associated prime of the quotient
  by the stalk of the ideal sheaf of `Z`.

## Implementation notes

Three mismatches have to be bridged, and each is handled by a lemma below or by an existing one.

First, the two notions of associated prime differ: `IsAssociatedPrimeStacks` of Stacks Tag 00LA,
which the definition of an associated point is stated against, asks for the annihilator of an
element to be *equal* to the prime, whereas Mathlib's `IsAssociatedPrime`, which the local
multiplicity comparison is stated against, inserts a radical. Over a Noetherian ring the two
agree, by `isAssociatedPrime_iff`; this is the only place Noetherianity is used, and it is why
`IsLocallyNoetherian X` appears in the statement — it gives `IsNoetherianRing` for the stalk.

Second, an associated point of a scheme is defined through the stalk of the structure sheaf read
as a module over itself, not through the local ring directly. That identification is
`AlgebraicGeometry.structureSheafStalkLinearEquiv`, and
`Stacks.Chow.isAssociatedPrimeStacks_of_linearEquiv` transports the Tag 00LA notion along it.

Third, the module `A/I` over `A` has to be recognised as the local ring of `Z` with its `A`-action
through the stalk map. The stalk map of the canonical closed immersion is surjective with kernel
the stalk of the ideal sheaf (`Stacks.Chow.ker_stalkMap_eq_idealStalk_ker` together with
`AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι`), so `A/I` is the local ring of `Z` as an
`A`-module; the annihilator of an element of that ring over `A` is the contraction along the stalk
map of its annihilator over the ring itself, and the stalk map being a surjective local
homomorphism, contraction is injective on ideals and carries the maximal ideal to the maximal
ideal. That is `Stacks.Chow.isAssociatedPrimeStacks_of_isAssociatedPrime_quotient_ker`.

## References

* [Stacks Project, Tag 02S5](https://stacks.math.columbia.edu/tag/02S5)
* [Stacks Project, Tag 02OJ](https://stacks.math.columbia.edu/tag/02OJ)
* [Stacks Project, Tag 00LA](https://stacks.math.columbia.edu/tag/00LA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

universe u

namespace Stacks.Chow

/-! ### Transporting the associated primes of Stacks 00LA -/

/-- The associated primes of Stacks Tag 00LA are invariant under a linear equivalence: if `p` is
the annihilator of an element of `M`, it is the annihilator of the corresponding element of `M'`.

Unlike Mathlib's `LinearEquiv.isAssociatedPrime_iff` this is about the strict notion, in which the
annihilator is required to equal `p` rather than to have it as its radical. -/
theorem isAssociatedPrimeStacks_of_linearEquiv {R M M' : Type*} [CommRing R] [AddCommGroup M]
    [Module R M]
    [AddCommGroup M'] [Module R M'] (l : M ≃ₗ[R] M') {p : Ideal R}
    (h : IsAssociatedPrimeStacks R M p) : IsAssociatedPrimeStacks R M' p := by
  obtain ⟨hp, m, hm⟩ := h
  refine ⟨hp, l m, ?_⟩
  rw [← hm]
  ext a
  simp only [Submodule.mem_colon_span_singleton, Submodule.mem_bot, ← l.map_smul,
    LinearEquiv.map_eq_zero_iff]

/-! ### Descent along a surjection of local rings -/

/-- Let `φ : A →+* B` be a surjective local homomorphism of local rings with `A` Noetherian. If
the maximal ideal of `A` is an associated prime of the `A`-module `A ⧸ ker φ`, then the maximal
ideal of `B` is an associated prime of `B` in the strict sense of Stacks Tag 00LA.

The point is that `A ⧸ ker φ` is `B` with its `A`-action through `φ`, so the annihilator over `A`
of an element `b : B` is the contraction along `φ` of its annihilator over `B`; since `φ` is
surjective, contraction is injective on ideals, and it carries the maximal ideal of `B` to the
maximal ideal of `A`. -/
theorem isAssociatedPrimeStacks_of_isAssociatedPrime_quotient_ker {A B : Type*} [CommRing A]
    [CommRing B] [IsNoetherianRing A] [IsLocalRing A] [IsLocalRing B] (φ : A →+* B) [IsLocalHom φ]
    (hφ : Function.Surjective φ)
    (h : IsAssociatedPrime (maximalIdeal A) (A ⧸ RingHom.ker φ)) :
    IsAssociatedPrimeStacks B B (maximalIdeal B) := by
  let _ : Module A B := Module.compHom B φ
  let ψ : A →ₗ[A] B :=
    { toFun := φ
      map_add' := φ.map_add
      map_smul' := fun r a => by
        show φ (r * a) = r • φ a
        rw [map_mul]
        rfl }
  let e : (A ⧸ RingHom.ker φ) ≃ₗ[A] B :=
    (Submodule.quotEquivOfEq _ _ rfl).trans (ψ.quotKerEquivOfSurjective hφ)
  obtain ⟨-, b, hb⟩ := isAssociatedPrime_iff.mp ((LinearEquiv.isAssociatedPrime_iff e).mp h)
  have hcolon : ((⊥ : Submodule B B).colon {b}).comap φ = maximalIdeal A := by
    rw [hb]
    ext a
    simp only [Ideal.mem_comap, Submodule.mem_colon_singleton, Submodule.mem_bot]
    exact Iff.rfl
  refine ⟨(maximalIdeal.isMaximal B).isPrime, b, ?_⟩
  rw [Submodule.colon_span]
  exact Ideal.comap_injective_of_surjective φ hφ
    (hcolon.trans (IsLocalRing.maximalIdeal_comap φ).symm)

/-! ### The hypothesis of the local multiplicity comparison, read on the geometry -/

/-- If a point of a closed subscheme `Z` of a locally Noetherian scheme `X` is not an associated
point of `Z`, then the maximal ideal of the local ring of `X` at that point is not an associated
prime of the quotient of that local ring by the stalk of the ideal sheaf of `Z`.

This is the hypothesis `hI` of
`Stacks.Chow.length_quotient_span_sup_eq_sum_minimalPrimes_of_notMem_associatedPrimes`, supplied
from the condition on associated points that Stacks Tag 02S5 states. -/
theorem notMem_associatedPrimes_idealStalk_of_notMem_schemeAssociatedPoints {X : Scheme.{u}}
    [IsLocallyNoetherian X] (I : X.IdealSheafData) (y : I.subscheme)
    (hy : y ∉ Stacks.Divisors.schemeAssociatedPoints I.subscheme) :
    maximalIdeal (X.presheaf.stalk (I.subschemeι y)) ∉
      associatedPrimes (X.presheaf.stalk (I.subschemeι y))
        (X.presheaf.stalk (I.subschemeι y) ⧸
          AlgebraicGeometry.IdealSheafData.stalk I (I.subschemeι y)) := by
  intro h
  have hker : RingHom.ker (I.subschemeι.stalkMap y).hom =
      IdealSheafData.stalk I (I.subschemeι y) := by
    rw [ker_stalkMap_eq_idealStalk_ker, Scheme.IdealSheafData.ker_subschemeι]
  rw [← hker] at h
  exact hy (isAssociatedPrimeStacks_of_linearEquiv
    (structureSheafStalkLinearEquiv I.subscheme y).symm
    (isAssociatedPrimeStacks_of_isAssociatedPrime_quotient_ker
      (I.subschemeι.stalkMap y).hom (SurjectiveOnStalks.stalkMap_surjective I.subschemeι y) h))

end Stacks.Chow

end
