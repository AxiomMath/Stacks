module

public import StacksFrontier.RingTheory.GeometricallyNormal.Defs
public import StacksFrontier.RingTheory.GeometricallyNormal.TFAE

/-!
# Localization preserves geometric normality

Let `k` be a field and let `A` be a commutative `k`-algebra which is geometrically normal over `k`,
that is, `k' ⊗[k] A` is a normal ring (Definition [stacks, 00GV]) for every field extension `k'/k`
(Definition [stacks, 0380]). Let `S ⊆ A` be a multiplicative subset and let `A'` be the
localization of `A` at `S`, a `k`-algebra through `A`. Then `A'` is geometrically normal over `k`.

The reason is that normality of a ring is a condition on its localizations at prime ideals, and
base change commutes with localization: `k' ⊗[k] A'` is the localization of `k' ⊗[k] A` at the
image of `S`, whose primes are exactly the primes of `k' ⊗[k] A` missing that image, with the same
local rings. So normality of the base changes of `A` is inherited by the base changes of `A'` prime
by prime, with no new local ring to check.

The lemma is what makes geometric normality usable at a point: for a geometrically normal domain
`A` with fraction field `K` it gives that `K` is geometrically normal over `k`, and for a prime
`𝔭 ⊆ A` that `A_𝔭` is.

## Main results

* `Algebra.IsGeometricallyNormal.of_isLocalization`: a localization of a geometrically normal
  algebra over a field is geometrically normal over that field.

## Implementation notes

"A localization of `A`" is spelled abstractly, as an `A`-algebra `A'` with `IsLocalization S A'`
for a submonoid `S ⊆ A`, rather than as the concrete `Localization S`; the `k`-algebra structure on
`A'` is the one restricted along `algebraMap A A'`, which is what `IsScalarTower k A A'` says. The
concrete ring `Localization S` and the fraction field of a domain are instances of the abstract
form, so no user has to transport the conclusion along a ring isomorphism.

The conclusion is an instance of a class, but the statement is a theorem rather than an `instance`,
because `S` cannot be recovered from `A'` by instance search; the specializations that *are* usable
by instance search (`Localization S`, `Localization.AtPrime 𝔭`, `FractionRing A`) are applications
of it, and belong with those constructions rather than here.

No hypothesis is imposed on `S`: it need not consist of nonzerodivisors and need not avoid `0`. The
degenerate case is genuinely covered rather than excluded, since if `0 ∈ S` then `A'` is the zero
ring and each `k' ⊗[k] A'` is the zero ring, which has no prime ideals and so is a normal ring
vacuously.

The localization `A'` lives in its own universe, free of `A`'s, while the test fields quantified
over inside `Algebra.IsGeometricallyNormal` stay in the universe of `k`, exactly as in
Definition 0380.

The `(k' ⊗[k] A)`-algebra structure on `k' ⊗[k] A'` is not an instance — it depends on the
localization map `A → A'`, which instance search cannot recover — so it is supplied locally, as the
base change of `algebraMap A A'` along `k`, together with the tower over `k'` that
`IsLocalization.tensorProduct_tensorProduct_right` asks for. That lemma is exactly the assertion
that base change commutes with localization, and `IsNormalRing.isLocalization` (Lemma
[stacks, 037C]) is exactly the assertion that a localization of a normal ring is normal; the proof
is their composition.

## References

* [Stacks 06DE](https://stacks.math.columbia.edu/tag/06DE), Lemma 10.166.3, in the section
  "Geometrically normal algebras"; geometric normality is Definition 0380, a normal ring is
  Definition 00GV, and the underlying fact that a localization of a normal ring is normal is
  Lemma 037C.
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace Algebra

/-- A localization of a geometrically normal algebra over a field is geometrically normal: if `A`
is geometrically normal over the field `k` and `A'` is the localization of `A` at a submonoid
`S ⊆ A`, regarded as a `k`-algebra through `A`, then `A'` is geometrically normal over `k`. -/
@[stacks 06DE "The source's `S⁻¹A` is spelled abstractly as an `A`-algebra `A'` with
  `IsLocalization S A'` and `IsScalarTower k A A'`, so that the fraction field of a domain and the
  localizations at primes are instances of the statement rather than transports of it."]
public theorem IsGeometricallyNormal.of_isLocalization {k : Type u} {A : Type v} {A' : Type w}
    [Field k] [CommRing A] [CommRing A'] [Algebra k A] [Algebra k A'] [Algebra A A']
    [IsScalarTower k A A'] [IsGeometricallyNormal k A] (S : Submonoid A) [IsLocalization S A'] :
    IsGeometricallyNormal k A' := by
  refine ⟨fun k' _ _ ↦ ?_⟩
  let : Algebra (k' ⊗[k] A) (k' ⊗[k] A') :=
    (Algebra.TensorProduct.map (AlgHom.id k k')
      (IsScalarTower.toAlgHom k A A')).toRingHom.toAlgebra
  have htower : IsScalarTower k' (k' ⊗[k] A) (k' ⊗[k] A') := by
    apply IsScalarTower.of_algebraMap_eq'
    ext x
    simp [RingHom.algebraMap_toAlgebra, Algebra.TensorProduct.algebraMap_apply]
  have hloc : IsLocalization (S.map (Algebra.TensorProduct.includeRight (R := k) (A := k')))
      (k' ⊗[k] A') :=
    IsLocalization.tensorProduct_tensorProduct_right k k' S A'
      (by ext a; simp [RingHom.algebraMap_toAlgebra])
  exact (IsGeometricallyNormal.isNormalRing_tensorProduct (k := k) (A := A) k').isLocalization
    (S.map (Algebra.TensorProduct.includeRight (R := k) (A := k'))) _

end Algebra

end
