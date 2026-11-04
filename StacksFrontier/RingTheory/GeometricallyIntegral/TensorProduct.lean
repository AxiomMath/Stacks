module

public import StacksFrontier.RingTheory.GeometricallyIntegral.Defs

/-!
# Tensor products with a geometrically integral algebra are domains

Let `k` be a field and let `S` be a geometrically integral `k`-algebra, that is, a `k`-algebra
such that `S ⊗[k] k'` is a domain for every field extension `k'/k`. Then `R ⊗[k] S` is a domain
for every `k`-algebra `R` which is a domain.

Let `K` be the fraction field of `R`. Geometric integrality of `S` applies to the field extension
`K/k` and gives that `K ⊗[k] S` is a domain. The inclusion `R → K` is an injective `k`-algebra
map, and tensoring it with `S` over `k` stays injective because every module over a field is
flat; hence `R ⊗[k] S` is a subring of the domain `K ⊗[k] S`, and therefore a domain itself.

## Main results

* `Algebra.IsGeometricallyIntegral.isDomain_tensorProduct`: if `S` is a geometrically integral
  `k`-algebra and `R` is a `k`-algebra which is a domain, then `R ⊗[k] S` is a domain.
* `Stacks.GeometricallyIntegral.TensorDomain.solution`: the same statement.

## Implementation notes

The source argues differently: a domain is a ring which is both reduced and irreducible, and it
gets reducedness of `R ⊗[k] S` from Lemma 034N and irreducibility from Lemma 037O. The route
taken here uses neither, because the hypothesis on `S` is already a statement about tensoring
with field extensions of `k` (`Algebra.isGeometricallyIntegral_iff_isDomain_tensorProduct`, from
Definition 05DX), and `FractionRing R` is one of them since `R` lies in the universe of `k` and
`S`. The three rings lie in a single universe, as they do in `Algebra.IsGeometricallyIntegral`,
whose quantifier over field extensions ranges over one universe because it is phrased through
`Spec`.

Neither hypothesis can be dropped: `IsDomain R` cannot, since `k[X]/(X²) ⊗[k] k ≅ k[X]/(X²)`, and
geometric integrality of `S` cannot be weakened to `IsDomain S`, since
`ℚ(i) ⊗[ℚ] ℚ(i) ≅ ℚ(i) × ℚ(i)`. The source writes the geometrically integral factor on the
right, and that order is kept here; `Algebra.TensorProduct.comm` transports the conclusion to
`S ⊗[k] R`.

Both auxiliary lemmas are stated for a commutative base semiring and an arbitrary flat right
factor, which is all their proofs use. `map_id_injective_of_flat_right` is the algebra-level form
of `IsTensorProduct.map_id_injective_of_flat_right`, and belongs with the latter and with
`Algebra.TensorProduct.includeLeft_injective` in `Mathlib.RingTheory.Flat.Basic`.

## References

* [Stacks Project, Tag 09P9](https://stacks.math.columbia.edu/tag/09P9)
-/

@[expose] public section

universe u

namespace Stacks.GeometricallyIntegral.TensorDomain

open TensorProduct

/-- Tensoring an injective morphism of `k`-algebras with a flat `k`-module on the right leaves it
injective. This is the algebra-level form of
`IsTensorProduct.map_id_injective_of_flat_right`. -/
private theorem map_id_injective_of_flat_right {k R A S : Type*} [CommSemiring k] [CommSemiring R]
    [CommSemiring A] [CommSemiring S] [Algebra k R] [Algebra k A] [Algebra k S]
    [Module.Flat k S] (f : R →ₐ[k] A) (hf : Function.Injective f) :
    Function.Injective (Algebra.TensorProduct.map f (AlgHom.id k S)) :=
  Module.Flat.rTensor_preserves_injective_linearMap (M := S) f.toLinearMap hf

/-- If `S` is a flat `k`-module and the `k`-algebra `R` embeds into a `k`-algebra `A` such that
`A ⊗[k] S` is a domain, then `R ⊗[k] S` is a domain. -/
private theorem isDomain_tensorProduct_of_injective {k R A S : Type*} [CommSemiring k]
    [CommSemiring R] [CommSemiring A] [CommSemiring S] [Algebra k R] [Algebra k A] [Algebra k S]
    [Module.Flat k S] [IsDomain (A ⊗[k] S)] (f : R →ₐ[k] A) (hf : Function.Injective f) :
    IsDomain (R ⊗[k] S) :=
  (map_id_injective_of_flat_right f hf).isDomain
    (Algebra.TensorProduct.map f (AlgHom.id k S)).toRingHom

/-- Let `k` be a field, let `S` be a geometrically integral `k`-algebra and let `R` be a
`k`-algebra which is an integral domain. Then `R ⊗[k] S` is an integral domain. -/
public theorem solution (k R S : Type u) [Field k]
    [CommRing R] [IsDomain R] [Algebra k R] [CommRing S] [Algebra k S]
    [Algebra.IsGeometricallyIntegral k S] : IsDomain (R ⊗[k] S) := by
  -- The fraction field of `R` is a field extension of `k` in the universe of `k`.
  have : IsDomain (S ⊗[k] FractionRing R) :=
    (Algebra.isGeometricallyIntegral_iff_isDomain_tensorProduct k S).mp ‹_› (FractionRing R)
  have : IsDomain (FractionRing R ⊗[k] S) :=
    (Algebra.TensorProduct.comm k (FractionRing R) S).injective.isDomain
      (Algebra.TensorProduct.comm k (FractionRing R) S).toRingHom
  -- `R ⊗[k] S` is a subring of `FractionRing R ⊗[k] S`, because `S` is flat over the field `k`.
  exact isDomain_tensorProduct_of_injective (IsScalarTower.toAlgHom k R (FractionRing R))
    (IsFractionRing.injective R (FractionRing R))

end Stacks.GeometricallyIntegral.TensorDomain

@[expose] public section

open TensorProduct

/-- Let `k` be a field, let `S` be a geometrically integral `k`-algebra and let `R` be a
`k`-algebra which is an integral domain. Then `R ⊗[k] S` is an integral domain. -/
@[stacks 09P9]
public theorem Algebra.IsGeometricallyIntegral.isDomain_tensorProduct (k R S : Type u) [Field k]
    [CommRing R] [IsDomain R] [Algebra k R] [CommRing S] [Algebra k S]
    [Algebra.IsGeometricallyIntegral k S] : IsDomain (R ⊗[k] S) :=
  Stacks.GeometricallyIntegral.TensorDomain.solution k R S
