module

public import Mathlib.RingTheory.Flat.Basic
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.PolynomialQuotientBaseChange
public import StacksFrontier.RingTheory.GeometricallyIntegral.Defs
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Absolute irreducibility of the model polynomial

Part of Step D of the proof of Stacks Tag 0559. Step C and the transport of
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.LastVariable` produce a polynomial
`q ∈ K[x₁, …, x_{r+1}]` generating the kernel of a map onto the function field `L` of the
generic fibre, so that `B := K[x₁, …, x_{r+1}] ⧸ (q)` embeds into `L`. What Step F needs of `q`
is that it stays irreducible over an algebraically closed extension `K̄` of `K`, and that is
what is proved here.

The route is base change, not Gauss's lemma. Geometric integrality of `L/K` makes `L ⊗[K] K̄` a
domain; `B` embeds into `L` and `K̄` is a flat `K`-module, so `B ⊗[K] K̄` embeds into `L ⊗[K] K̄`
and is a domain too; by `MvPolynomial.quotientSpanTensorEquiv` that ring is
`K̄[x₁, …, x_{r+1}] ⧸ (q^φ)`, so the ideal `(q^φ)` is prime, so `q^φ` is a prime element, so it
is irreducible.

## Main results

* `MvPolynomial.irreducible_map_of_isDomain_tensor`: **absolute irreducibility of the model
  polynomial**, from the hypothesis that `L ⊗[K] K̄` is a domain.
* `MvPolynomial.irreducible_map_of_isGeometricallyIntegral`: the same with the hypothesis in the
  form in which Step A supplies it, geometric integrality of `L` over `K`.

## Implementation notes

The embedding `B → L` is an arbitrary injective `K`-algebra map, not necessarily the one induced
by a presentation of `L`: all that is used of it is injectivity, and stating it this way means
the caller does not have to produce an identification of `L` with the fraction field of `B` (that
is a separate part of Step D).

Only `q ≠ 0` is assumed of `q` beyond the embedding; irreducibility of `q` over `K` itself is a
consequence rather than a hypothesis, since a prime element of `K̄[xᵢ]` whose image generates a
prime ideal cannot factor.

The step from an injective `K`-algebra map `B →ₐ[K] L` to an injective map
`B ⊗[K] K̄ → L ⊗[K] K̄` duplicates the private lemma
`Stacks.GeometricallyIntegral.TensorDomain.isDomain_tensorProduct_of_injective`
(`StacksFrontier/RingTheory/GeometricallyIntegral/TensorProduct.lean`), which is not exported; it is
two lines, and one public lemma next to `Algebra.IsGeometricallyIntegral.isDomain_tensorProduct`
would retire both copies.

No Stacks tag is attached: Step D is not itself a tag of the source.

## References

* [Stacks Project, Tag 0559](https://stacks.math.columbia.edu/tag/0559), Step D of the first
  proof
* [Stacks Project, Tag 05DX](https://stacks.math.columbia.edu/tag/05DX)
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace MvPolynomial

/-- **Absolute irreducibility of the model polynomial, part of Step D of Stacks Tag 0559.** Let
`K` be a field, let `K̄` be a field extension of `K` and let `L` be a `K`-algebra with
`L ⊗[K] K̄` a domain. If a nonzero `q : MvPolynomial ι K` is such that
`MvPolynomial ι K ⧸ (q)` embeds into `L` over `K`, then the coefficientwise image of `q` in
`K̄[xᵢ]` is irreducible. -/
@[ega "IV 9.7.4" "a ⇒ b"]
theorem irreducible_map_of_isDomain_tensor {K : Type u} [Field K] {Kbar : Type v} [Field Kbar]
    [Algebra K Kbar] {ι : Type w} {L : Type*} [CommRing L] [Algebra K L]
    (hL : IsDomain (L ⊗[K] Kbar)) {q : MvPolynomial ι K} (hq : q ≠ 0)
    (φ : (MvPolynomial ι K ⧸ Ideal.span {q}) →ₐ[K] L) (hφ : Function.Injective φ) :
    Irreducible (q.map (algebraMap K Kbar)) := by
  have _ := hL
  have hinj : Function.Injective (Algebra.TensorProduct.map φ (AlgHom.id K Kbar)) :=
    Module.Flat.rTensor_preserves_injective_linearMap (M := Kbar) φ.toLinearMap hφ
  have hdom : IsDomain ((MvPolynomial ι K ⧸ Ideal.span {q}) ⊗[K] Kbar) :=
    hinj.isDomain (Algebra.TensorProduct.map φ (AlgHom.id K Kbar)).toRingHom
  have hdom2 : IsDomain (MvPolynomial ι Kbar ⧸ Ideal.span {q.map (algebraMap K Kbar)}) :=
    MulEquiv.isDomain _
      (MvPolynomial.quotientSpanTensorEquiv K Kbar ι q).symm.toRingEquiv.toMulEquiv
  have hprime : (Ideal.span {q.map (algebraMap K Kbar)}).IsPrime :=
    (Ideal.Quotient.isDomain_iff_prime _).mp hdom2
  have hqne : q.map (algebraMap K Kbar) ≠ 0 := fun h => hq <|
    MvPolynomial.map_injective _ (algebraMap K Kbar).injective (by simpa using h)
  exact ((Ideal.span_singleton_prime hqne).mp hprime).irreducible

/-- `MvPolynomial.irreducible_map_of_isDomain_tensor` with the hypothesis on `L` in the form
Step A supplies it: `L` is geometrically integral over `K`. -/
@[ega "IV 9.7.4" "a ⇒ b"]
theorem irreducible_map_of_isGeometricallyIntegral {K Kbar L : Type u} [Field K] [Field Kbar]
    [Algebra K Kbar] [CommRing L] [Algebra K L] [Algebra.IsGeometricallyIntegral K L]
    {ι : Type w} {q : MvPolynomial ι K} (hq : q ≠ 0)
    (φ : (MvPolynomial ι K ⧸ Ideal.span {q}) →ₐ[K] L) (hφ : Function.Injective φ) :
    Irreducible (q.map (algebraMap K Kbar)) :=
  irreducible_map_of_isDomain_tensor
    ((Algebra.isGeometricallyIntegral_iff_isDomain_tensorProduct K L).mp ‹_› Kbar) hq φ hφ

end MvPolynomial

end
