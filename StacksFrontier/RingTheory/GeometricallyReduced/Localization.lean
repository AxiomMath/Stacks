module

public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Nilpotent.GeometricallyReduced
public import StacksFrontier.RingTheory.GeometricallyReduced.Basic

/-!
# Subalgebras and localizations of geometrically reduced algebras

Let `k` be a field and let `S` be a `k`-algebra which is geometrically reduced over `k`. Then every
`k`-subalgebra of `S` is geometrically reduced over `k`, and so is every localization of `S`,
regarded as a `k`-algebra through `S`.

For a subalgebra this is base change along an injective map: `K ⊗[k] -` is exact for a field `K`
over `k`, so `K ⊗[k] B` is a subring of the reduced ring `K ⊗[k] S`. For a localization `S'` of `S`
at a submonoid `M ⊆ S`, base change commutes with localization: `S' ⊗[k] K` is the localization of
`S ⊗[k] K` at the image of `M`, and a localization of a reduced ring is reduced.

## Main results

* `Subalgebra.isGeometricallyReduced`: a `k`-subalgebra of a geometrically reduced `k`-algebra is
  geometrically reduced.
* `IsLocalization.isGeometricallyReduced`: a localization of a geometrically reduced
  `k`-algebra is geometrically reduced.

## Implementation notes

Geometric reducedness is Mathlib's `Algebra.IsGeometricallyReduced`, which over a field `k` is
reducedness of `AlgebraicClosure k ⊗[k] S` (`Algebra.isGeometricallyReduced_field_iff`); it is
equivalent to the source's Definition 030S, reducedness of `K ⊗[k] S` for every field extension
`K/k`, by Lemma 030V (`Algebra.isGeometricallyReduced_tfae`).

A localization is spelled abstractly, as an `S`-algebra `S'` with `IsLocalization M S'` and the
`k`-algebra structure restricted along `algebraMap S S'` (`IsScalarTower k S S'`), so that
`Localization M`, `Localization.AtPrime 𝔭` and `FractionRing S` are instances of the statement.
No hypothesis is put on `M`: if `0 ∈ M` the localization is the zero ring, which is geometrically
reduced.

## References

* [Stacks 030T](https://stacks.math.columbia.edu/tag/030T) (`algebra-lemma-subalgebra-separable`),
  parts (1) and (4), in the section "Geometrically reduced algebras".
-/

@[expose] public section

open scoped TensorProduct

universe u v w

/-- A `k`-subalgebra of a geometrically reduced `k`-algebra is geometrically reduced over `k`. -/
@[stacks 030T "Part (1): every `k`-subalgebra of a geometrically reduced `k`-algebra is
  geometrically reduced; this is Mathlib's `Algebra.IsGeometricallyReduced.of_injective` applied to
  the inclusion `B.val`. Part (2) is Mathlib's `Algebra.IsGeometricallyReduced.of_forall_fg`, part
  (3) is `DirectLimit.instIsGeometricallyReduced`, part (4) is
  `IsLocalization.isGeometricallyReduced`. Geometric reducedness is Mathlib's
  `Algebra.IsGeometricallyReduced`, equivalent to Definition 030S by Lemma 030V."]
public instance Subalgebra.isGeometricallyReduced {k : Type u} {S : Type v} [Field k] [Ring S]
    [Algebra k S] [Algebra.IsGeometricallyReduced k S] (B : Subalgebra k S) :
    Algebra.IsGeometricallyReduced k B :=
  Algebra.IsGeometricallyReduced.of_injective B.val Subtype.val_injective

namespace IsLocalization

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- A localization of a geometrically reduced algebra over a field is geometrically reduced: if `S`
is geometrically reduced over the field `k` and `S'` is the localization of `S` at a submonoid
`M ⊆ S`, regarded as a `k`-algebra through `S`, then `S'` is geometrically reduced over `k`. -/
@[stacks 030T "Part (4): any localization of a geometrically reduced `k`-algebra is geometrically
  reduced. The source's localization is spelled abstractly as an `S`-algebra `S'` with
  `IsLocalization M S'` and `IsScalarTower k S S'`. Part (1) is `Subalgebra.isGeometricallyReduced`,
  part (2) is Mathlib's `Algebra.IsGeometricallyReduced.of_forall_fg`, part (3) is
  `DirectLimit.instIsGeometricallyReduced`. Geometric reducedness is Mathlib's
  `Algebra.IsGeometricallyReduced`, equivalent to Definition 030S by Lemma 030V."]
public theorem isGeometricallyReduced {k : Type u} {S : Type v} {S' : Type w} [Field k]
    [CommRing S] [Algebra k S] [CommRing S'] [Algebra S S'] [Algebra k S'] [IsScalarTower k S S']
    (M : Submonoid S) [IsLocalization M S'] [Algebra.IsGeometricallyReduced k S] :
    Algebra.IsGeometricallyReduced k S' := by
  rw [Algebra.isGeometricallyReduced_field_iff]
  have h : IsReduced (S ⊗[k] AlgebraicClosure k) :=
    isReduced_of_injective (Algebra.TensorProduct.comm k S (AlgebraicClosure k))
      (AlgEquiv.injective _)
  have : IsReduced (S' ⊗[S] (S ⊗[k] AlgebraicClosure k)) :=
    isReduced_localization _ (Algebra.algebraMapSubmonoid (S ⊗[k] AlgebraicClosure k) M) _
  have : IsReduced (S' ⊗[k] AlgebraicClosure k) :=
    isReduced_of_injective
      (Algebra.TensorProduct.cancelBaseChange k S S' S' (AlgebraicClosure k)).symm
      (AlgEquiv.injective _)
  exact isReduced_of_injective (Algebra.TensorProduct.comm k (AlgebraicClosure k) S')
    (AlgEquiv.injective _)

end IsLocalization

end
