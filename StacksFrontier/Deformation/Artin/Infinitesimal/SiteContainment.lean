module

public import StacksFrontier.Deformation.Artin.Infinitesimal.TangentFunctor
public import StacksFrontier.RingTheory.Ideal.QuotientCardinality

/-!
# Placing a ring, a module and their dual numbers in a big fppf site

Membership in a big fppf site is a size condition: `AlgebraicGeometry.BigFppfSite.Contains X`
is `X.size < B.cutoff`, and for an affine scheme the size is `max ℵ₀` of the cardinality of
its ring (Stacks 000P). So every statement of the form "this ring's spectrum lies in the site"
reduces to a cardinality bound, and a site already containing `Spec A` contains the spectrum of
any ring of cardinality at most `max ℵ₀ #A` -- that being the bound the cutoff is closed under.

This file records that reduction for the four shapes the deformation theory of Stacks 07YM
needs: a ring, the trivial square-zero extension of a ring by a module, the resulting
assertion that an `A`-module is a site module, and an arbitrary — not necessarily trivial —
extension of `A` by a small ideal, which is the shape the thickening of Stacks 07YL comes in.

## Main results

* `Deformation.Artin.contains_spec_of_mk_le` — a ring of cardinality at most `max ℵ₀ #A` has
  its spectrum in a site containing `Spec A`.
* `Deformation.Artin.contains_spec_squareZeroRing_of_mk_le` — the same for the dual numbers
  `C[M]` of a ring `C` by a `C`-module `M`.
* `Deformation.Artin.isSiteModule_of_mk_le` — an `A`-module of cardinality at most `max ℵ₀ #A`
  is a site module.
* `Deformation.Artin.contains_spec_of_surjective_of_mk_ker_le` — the same for a ring
  surjecting onto `A` with kernel of cardinality at most `max ℵ₀ #A`.

## Implementation notes

The square-zero extension is a product, so its cardinality is a product of cardinals and
`Cardinal.mul_le_max` finishes; the bound `max ℵ₀ #A` is closed under finite products of
cardinals bounded by it, which is what makes all three statements the same estimate.

A general extension of `A` by an ideal `I` is not a product as a type, but a surjection onto
`A` presents it as a union of `#A` cosets of `I`, so the same product estimate applies; that
is `Cardinal.mk_le_max_of_surjective_of_mk_ker_le_max`. No square-zero hypothesis is needed,
and none is imposed: nilpotence of the kernel plays no part in a size bound.

## References

* [Stacks Project, Tag 000P](https://stacks.math.columbia.edu/tag/000P)
* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Deformation.Artin

universe u

variable (B : BigFppfSite.{u}) {A : Type u} [CommRing A] (hA : B.Contains (Spec (.of A)))

include hA in
/-- A commutative ring of cardinality at most `max ℵ₀ #A` has its spectrum in a big fppf site
containing `Spec A`: the cutoff of the site is a strong prelimit above `ℵ₀`, so it is closed
under the size bound of Stacks 000R (9). -/
public theorem contains_spec_of_mk_le (C : Type u) [CommRing C]
    (h : Cardinal.mk C ≤ max Cardinal.aleph0 (Cardinal.mk A)) :
    B.Contains (Spec (.of C)) :=
  Scheme.size_Spec_lt_of_mk_le_max B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit hA h

include hA in
/-- The trivial square-zero extension `C[M]` of a commutative ring `C` by a `C`-module `M`,
both of cardinality at most `max ℵ₀ #A`, has its spectrum in a big fppf site containing
`Spec A`: the extension is the product `C × M` as a type. -/
public theorem contains_spec_squareZeroRing_of_mk_le (C : Type u) [CommRing C]
    (M : ModuleCat.{u} C) (hC : Cardinal.mk C ≤ max Cardinal.aleph0 (Cardinal.mk A))
    (hM : Cardinal.mk (M : Type u) ≤ max Cardinal.aleph0 (Cardinal.mk A)) :
    B.Contains (Spec (squareZeroRing C M)) := by
  refine contains_spec_of_mk_le B hA (TrivSqZeroExt C (M : Type u)) ?_
  change Cardinal.mk (C × (M : Type u)) ≤ _
  rw [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_id]
  exact (Cardinal.mul_le_max _ _).trans (max_le (max_le hC hM) (le_max_left _ _))

include hA in
/-- A commutative ring surjecting onto `A` with kernel of cardinality at most `max ℵ₀ #A` has
its spectrum in a big fppf site containing `Spec A`: a surjection presents the ring as a union
of `#A` cosets of its kernel, so the size bound of Stacks 000R (9) is again satisfied.

This is the shape the square-zero thickening of Stacks 07YL comes in: there the kernel is a
copy of the residue field at a prime of `A`, which is no larger than `max ℵ₀ #A` by
`Cardinal.mk_residueField_le_max`. -/
public theorem contains_spec_of_surjective_of_mk_ker_le (A' : Type u) [CommRing A']
    (f : A' →+* A) (hf : Function.Surjective f)
    (hker : Cardinal.mk (RingHom.ker f) ≤ max Cardinal.aleph0 (Cardinal.mk A)) :
    B.Contains (Spec (.of A')) :=
  contains_spec_of_mk_le B hA A'
    (Cardinal.mk_le_max_of_surjective_of_mk_ker_le_max f hf hker)

include hA in
/-- An `A`-module of cardinality at most `max ℵ₀ #A` is a site module for a big fppf site
containing `Spec A`. -/
public theorem isSiteModule_of_mk_le (M : ModuleCat.{u} A)
    (hM : Cardinal.mk (M : Type u) ≤ max Cardinal.aleph0 (Cardinal.mk A)) :
    IsSiteModule A B M :=
  contains_spec_squareZeroRing_of_mk_le B hA A M (le_max_right _ _) hM

end Deformation.Artin
