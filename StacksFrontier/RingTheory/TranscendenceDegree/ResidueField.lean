module

import Mathlib.FieldTheory.FinTrdeg

public import StacksFrontier.RingTheory.KrullDimension.FiniteTypeOverField
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

universe u v

/-!
# Transcendence degree of the residue fields drops along a strict inclusion of primes

Let `k` be a field and let `S` be a `k`-algebra of finite type. This file proves Stacks 06RP: if
`𝔮 ⊊ 𝔮'` are prime ideals of `S`, then the residue field `κ(𝔮')` has strictly smaller
transcendence degree over `k` than `κ(𝔮)`.

The proof is the source's. Stacks 00P0, applied to the finite type `k`-algebra domain `S ⧸ 𝔮`
with field of fractions `κ(𝔮)`, computes `dim (S ⧸ 𝔮) = trdeg_k κ(𝔮)`, and likewise at `𝔮'`. The
strict inclusion `V(𝔮') ⊊ V(𝔮)` of irreducible closed subsets gives
`dim (S ⧸ 𝔮') + 1 ≤ dim (S ⧸ 𝔮)`: a chain of primes above `𝔮'` is prolonged by prefixing `𝔮`.
Both transcendence degrees are finite, `k ⊆ κ(𝔮)` being essentially of finite type, so the
inequality of dimensions is an inequality of cardinals.

## Main results

* `Stacks.TranscendenceDegree.ResidueDrop.solution`: the statement of the tag,
  `Ideal.trdeg_residueField_lt_trdeg_residueField_of_lt`.

## Implementation notes

The dimension drop is the content, and it is carried by `ringKrullDim_quotient_succ_le_of_lt`:
for primes `p < q` of an arbitrary commutative ring, `dim (R ⧸ q) + 1 ≤ dim (R ⧸ p)`. It is
proved by reading `dim (R ⧸ p)` as the coheight of `p` in `PrimeSpectrum R`
(`ringKrullDim_quotient_eq_coheight`, the vanishing locus of `p` being the interval `Set.Ici p`
by `zeroLocus_eq_Ici`), where the statement is `Order.coheight_add_one_le`. None of the three is
special to the situation of the tag; they belong to Mathlib beside `ringKrullDim_quotient`.

Both applications of Stacks 00P0 are one lemma,
`ringKrullDim_quotient_eq_toENat_trdeg_residueField`, which also holds the scalar tower
`k → S ⧸ 𝔮 → κ(𝔮)` that instance search does not see through the definition of
`Ideal.ResidueField`.

Passing from `dim (S ⧸ 𝔮') + 1 ≤ dim (S ⧸ 𝔮)` back to a strict inequality of `Cardinal` is
`lt_of_toENat_add_one_le_toENat`: `Cardinal.toENat` reflects `≤` at a finite cardinal
(`Cardinal.toENat_le_iff_of_lt_aleph0`), and `ENat.add_one_le_iff` turns the successor bound into
a strict one. The finiteness is `trdeg_residueField_lt_aleph0`, which holds because
`Algebra.EssFiniteType k κ(𝔮)` composes `Algebra.EssFiniteType k S` with the residue field's own
instance over `S`.

## References

* [StacksProject 06RP](https://stacks.math.columbia.edu/tag/06RP)
-/

namespace Stacks.TranscendenceDegree.ResidueDrop



/-- The vanishing locus of a prime ideal `p` is the set of primes containing `p`. -/
private lemma zeroLocus_eq_Ici {R : Type*} [CommRing R] (p : Ideal R) [hp : p.IsPrime] :
    PrimeSpectrum.zeroLocus (R := R) p = Set.Ici (⟨p, hp⟩ : PrimeSpectrum R) := rfl

/-- The dimension of `V(p) = Spec (R ⧸ p)` is the coheight of `p` in `PrimeSpectrum R`. -/
private lemma ringKrullDim_quotient_eq_coheight {R : Type*} [CommRing R] (p : Ideal R)
    [hp : p.IsPrime] :
    ringKrullDim (R ⧸ p) =
      ((Order.coheight (⟨p, hp⟩ : PrimeSpectrum R) : ℕ∞) : WithBot ℕ∞) := by
  rw [ringKrullDim_quotient, zeroLocus_eq_Ici, ← Order.coheight_eq_krullDim_Ici]

/-- Along a strict inclusion `p < q` of prime ideals the dimension of the quotient drops:
`dim (R ⧸ q) + 1 ≤ dim (R ⧸ p)`. -/
private lemma ringKrullDim_quotient_succ_le_of_lt {R : Type*} [CommRing R] {p q : Ideal R}
    [hp : p.IsPrime] [hq : q.IsPrime] (h : p < q) :
    ringKrullDim (R ⧸ q) + 1 ≤ ringKrullDim (R ⧸ p) := by
  rw [ringKrullDim_quotient_eq_coheight, ringKrullDim_quotient_eq_coheight]
  exact_mod_cast Order.coheight_add_one_le (α := PrimeSpectrum R) h

/-- A finite cardinal `a` with `toENat a + 1 ≤ toENat b` is `< b`. -/
private lemma lt_of_toENat_add_one_le_toENat {a b : Cardinal} (ha : a < Cardinal.aleph0)
    (h : Cardinal.toENat a + 1 ≤ Cardinal.toENat b) : a < b := by
  rw [← not_le, ← Cardinal.toENat_le_iff_of_lt_aleph0 ha, not_le,
    ← ENat.add_one_le_iff (Cardinal.toENat_lt_top.mpr ha).ne]
  exact h

/-- Stacks 00P0 at a prime `𝔮` of a finite type algebra over a field: the dimension of `S ⧸ 𝔮`
is the transcendence degree of the residue field `κ(𝔮)`, which is its field of fractions. -/
@[ega "IV 5.6.5" "special case"]
private lemma ringKrullDim_quotient_eq_toENat_trdeg_residueField (k : Type u) [Field k]
    {S : Type v} [CommRing S] [Algebra k S] [Algebra.FiniteType k S] (q : Ideal S) [q.IsPrime] :
    ringKrullDim (S ⧸ q) =
      ((Cardinal.toENat (Algebra.trdeg k q.ResidueField) : ℕ∞) : WithBot ℕ∞) :=
  have : IsScalarTower k (S ⧸ q) q.ResidueField :=
    inferInstanceAs (IsScalarTower k (S ⧸ q) (IsLocalRing.ResidueField (Localization.AtPrime q)))
  (ringKrullDim_eq_trdeg_and_ringKrullDim_localization_eq_trdeg.{u, v, v, 0} k (S ⧸ q)
    q.ResidueField).1

/-- The residue field at a prime of a finite type algebra over a field has finite transcendence
degree, `k → κ(𝔮)` being essentially of finite type. -/
private lemma trdeg_residueField_lt_aleph0 (k : Type u) [Field k] {S : Type v} [CommRing S]
    [Algebra k S] [Algebra.FiniteType k S] (q : Ideal S) [q.IsPrime] :
    Algebra.trdeg k q.ResidueField < Cardinal.aleph0 :=
  have : IsScalarTower k S q.ResidueField := IsScalarTower.of_algebraMap_eq' rfl
  have : Algebra.EssFiniteType k q.ResidueField := .comp k S _
  trdeg_lt_aleph0 k _

/-- Stacks 06RP: along a strict inclusion `𝔮 < 𝔮'` of primes of a finite type algebra over a
field `k`, the transcendence degree over `k` of the residue field drops. -/
public theorem solution
    (k : Type u) [Field k] {S : Type v} [CommRing S] [Algebra k S] [Algebra.FiniteType k S]
    {q q' : Ideal S} [q.IsPrime] [q'.IsPrime] (h : q < q') :
    Algebra.trdeg k q'.ResidueField < Algebra.trdeg k q.ResidueField := by
  have hd := ringKrullDim_quotient_succ_le_of_lt h
  rw [ringKrullDim_quotient_eq_toENat_trdeg_residueField k q,
    ringKrullDim_quotient_eq_toENat_trdeg_residueField k q'] at hd
  exact lt_of_toENat_add_one_le_toENat (trdeg_residueField_lt_aleph0 k q') (by exact_mod_cast hd)

end Stacks.TranscendenceDegree.ResidueDrop

/-!
# Transcendence degree of the residue fields drops along a strict inclusion of primes

Let `k` be a field and let `S` be a `k`-algebra of finite type. If `𝔮 ⊆ 𝔮'` are distinct prime
ideals of `S`, then the residue field `κ(𝔮')` has strictly smaller transcendence degree over `k`
than `κ(𝔮)` (Stacks 06RP).

The proof is the source's: by Lemma 00P0 applied to the finite type `k`-algebra `S ⧸ 𝔮`, whose
field of fractions is `κ(𝔮)`, the transcendence degree of `κ(𝔮)` over `k` is the dimension of
`V(𝔮) = Spec (S ⧸ 𝔮)`, and likewise for `𝔮'`. The strict inclusion `V(𝔮') ⊊ V(𝔮)` of irreducible
closed subsets forces a strict inequality of dimensions: a chain of primes of length `n` above
`𝔮'` is prolonged by prefixing `𝔮 ⊊ 𝔮'` to a chain of length `n + 1` above `𝔮`, so
`dim (S ⧸ 𝔮') + 1 ≤ dim (S ⧸ 𝔮)`, both dimensions being finite.

## Main results

* `Ideal.trdeg_residueField_lt_trdeg_residueField_of_lt`: for `𝔮 < 𝔮'` prime ideals of a finite
  type algebra `S` over a field `k`, `trdeg_k κ(𝔮') < trdeg_k κ(𝔮)`. The inequality runs against
  the inclusion: the *smaller* prime has the *larger* residue transcendence degree.

## Implementation notes

The residue field `κ(𝔮)` is Mathlib's `Ideal.ResidueField 𝔮`, that is the residue field of
`Localization.AtPrime 𝔮`; it comes with `IsFractionRing (S ⧸ 𝔮) 𝔮.ResidueField`, so it is the
field of fractions of `S ⧸ 𝔮` that the source writes, and with
`Ideal.ker_algebraMap_residueField : RingHom.ker (algebraMap S 𝔮.ResidueField) = 𝔮`, which pins
the canonical map `S → κ(𝔮)` and its kernel rather than positing some field of the right size.
Unlike the abstract `IsFractionRing S K` of Lemma 00P0 this is a named object, which is what keeps
both transcendence degrees in the single universe of `S`, so the conclusion is an inequality of
`Cardinal.{v}` needing no `Cardinal.lift`; a reader holding another model `K` of `κ(𝔮)`, say
`FractionRing (S ⧸ 𝔮)`, rewrites along `IsFractionRing.algEquiv` and `AlgEquiv.trdeg_eq`.

The `k`-algebra structure on `κ(𝔮)` is the canonical one, not an extra datum: it is inferred from
`Algebra k S` and satisfies both `IsScalarTower k S 𝔮.ResidueField` and
`IsScalarTower k (S ⧸ 𝔮) 𝔮.ResidueField`, so `Algebra.trdeg k 𝔮.ResidueField` is the transcendence
degree of `κ(𝔮)` over `k` computed through the given `k`-structure of `S`.

The comparison is a strict inequality of cardinals, where the source's `<` is between natural
numbers. This is no weaker: `Algebra.EssFiniteType k 𝔮.ResidueField` holds (from
`Algebra.EssFiniteType.comp` and the residue field's own instance), so both transcendence degrees
are `< ℵ₀` by `trdeg_lt_aleph0`, and for finite cardinals `a < b`, `a + 1 ≤ b` and
`Cardinal.toENat a < Cardinal.toENat b` all agree.

Faithfulness. (1) No hypothesis is dead: `Field k` is used — over `k = ℤ` and `S = ℤ` the primes
`⊥ < (2)` give `κ(⊥) = ℚ` and `κ((2)) = 𝔽₂`, both of transcendence degree `0` over `ℤ`;
`Algebra.FiniteType k S` is used — for `S = k[x₁, x₂, …]` the primes `⊥ < (x₁)` give residue
fields `k(x₁, x₂, …)` and `k(x₂, x₃, …)`, both of transcendence degree `ℵ₀`; and `𝔮 < 𝔮'` carries
the source's "distinct", the conclusion failing outright for `𝔮 = 𝔮'`. (2) The scalars and base
are the source's: the transcendence degree is taken over `k`, of the residue fields of `S` itself,
with no base change and no localization of `k`. (3) The map the source names is pinned: `κ(𝔮)` is
`Ideal.ResidueField`, a definition whose structure map from `S` has kernel exactly `𝔮`, so the
statement is about the residue field at `𝔮` and not about an unspecified extension of `k`.
(4) The instantiation is not degenerate: for `k = ℚ`, `S = ℚ[x, y]`, `𝔮 = ⊥` and `𝔮' = (x)` one
has `κ(𝔮) = ℚ(x, y)` and `κ(𝔮') = ℚ(y)`, so the conclusion reads `1 < 2`; taking `𝔮' = (x, y)`
maximal instead gives `0 < 2`. Both primes range over all of `Spec S`, the maximal ones included,
where the right-hand side may itself be `0` and the hypothesis is then unsatisfiable.

## References

* [StacksProject 06RP](https://stacks.math.columbia.edu/tag/06RP)
-/

@[expose] public section



/-- **Stacks 06RP.** Let `k` be a field, let `S` be a finite type `k`-algebra, and let
`𝔮 ⊊ 𝔮'` be prime ideals of `S`. Then the transcendence degree over `k` of the residue field
`κ(𝔮')` is strictly smaller than that of `κ(𝔮)`. -/
@[stacks 06RP "The residue field `κ(𝔮)` is Mathlib's `Ideal.ResidueField`, the fraction field of
`S ⧸ 𝔮`, and the comparison is a strict inequality of `Cardinal`, both degrees being finite. See
the module docstring."]
public theorem Ideal.trdeg_residueField_lt_trdeg_residueField_of_lt
    (k : Type u) [Field k] {S : Type v} [CommRing S] [Algebra k S] [Algebra.FiniteType k S]
    {q q' : Ideal S} [q.IsPrime] [q'.IsPrime] (h : q < q') :
    Algebra.trdeg k q'.ResidueField < Algebra.trdeg k q.ResidueField :=
    by exact Stacks.TranscendenceDegree.ResidueDrop.solution (S := S) k h

end
