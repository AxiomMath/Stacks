module

public import Mathlib.RingTheory.Algebraic.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Transcendence degree is unchanged by passing to fraction fields

The transcendence degree `trdeg R S` of an extension of domains agrees with the transcendence
degree of the induced extension of fraction fields. This is the identification that lets the
Stacks Project write the dimension formula (Stacks 02IJ) with the ring-level `trdeg_R(S)` and
its scheme-level counterpart (Stacks 02JU) with the field-level
`trdeg_{R(S)} R(X)`: on an affine open the function field of an integral scheme is the fraction
field of the section ring, so the two readings of the formula's transcendence-degree term are
the same number.

The same lemma computes the residue-field term of either formula: `κ(p)` is by construction a
fraction field of `A / p`, so `trdeg_{κ(p)} κ(q)` is the transcendence degree of `B / q` over
`A / p`.

## Main results

* `Algebra.trdeg_eq_of_isFractionRing`: for domains `A ⊆ B` with fraction fields `K` and `L`,
  `trdeg K L = trdeg A B`.
* `Algebra.trdeg_residueField_eq_trdeg_quotient`: for a prime `q` of `B` lying over a prime `p`
  of `A`, `trdeg_{κ(p)} κ(q) = trdeg_{A / p} (B / q)`.

## Implementation notes

Both proofs are the additivity of transcendence degree in towers,
`Algebra.trdeg_add_eq` (Stacks 030H), applied twice to the square

```
A → B
↓   ↓
K → L
```

read along its two paths `A → B → L` and `A → K → L`. The two vertical maps contribute nothing
because a localization is algebraic over the ring it localizes
(`IsLocalization.isAlgebraic`), so `Algebra.trdeg_eq_zero` kills those terms and the two
readings of `trdeg A L` give the result.

`Algebra.trdeg R S` lives in the universe of `S`, so the first lemma is stated with all four
rings in one universe; that is the shape in which its consumers use it.

The residue-field statement has to introduce the `A / p`-algebra structure on `κ(q)` and the
scalar tower through `κ(p)` by hand: neither is an instance, and the tower is exactly
`Ideal.ResidueField.map_algebraMap`, the compatibility of the canonical embedding
`κ(p) ↪ κ(q)` with the structure maps from `A` and `B`. That embedding is the structure map of
`Ideal.ResidueField.algebraOfLiesOver`, which the statement writes out rather than importing, so
that this file sits below the dimension formula it serves.

## References

* [Stacks Project, Tag 030H](https://stacks.math.columbia.edu/tag/030H)
* [Stacks Project, Tag 02IJ](https://stacks.math.columbia.edu/tag/02IJ)
-/

@[expose] public section

universe u

namespace Algebra

/-- Transcendence degree is unchanged by passing to fraction fields: if `K` is a fraction field
of the domain `A`, `L` is a fraction field of the domain `B`, and `B` is an `A`-algebra whose
structure map is injective, compatibly with `K → L`, then `trdeg K L = trdeg A B`. -/
@[ega "IV 5.5.7"]
theorem trdeg_eq_of_isFractionRing {A B K L : Type u}
    [CommRing A] [CommRing B] [Field K] [Field L] [IsDomain A] [IsDomain B]
    [Algebra A B] [Algebra A K] [Algebra B L] [Algebra K L] [Algebra A L]
    [IsFractionRing A K] [IsFractionRing B L]
    [IsScalarTower A K L] [IsScalarTower A B L] [FaithfulSMul A B] :
    Algebra.trdeg K L = Algebra.trdeg A B := by
  have h1 : Algebra.trdeg A B + Algebra.trdeg B L = Algebra.trdeg A L := trdeg_add_eq A B
  have h2 : Algebra.trdeg A K + Algebra.trdeg K L = Algebra.trdeg A L := trdeg_add_eq A K
  have : Algebra.IsAlgebraic B L := IsLocalization.isAlgebraic L (nonZeroDivisors B)
  have : Algebra.IsAlgebraic A K := IsLocalization.isAlgebraic K (nonZeroDivisors A)
  rw [trdeg_eq_zero (R := B) (A := L), add_zero] at h1
  rw [trdeg_eq_zero (R := A) (A := K), zero_add] at h2
  rw [h2, h1]

/-- The residue field extension of a prime `q` of `B` lying over a prime `p` of `A` has the same
transcendence degree as the extension `B / q` of `A / p`. -/
theorem trdeg_residueField_eq_trdeg_quotient {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] (p : Ideal A) (q : Ideal B) [p.IsPrime] [q.IsPrime] [q.LiesOver p] :
    letI : Algebra p.ResidueField q.ResidueField :=
      (Ideal.ResidueField.map p q (algebraMap A B) Ideal.LiesOver.over).toAlgebra
    Algebra.trdeg p.ResidueField q.ResidueField = Algebra.trdeg (A ⧸ p) (B ⧸ q) := by
  let : Algebra p.ResidueField q.ResidueField :=
    (Ideal.ResidueField.map p q (algebraMap A B) Ideal.LiesOver.over).toAlgebra
  let : Algebra (A ⧸ p) q.ResidueField :=
    ((algebraMap (B ⧸ q) q.ResidueField).comp (algebraMap (A ⧸ p) (B ⧸ q))).toAlgebra
  have : IsScalarTower (A ⧸ p) (B ⧸ q) q.ResidueField := .of_algebraMap_eq' rfl
  have : IsScalarTower (A ⧸ p) p.ResidueField q.ResidueField := by
    refine .of_algebraMap_eq fun y ↦ ?_
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    have h := Ideal.ResidueField.map_algebraMap p q (algebraMap A B) Ideal.LiesOver.over x
    simp only [RingHom.algebraMap_toAlgebra]
    exact h.symm
  exact trdeg_eq_of_isFractionRing

end Algebra

end
