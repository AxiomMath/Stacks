module

public import Mathlib.FieldTheory.FinTrdeg
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
# Finiteness of the residue-field transcendence degree of a finite type algebra

Let `R → T` be of finite type, let `𝔮 ⊂ T` be a prime and `𝔭 ⊂ R` a prime below it. Then
`κ(𝔮)` is essentially of finite type over `κ(𝔭)`, hence the transcendence degree
`trdeg_{κ(𝔭)} κ(𝔮)` is a natural number.

This is the second numerical input of Stacks 0520 — alongside the relative dimension — and
therefore of Stacks 052E: the integer `r` of `(𝔭, x_{r+1}, …, x_n)` is this transcendence
degree, and the statement of 0520 requires it as a natural number.

## Main results

* `Algebra.essFiniteType_residueField_of_finiteType`: `κ(𝔮)` is essentially of finite type over
  `R`, for `R → T` of finite type.
* `Algebra.exists_trdeg_residueField_eq_natCast`: the transcendence degree of `κ(𝔮)` over
  `κ(𝔭)` is a natural number.

## Implementation notes

`κ(𝔮)` is a quotient of `Localization.AtPrime 𝔮`, which is essentially of finite type over `R`
whenever `T` is; essential finiteness passes to quotients by
`Algebra.EssFiniteType.of_surjective`, and descends along the tower `R → κ(𝔭) → κ(𝔮)` by
`Algebra.EssFiniteType.of_comp`. Finiteness of the transcendence degree then follows from the
instance `FinTrdeg` attached to `Algebra.EssFiniteType` and `Cardinal.lt_aleph0`.

The `κ(𝔭)`-algebra structure on `κ(𝔮)` and its compatibility with `R` are hypotheses, exactly
as in the statement of Stacks 0520 in `StacksFrontier/RingTheory/RelativeDimension/QuasiFiniteAffineSpace.lean`.

## References

* [Stacks Project, Tag 0520](https://stacks.math.columbia.edu/tag/0520)
* [Stacks Project, Tag 052E](https://stacks.math.columbia.edu/tag/052E)
-/

@[expose] public section

namespace Algebra

variable {R T : Type*} [CommRing R] [CommRing T] [Algebra R T]

/-- The residue field at a prime of a finite type algebra is essentially of finite type over the
base ring. -/
theorem essFiniteType_residueField_of_finiteType [Algebra.FiniteType R T]
    (q : Ideal T) [q.IsPrime] :
    Algebra.EssFiniteType R q.ResidueField :=
  Algebra.EssFiniteType.of_surjective
    (IsScalarTower.toAlgHom R (Localization.AtPrime q) q.ResidueField)
    IsLocalRing.residue_surjective

/-- **The transcendence-degree input of Stacks 0520.** For `R → T` of finite type and primes
`𝔮 ⊂ T`, `𝔭 ⊂ R` with a compatible residue-field extension, the transcendence degree of `κ(𝔮)`
over `κ(𝔭)` is a natural number. -/
theorem exists_trdeg_residueField_eq_natCast [Algebra.FiniteType R T]
    (p : Ideal R) [p.IsPrime] (q : Ideal T) [q.IsPrime]
    [Algebra p.ResidueField q.ResidueField] [IsScalarTower R p.ResidueField q.ResidueField] :
    ∃ r : ℕ, Algebra.trdeg p.ResidueField q.ResidueField = r := by
  have hR : Algebra.EssFiniteType R q.ResidueField :=
    essFiniteType_residueField_of_finiteType q
  have hk : Algebra.EssFiniteType p.ResidueField q.ResidueField :=
    Algebra.EssFiniteType.of_comp R p.ResidueField q.ResidueField
  exact Cardinal.lt_aleph0.mp (trdeg_lt_aleph0 _ _)

end Algebra
