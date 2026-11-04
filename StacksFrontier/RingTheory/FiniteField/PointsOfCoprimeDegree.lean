module

public import StacksFrontier.FieldTheory.Finite.CoprimeDegreeExtension
public import StacksFrontier.RingTheory.FiniteField.PointsOfLargeDegree
public import StacksFrontier.RingTheory.GeometricallyIrreducible.Subalgebra

/-!
# Points of prescribed degree on geometrically irreducible algebras over finite fields

Let `k` be a finite field and `A` a geometrically irreducible `k`-algebra of finite type. By the
Lang–Weil estimates, in the form
`Algebra.exists_forall_nonempty_algHom_of_isGeometricallyIrreducible`, there is a `k`-algebra map
from `A` to every large enough finite extension of `k`. This module records the two forms in which
Stacks Remark 0BA7 uses that:

* for `n ≫ 0` there is a `k`-algebra map `A → k'` with `[k' : k] = n`;
* every finitely generated `k`-subalgebra of a geometrically irreducible `k`-algebra maps to a
  finite extension of `k` of degree prime to any given integer, which is the input of the argument
  of Stacks Lemma 0B85 for a finite ground field.

## Main results

* `Algebra.exists_forall_nonempty_algHom_of_le_finrank_of_isGeometricallyIrreducible`
* `Algebra.IsGeometricallyIrreducible.exists_finrank_coprime_algHom_of_fg`

## References

* [Stacks Project, Tag 0B85](https://stacks.math.columbia.edu/tag/0B85)
* [Stacks Project, Tag 0BA7](https://stacks.math.columbia.edu/tag/0BA7)
-/

@[expose] public section

universe u

open Module

namespace Algebra

/-- **Points of every large degree.** A geometrically irreducible algebra `A` of finite type over a
finite field `k` has a `k`-algebra map `A → k'` to every finite extension `k'` of `k` of degree
`[k' : k] ≥ N`, for some `N`. -/
theorem exists_forall_nonempty_algHom_of_le_finrank_of_isGeometricallyIrreducible
    (k A : Type u) [Field k] [Finite k] [CommRing A] [Algebra k A] [Algebra.FiniteType k A]
    (hA : Algebra.IsGeometricallyIrreducible k A) :
    ∃ N : ℕ, ∀ (k' : Type u) [Field k'] [Algebra k k'] [FiniteDimensional k k'],
      N ≤ finrank k k' → Nonempty (A →ₐ[k] k') := by
  obtain ⟨N, hN⟩ := exists_forall_nonempty_algHom_of_isGeometricallyIrreducible k A hA
  refine ⟨N + 1, fun k' _ _ _ hn => ?_⟩
  have : Finite k' := Module.finite_of_finite k
  refine hN k' ?_
  calc N < finrank k k' := by omega
    _ < 2 ^ finrank k k' := Nat.lt_two_pow_self
    _ ≤ Nat.card k ^ finrank k k' := Nat.pow_le_pow_left Finite.one_lt_card _
    _ = Nat.card k' := Module.natCard_eq_pow_finrank.symm

/-- **Points of degree prime to `d`.** Let `S` be a geometrically irreducible algebra over a finite
field `k`. Every finitely generated `k`-subalgebra `A` of `S` has a `k`-algebra map to a finite
field extension of `k` whose degree is prime to any given `d > 0`. -/
theorem IsGeometricallyIrreducible.exists_finrank_coprime_algHom_of_fg {k S : Type u} [Field k]
    [Finite k] [CommRing S] [Algebra k S] (hS : Algebra.IsGeometricallyIrreducible k S)
    (A : Subalgebra k S) (hA : A.FG) (d : ℕ) (hd : 0 < d) :
    ∃ (L : Type u) (_ : Field L) (_ : Finite L) (_ : Algebra k L),
      Nat.Coprime (finrank k L) d ∧ Nonempty (A →ₐ[k] L) := by
  have : Algebra.FiniteType k A := (Subalgebra.fg_iff_finiteType A).mp hA
  obtain ⟨N, hN⟩ := exists_forall_nonempty_algHom_of_isGeometricallyIrreducible k A
    (isGeometricallyIrreducible_of_subalgebra k S hS A)
  obtain ⟨L, hL, hLf, hLa, hcop, hcard⟩ := FiniteField.exists_finrank_coprime_lt_card k N d hd
  exact ⟨L, hL, hLf, hLa, hcop, hN L hcard⟩

end Algebra
