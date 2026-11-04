module

public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.TensorProduct.Quotient
public import StacksFrontier.AlgebraicGeometry.Chow.KeyLemma.TameSymbolOrder
public import StacksFrontier.RingTheory.Length.FlatLocalHom
public import StacksFrontier.RingTheory.Flat.NonZeroDivisors

/-!
# The tame symbol under a flat local homomorphism

Let `(A, 𝔪, κ) → (A', 𝔪', κ')` be a local homomorphism of Noetherian local rings with `A → A'`
flat and `dim(A) = dim(A') = 1`, and set `m = length_{A'}(A' / 𝔪A')`. Stacks 0EPG asserts that
for nonzerodivisors `a₁, a₂ ∈ A` the element `∂_A(a₁, a₂) ^ m` of `κ` maps to `∂_{A'}(a₁, a₂)`
under `κ → κ'`.

Two of the three ingredients of that statement are established here in full generality.

* A flat ring map carries nonzerodivisors to nonzerodivisors, so `a₁` and `a₂` are again
  nonzerodivisors of `A'` and `∂_{A'}(a₁, a₂)` is defined
  (`Stacks.Chow.flatNonZeroDivisor`).
* The order of vanishing is multiplied by `m`:

  `length_{A'}(A' / x A') = m · length_A(A / xA)` for `x ∈ A`,

  which is the length identity of Stacks 02M1 applied to the `A`-module `A / xA`, whose base
  change is `A' / x A'` (`Stacks.Chow.ord_algebraMap_eq_ord_mul_length_quotient`). This is the
  numerical reason for the exponent `m` in Stacks 0EPG.

The third ingredient is the comparison of the two values of the defining formula Stacks 0EAQ.
The source obtains it by choosing a finite extension `A ⊆ B` as in Stacks 0EAG in which `a₁` and
`a₂` become unit multiples of powers of one parameter, setting `B' = A' ⊗_A B`, and comparing the
two products of norms through the determinant of an endomorphism of a finite length module (More
on Algebra 15.122). Here the comparison is carried out in the case in which that extension is
not needed, that is, when `a₁` and `a₂` already admit a simultaneous power factorization
`a₁ = u π ^ e₁`, `a₂ = v π ^ e₂` over `A` itself: both symbols are then evaluated by
`Stacks.Chow.RegularTameSymbol.apply_eq_of_factorization`, on `π` over `A` and on the image of
`π` over `A'`, and the two values differ exactly by the exponent `m` supplied by the length
identity. That case already contains the one the source disposes of first, `a₁` and `a₂` units
(take `π = 1`), and the case of a unit against an arbitrary nonzerodivisor (take `π = a₂`).

The passage through a finite extension, which a pair with no simultaneous power factorization
over `A` needs, is carried out in
`StacksFrontier.AlgebraicGeometry.Chow.KeyLemma.TameSymbolFlatBaseChangeGeneral`: there the
determinant comparison of More on Algebra 15.122 enters through
`Stacks.Length.map_norm_pow_length_eq_prod_norm_pow_length`, and Stacks 0EPG is obtained for the
value of the formula Stacks 0EAQ on an arbitrary tame-symbol preparation, hence for every pair of
nonzerodivisors of `A`.

## Main definitions

* `Stacks.Chow.flatNonZeroDivisor` — a nonzerodivisor of `A`, as a nonzerodivisor of a flat
  `A`-algebra.

## Main results

* `Stacks.Chow.ord_algebraMap_eq_ord_mul_length_quotient`,
  `Stacks.Chow.ord_toNat_algebraMap_eq_ord_toNat_mul` — the order of vanishing under a flat local
  homomorphism is multiplied by `length_{A'}(A' / 𝔪A')`.
* `Stacks.Chow.units_map_residueField_tameSymbol_pow_eq_of_factorization` — Stacks 0EPG for a
  pair admitting a simultaneous power factorization over `A`.

## Implementation notes

The multiplier `m` is carried as a natural number together with the hypothesis
`length_{A'}(A' / 𝔪A') = m`, rather than as `(length_{A'}(A' / 𝔪A')).toNat`: the finiteness of
that length follows from `dim(A) = dim(A') = 1` through the dimension formula for a flat local
homomorphism, which is not available here, while a unit of `κ` can only be raised to an integer
power.

## References

* [Stacks Project, Tag 0EPG](https://stacks.math.columbia.edu/tag/0EPG)
* [Stacks Project, Tag 02M1](https://stacks.math.columbia.edu/tag/02M1)
* [Stacks Project, Tag 0EAG](https://stacks.math.columbia.edu/tag/0EAG)
* [Stacks Project, Tag 0EAQ](https://stacks.math.columbia.edu/tag/0EAQ)
-/

@[expose] public section

open IsLocalRing

open scoped TensorProduct

universe u v

namespace Stacks.Chow

section NonZeroDivisors

variable {A : Type u} [CommRing A] (A' : Type v) [CommRing A'] [Algebra A A'] [Module.Flat A A']

/-- A nonzerodivisor of `A`, as a nonzerodivisor of a flat `A`-algebra. -/
def flatNonZeroDivisor (a : nonZeroDivisors A) : nonZeroDivisors A' :=
  ⟨algebraMap A A' (a : A), algebraMap_mem_nonZeroDivisors_of_flat a.2⟩

/-- The underlying element of `flatNonZeroDivisor A' a` is the image of `a` under
`algebraMap A A'`. -/
@[simp]
theorem flatNonZeroDivisor_val (a : nonZeroDivisors A) :
    (flatNonZeroDivisor A' a : A') = algebraMap A A' (a : A) := rfl

end NonZeroDivisors

section Order

variable {A : Type u} [CommRing A] [IsLocalRing A] {A' : Type v} [CommRing A'] [IsLocalRing A']
  [Algebra A A'] [IsLocalHom (algebraMap A A')] [Module.Flat A A']

/-- **The order of vanishing under a flat local homomorphism.** For a flat local homomorphism
`A → A'` of local rings and `x ∈ A`,

`length_{A'}(A' / x A') = length_A(A / xA) · length_{A'}(A' / 𝔪A')`.

The quotient `A' / x A'` is the base change `A' ⊗_A (A / xA)`, and the length identity of
Stacks 02M1 computes the length of a base change along a flat local homomorphism. -/
theorem ord_algebraMap_eq_ord_mul_length_quotient (x : A) :
    Ring.ord A' (algebraMap A A' x) =
      Ring.ord A x * Module.length A' (A' ⧸ extendedMaximalIdeal A A') := by
  calc Ring.ord A' (algebraMap A A' x)
      = Module.length A' (A' ⧸ Ideal.map (algebraMap A A') (Ideal.span {x})) := by
        rw [Ring.ord, Ideal.map_span, Set.image_singleton]
    _ = Module.length A' (A' ⊗[A] (A ⧸ Ideal.span {x})) :=
        (Algebra.TensorProduct.quotIdealMapEquivTensorQuot A'
          (Ideal.span {x})).toLinearEquiv.length_eq
    _ = Ring.ord A x * Module.length A' (A' ⧸ extendedMaximalIdeal A A') := by
        rw [Ring.ord, ← length_baseChange_eq_length_mul_length_quotient A A' (A ⧸ Ideal.span {x})]

variable [IsNoetherianRing A] [Ring.KrullDimLE 1 A]

/-- The order of vanishing of a nonzerodivisor under a flat local homomorphism, as a natural
number: it is multiplied by `m = length_{A'}(A' / 𝔪A')`. -/
theorem ord_toNat_algebraMap_eq_ord_toNat_mul {m : ℕ}
    (hm : Module.length A' (A' ⧸ extendedMaximalIdeal A A') = m)
    {x : A} (hx : x ∈ nonZeroDivisors A) :
    (Ring.ord A' (algebraMap A A' x)).toNat = (Ring.ord A x).toNat * m := by
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp (Ring.ord_ne_top hx)
  rw [ord_algebraMap_eq_ord_mul_length_quotient, hm, ← hk, ← Nat.cast_mul]
  simp

end Order

/-- **Stacks 0EPG for a pair with a simultaneous power factorization over the base.** Let
`(A, 𝔪, κ) → (A', 𝔪', κ')` be a flat local homomorphism of one-dimensional Noetherian local
rings and let `m = length_{A'}(A' / 𝔪A')`. If two nonzerodivisors of `A` are simultaneous unit
multiples of powers of one nonzerodivisor `π` of `A`, `a = u π ^ e` and `b = v π ^ f`, then

`∂_A(a, b) ^ m` maps to `∂_{A'}(a, b)` under `κ → κ'`.

Both symbols are evaluated by
`Stacks.Chow.RegularTameSymbol.apply_eq_of_factorization`: over `A` on the parameter `π`, and
over `A'` on the image of `π`, with the images of `u` and `v` as unit parts and the same
exponents `e` and `f`. The two resulting expressions have the same base, the image in `κ'` of
`(-1) ^ (ef) ū ^ f v̄ ^ (-e)`, and their exponents differ by exactly the factor `m`, because
`length_{A'}(A' / π A') = m · length_A(A / πA)` by
`Stacks.Chow.ord_algebraMap_eq_ord_mul_length_quotient`.

This covers the case the source's proof disposes of first, `a` and `b` both units (take
`π = 1`), and more generally a unit against a nonzerodivisor (take `π = b`, `v = 1`, `f = 1`).
It does not cover a pair for which the finite extension of Stacks 0EAG is genuinely needed. -/
@[stacks 0EPG "for a pair of nonzerodivisors admitting a simultaneous power factorization over \
`A` itself, so that the finite extension of Stacks 0EAG used by the source's proof is not \
needed; the length multiplier is Stacks 02M1"]
theorem units_map_residueField_tameSymbol_pow_eq_of_factorization
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [Ring.KrullDimLE 1 A]
    {A' : Type v} [CommRing A'] [IsNoetherianRing A'] [IsLocalRing A'] [Ring.KrullDimLE 1 A']
    [Algebra A A'] [IsLocalHom (algebraMap A A')] [Module.Flat A A']
    (symb : RegularTameSymbol A) (symb' : RegularTameSymbol A') {m : ℕ}
    (hm : Module.length A' (A' ⧸ extendedMaximalIdeal A A') = m)
    (p a b : nonZeroDivisors A) (u v : Aˣ) (e f : ℕ)
    (ha : (a : A) = u * (p : A) ^ e) (hb : (b : A) = v * (p : A) ^ f) :
    Units.map (ResidueField.map (algebraMap A A')).toMonoidHom (symb a b ^ m) =
      symb' (flatNonZeroDivisor A' a) (flatNonZeroDivisor A' b) := by
  have hneg : Units.map (ResidueField.map (algebraMap A A')).toMonoidHom
      (-1 : (ResidueField A)ˣ) = -1 := Units.ext (by simp)
  have hres (w : Aˣ) :
      Units.map (ResidueField.map (algebraMap A A')).toMonoidHom
          (Units.map (residue A).toMonoidHom w) =
        Units.map (residue A').toMonoidHom (Units.map (algebraMap A A').toMonoidHom w) :=
    Units.ext rfl
  have hfac (c : nonZeroDivisors A) (w : Aˣ) (n : ℕ) (h : (c : A) = w * (p : A) ^ n) :
      (flatNonZeroDivisor A' c : A') =
        (Units.map (algebraMap A A').toMonoidHom w : A') *
          (flatNonZeroDivisor A' p : A') ^ n := by
    simp [h]
  rw [symb.apply_eq_of_factorization p a b u v e f ha hb,
    symb'.apply_eq_of_factorization (flatNonZeroDivisor A' p) _ _
      (Units.map (algebraMap A A').toMonoidHom u) (Units.map (algebraMap A A').toMonoidHom v)
      e f (hfac a u e ha) (hfac b v f hb),
    flatNonZeroDivisor_val, ord_toNat_algebraMap_eq_ord_toNat_mul hm p.2, ← pow_mul, map_pow]
  simp only [map_mul, map_pow, map_inv, hneg, hres]

end Stacks.Chow

end
