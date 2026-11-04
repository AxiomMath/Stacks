module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import StacksFrontier.RingTheory.Etale.ResidueFieldColimit

/-!
# Étale extraction of Artin–Schreier roots

For a commutative ring `A` of characteristic `p` and an element `a` of `A`, the algebra
`A[X]/(X ^ p - X - a)` is étale over `A`, free of rank `p` as an `A`-module, surjective on prime
spectra, and contains a root of `X ^ p - X - a`. This says precisely that the Artin–Schreier map
`x ↦ x ^ p - x` on `𝐆_a` is surjective étale-locally, and it is the only non-formal input to the
exactness of the Artin–Schreier sequence `0 → 𝐙/p𝐙 → 𝐆_a → 𝐆_a → 0` on the étale site.

## Main results

* `Stacks.ArtinSchreier.etale_adjoinRootAS`: the étaleness.
* `Stacks.ArtinSchreier.root_pow_sub_root`: the adjoined root solves `x ^ p - x = a`.
* `Stacks.ArtinSchreier.comap_surjective_adjoinRootAS`: surjectivity on prime spectra, so that
  the corresponding morphism of affine schemes is an étale covering.

## Implementation notes

The algebra is `AdjoinRoot (X ^ p - X - Polynomial.C a)`; no new definition is introduced for it,
so that the whole Mathlib `AdjoinRoot` API applies unchanged.

Étaleness comes from `Stacks.Etale.ResidueFieldColimit.etale_adjoinRoot`, which asks for a monic
polynomial whose derivative is a unit in the quotient. Here the derivative is
`p * X ^ (p - 1) - 1 = -1`, a unit unconditionally: this is where the characteristic hypothesis
enters, and it is the only place. In contrast with the Kummer polynomial `X ^ n - u` there is no
invertibility condition on the exponent and no unit hypothesis on `a`.

Surjectivity on prime spectra is deduced from faithful flatness, which for a free module is the
statement that it is nonzero. That fails when `A` is the zero ring, where the prime spectrum is
empty and the conclusion is vacuous; the two cases are separated in the proof so that the
statement itself carries no nontriviality hypothesis.

## References

* [Stacks Project, Tag 0A3J](https://stacks.math.columbia.edu/tag/0A3J): the Artin–Schreier
  sequence, whose exactness on the right is the content of this file.
* [Stacks Project, Tag 09E0](https://stacks.math.columbia.edu/tag/09E0): étaleness of a monogenic
  algebra with invertible derivative.
-/

@[expose] public noncomputable section

open Polynomial

universe u

namespace Stacks.ArtinSchreier

variable {A : Type u} [CommRing A] {p : ℕ}

/-- The degree of `X + a` is less than `p` for `p > 1`. -/
theorem degree_X_add_C_lt (a : A) (hp : 1 < p) : (X + C a : A[X]).degree < (p : ℕ) :=
  lt_of_le_of_lt ((degree_add_le _ _).trans
    (max_le degree_X_le (degree_C_le.trans zero_le_one))) (by exact_mod_cast hp)

/-- The Artin–Schreier polynomial `X ^ p - X - a` is monic for `p > 1`. -/
theorem monic_artinSchreier (a : A) (hp : 1 < p) : (X ^ p - X - C a).Monic := by
  rw [sub_sub]
  exact monic_X_pow_sub (degree_X_add_C_lt a hp)

/-- The Artin–Schreier polynomial has degree `p` over a nonzero ring. -/
theorem degree_artinSchreier [Nontrivial A] (a : A) (hp : 1 < p) :
    (X ^ p - X - C a : A[X]).degree = p := by
  rw [sub_sub, degree_sub_eq_left_of_degree_lt
    (by rw [degree_X_pow]; exact degree_X_add_C_lt a hp), degree_X_pow]

/-- The derivative of `X ^ p - X - a` is `-1` in characteristic `p`: the term `p * X ^ (p - 1)`
coming from `X ^ p` vanishes. -/
theorem derivative_artinSchreier (a : A) (hchar : (p : A) = 0) :
    derivative (X ^ p - X - C a) = -1 := by
  simp [derivative_X_pow, hchar]

/-- The derivative of `X ^ p - X - a` is a unit in `A[X]/(X ^ p - X - a)`, being `-1`. -/
theorem isUnit_mk_derivative_artinSchreier (a : A) (hchar : (p : A) = 0) :
    IsUnit (AdjoinRoot.mk (X ^ p - X - C a) (derivative (X ^ p - X - C a))) := by
  rw [derivative_artinSchreier a hchar]
  simp

/-- **Étale extraction of an Artin–Schreier root.** For `A` of characteristic `p > 1` and `a` in
`A`, the algebra `A[X]/(X ^ p - X - a)` is étale over `A`. -/
theorem etale_adjoinRootAS (a : A) (hp : 1 < p) (hchar : (p : A) = 0) :
    Algebra.Etale A (AdjoinRoot (X ^ p - X - C a)) :=
  Stacks.Etale.ResidueFieldColimit.etale_adjoinRoot (monic_artinSchreier a hp)
    (isUnit_mk_derivative_artinSchreier a hchar)

/-- `A[X]/(X ^ p - X - a)` is a free `A`-module. -/
theorem free_adjoinRootAS (a : A) (hp : 1 < p) :
    Module.Free A (AdjoinRoot (X ^ p - X - C a)) :=
  (monic_artinSchreier a hp).free_adjoinRoot

/-- `A[X]/(X ^ p - X - a)` is a finite `A`-module. -/
theorem finite_adjoinRootAS (a : A) (hp : 1 < p) :
    Module.Finite A (AdjoinRoot (X ^ p - X - C a)) :=
  (monic_artinSchreier a hp).finite_adjoinRoot

/-- **The adjoined root solves the Artin–Schreier equation**: it satisfies `x ^ p - x = a`. -/
theorem root_pow_sub_root (a : A) :
    AdjoinRoot.root (X ^ p - X - C a) ^ p - AdjoinRoot.root (X ^ p - X - C a) =
      algebraMap A (AdjoinRoot (X ^ p - X - C a)) a := by
  have h : (AdjoinRoot.mk (X ^ p - X - C a)) (X ^ p - X - C a) = 0 := AdjoinRoot.mk_self
  rw [← AdjoinRoot.aeval_eq, map_sub, map_sub, map_pow, aeval_X, aeval_C, sub_eq_zero] at h
  exact h

/-- `A[X]/(X ^ p - X - a)` is faithfully flat over a nonzero `A`: it is free, and free of
positive rank. -/
theorem faithfullyFlat_adjoinRootAS [Nontrivial A] (a : A) (hp : 1 < p) :
    Module.FaithfullyFlat A (AdjoinRoot (X ^ p - X - C a)) :=
  have := free_adjoinRootAS a hp
  have : Nontrivial (AdjoinRoot (X ^ p - X - C a)) :=
    (AdjoinRoot.nontrivial_iff_of_monic (monic_artinSchreier a hp)).mpr <| by
      rw [degree_artinSchreier a hp]
      exact_mod_cast Nat.zero_lt_of_lt hp
  inferInstance

/-- The morphism of prime spectra induced by `A → A[X]/(X ^ p - X - a)` is surjective, so that
together with `Stacks.ArtinSchreier.etale_adjoinRootAS` it is an étale covering of `Spec A`. -/
theorem comap_surjective_adjoinRootAS (a : A) (hp : 1 < p) :
    Function.Surjective
      (PrimeSpectrum.comap (algebraMap A (AdjoinRoot (X ^ p - X - C a)))) := by
  rcases subsingleton_or_nontrivial A with h | h
  · exact fun q => isEmptyElim q
  · have := faithfullyFlat_adjoinRootAS a hp
    exact PrimeSpectrum.comap_surjective_of_faithfullyFlat

end Stacks.ArtinSchreier

end
