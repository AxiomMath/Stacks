module

public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import StacksFrontier.Algebra.Homology.ProjectiveDimension
public import StacksFrontier.RingTheory.GlobalDimension.Defs
public import StacksFrontier.RingTheory.PseudoCoherentMap.PerfectPresentation
import all StacksFrontier.RingTheory.PseudoCoherentMap.PerfectPresentation

/-!
# The fibres of a localization of a polynomial algebra

Let `A` be a commutative ring, let `q` be a prime of `P = A[x_1, …, x_n]` and let `P_q` be the
localization of `P` at `q`. Every fibre of `A → P_q`, that is every ring `P_q ⊗_A κ(p)` for `p` a
prime of `A`, has global dimension at most `n`.

This is the hypothesis [stacks 068X] needs in order to be applied to `A → P_q`, which is how the
source's proof of [stacks 069C] makes the localization of the target at a prime of a polynomial
presentation perfect. The fibre of `A → P` is a polynomial algebra in `n` variables over a field,
so has global dimension at most `n` by `RingHom.polynomial_fibre_globalDimension_le`; the fibre of
`A → P_q` is a localization of it, by `IsLocalization.tensorProduct_tensorProduct`, and
localization does not raise global dimension, which is [stacks 00O8] (2).

## Main results

* `RingHom.ringGlobalDimension_le_of_isLocalization`: [stacks 00O8] (2) at an arbitrary model of
  the localization rather than at `Localization`.
* `RingHom.polynomial_localization_fibre_globalDimension_le`: the fibre bound itself.

## Implementation notes

`StacksFrontier.Algebra.Homology.ProjectiveDimension` states [stacks 00O8] (2) as
`ringGlobalDimension_localization_le`, for `Localization`, and also as
`globalDimension_localization_le` in the vocabulary `RingGlobalDimensionLE`, which quantifies over
all modules; the two are the same statement by `CategoryTheory.projectiveDimension_le_iff`. The
first result below carries it to an arbitrary model of the localization through
`IsLocalization.algEquiv` and `RingHom.ringGlobalDimension_le_of_ringEquiv`.

`RingHom.polynomial_fibre_globalDimension_le` and
`RingHom.ringGlobalDimension_le_of_ringEquiv` live in
`StacksFrontier.RingTheory.PseudoCoherentMap.PerfectPresentation` and are public, so that module is
imported rather than reached by `import all`.

The algebra structure of the fibre of `A → P_q` over the fibre of `A → P` is not an instance:
`Algebra.TensorProduct.map` applied to `P → P_q` and the identity of `κ(p)` supplies it, and the
two side conditions `IsLocalization.tensorProduct_tensorProduct` asks for — that the structure
map is the identity on the right factor and that it is compatible with the `P`-algebra structures
— are checked on generators.

## References

* [The Stacks Project, Lemma 15.83.1 (068X)](https://stacks.math.columbia.edu/tag/068X)
* [The Stacks Project, Lemma 13.27.2 (00O8)](https://stacks.math.columbia.edu/tag/00O8)
* [The Stacks Project, Lemma 37.61.11 (069C)](https://stacks.math.columbia.edu/tag/069C)
-/

@[expose] public section

universe u

open CategoryTheory

open scoped TensorProduct

namespace RingHom

/-- Global dimension does not grow under localization, for an arbitrary model of the
localization. -/
public theorem ringGlobalDimension_le_of_isLocalization {R : Type u} [CommRing R]
    (M : Submonoid R) (T : Type u) [CommRing T] [Algebra R T] [IsLocalization M T] (n : ℕ)
    (h : ringGlobalDimension R ≤ (n : ℕ)) : ringGlobalDimension T ≤ (n : ℕ) := by
  have hR : RingGlobalDimensionLE R n := fun X =>
    (projectiveDimension_le_iff X n).mp (le_trans (le_iSup
      (fun N : ModuleCat.{u} R => projectiveDimension N) X) h)
  have hL : ringGlobalDimension (Localization M) ≤ (n : ℕ) :=
    iSup_le fun X => (projectiveDimension_le_iff X n).mpr
      (globalDimension_localization_le R M n hR X)
  exact ringGlobalDimension_le_of_ringEquiv
    (IsLocalization.algEquiv M T (Localization M)).toRingEquiv _ hL

/-- Every fibre of the localization `A[x_1, …, x_n]_q` at a prime `q` over `A` has global
dimension at most `n`: the fibre is a localization of the corresponding fibre of
`A[x_1, …, x_n]`, which is a polynomial algebra in `n` variables over a field. -/
public theorem polynomial_localization_fibre_globalDimension_le (A : Type u) [CommRing A] (n : ℕ)
    (q : Ideal (MvPolynomial (Fin n) A)) [q.IsPrime] (p : PrimeSpectrum A) :
    ringGlobalDimension
        (TensorProduct A (Localization.AtPrime q) p.asIdeal.ResidueField) ≤ (n : ℕ) := by
  have hC : ∀ y : A, (algebraMap (MvPolynomial (Fin n) A) (Localization.AtPrime q))
      (MvPolynomial.C y) = algebraMap A (Localization.AtPrime q) y := fun y => by
    rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
  let alg : Algebra (MvPolynomial (Fin n) A ⊗[A] p.asIdeal.ResidueField)
      (Localization.AtPrime q ⊗[A] p.asIdeal.ResidueField) :=
    (Algebra.TensorProduct.map
      (IsScalarTower.toAlgHom A (MvPolynomial (Fin n) A) (Localization.AtPrime q))
      (AlgHom.id A p.asIdeal.ResidueField)).toRingHom.toAlgebra
  have H : (algebraMap (MvPolynomial (Fin n) A ⊗[A] p.asIdeal.ResidueField)
        (Localization.AtPrime q ⊗[A] p.asIdeal.ResidueField)).comp
        Algebra.TensorProduct.includeRight.toRingHom =
      Algebra.TensorProduct.includeRight.toRingHom := by
    ext x
    simp [RingHom.algebraMap_toAlgebra, Algebra.TensorProduct.map]
  have : IsScalarTower (MvPolynomial (Fin n) A)
      (MvPolynomial (Fin n) A ⊗[A] p.asIdeal.ResidueField)
      (Localization.AtPrime q ⊗[A] p.asIdeal.ResidueField) := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    ext x
    · simp [RingHom.algebraMap_toAlgebra, Algebra.TensorProduct.map, hC]
    · simp [RingHom.algebraMap_toAlgebra, Algebra.TensorProduct.map]
  have := IsLocalization.tensorProduct_tensorProduct A p.asIdeal.ResidueField
    q.primeCompl (Localization.AtPrime q) H
  exact ringGlobalDimension_le_of_isLocalization
    (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) A ⊗[A] p.asIdeal.ResidueField)
      q.primeCompl)
    (Localization.AtPrime q ⊗[A] p.asIdeal.ResidueField) n
    (RingHom.polynomial_fibre_globalDimension_le A n p)

end RingHom

end
