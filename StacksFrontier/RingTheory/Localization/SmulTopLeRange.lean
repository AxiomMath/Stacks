module

public import Mathlib.RingTheory.LocalProperties.Submodule
public import StacksCore.RingTheory.Localization.Ideal
public import StacksFrontier.RingTheory.Localization.RangeAlgebraLinearMap

/-!
# A multiple of an algebra lying in the base ring, checked one maximal ideal at a time

Let `A → B` be a map of commutative rings and let `I` be an ideal of `A`. The containment

`I • B ⊆ A`,

which says that `I` lies in the conductor of `A` in `B`, is a statement about the `A`-module
`B / A`, hence local on `Spec A`: it holds as soon as it holds after localizing at every maximal
ideal `P` of `A`, where it reads

`(I A_P) • (B ⊗_A A_P) ⊆ A_P`.

That is the content of this file. Both sides localize by a result already available: the left
one by `Submodule.localized'_smul_top`, the right one — the image of `A` in `B` — by
`Submodule.localized'_range_algebraLinearMap`, and `Submodule.le_of_localization_maximal`
assembles the local containments into the global one.

The reason this is worth isolating is that the two sides of the local containment are
qualitatively different from the global ones. For a curve the module `B / A` is supported at
finitely many closed points; at a point in the support the local containment is a computation in
a one-dimensional local ring, and at every other point the image of `A_P` is already everything,
so there is nothing to check at all. The global containment has no such case division, and
reaching it directly would require knowing the support.

## Main results

* `Submodule.smul_top_le_range_algebraLinearMap_of_localization_maximal`: `I • B ≤ A` follows
  from the same containment at every maximal ideal of `A`.

## Implementation notes

The localization of `B` at a maximal ideal `P` of `A` is spelled
`Localization (Algebra.algebraMapSubmonoid B P.primeCompl)`, the localization of `B` at the image
of `P.primeCompl`; its `Localization.AtPrime P`-algebra structure is Mathlib's
`localizationAlgebra` instance, and the localization map `B → B_P` is
`(IsScalarTower.toAlgHom A B _).toLinearMap`, the spelling under which Mathlib supplies the
`IsLocalizedModule P.primeCompl` instance. These are the choices
`Submodule.localized'_range_algebraLinearMap` is stated with, so no comparison map has to be
moved across.
-/

@[expose] public section

namespace Submodule

/-- **An ideal multiple of an algebra lies in the base ring as soon as it does locally.** Let
`B` be an algebra over `A` and `I` an ideal of `A`. If for every maximal ideal `P` of `A` the
extension of `I` to `A_P` carries the localization of `B` into the image of `A_P`, then `I`
carries `B` into the image of `A`.

Equivalently: `I` lies in the conductor of `A` in `B` as soon as it lies in the conductor of
`A_P` in `B ⊗_A A_P` for every maximal ideal `P`. -/
theorem smul_top_le_range_algebraLinearMap_of_localization_maximal
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] {I : Ideal A}
    (h : ∀ (P : Ideal A) [P.IsMaximal],
      I.map (algebraMap A (Localization.AtPrime P)) •
          (⊤ : Submodule (Localization.AtPrime P)
            (Localization (Algebra.algebraMapSubmonoid B P.primeCompl))) ≤
        LinearMap.range (Algebra.linearMap (Localization.AtPrime P)
          (Localization (Algebra.algebraMapSubmonoid B P.primeCompl)))) :
    I • (⊤ : Submodule A B) ≤ LinearMap.range (Algebra.linearMap A B) := by
  refine le_of_localization_maximal
    (fun P _ => Localization (Algebra.algebraMapSubmonoid B P.primeCompl))
    (fun P _ => (IsScalarTower.toAlgHom A B
      (Localization (Algebra.algebraMapSubmonoid B P.primeCompl))).toLinearMap)
    fun P _ => ?_
  simp only [← restrictScalars_localized' (Localization.AtPrime P) P.primeCompl
      (IsScalarTower.toAlgHom A B
        (Localization (Algebra.algebraMapSubmonoid B P.primeCompl))).toLinearMap,
    localized'_smul_top, localized'_range_algebraLinearMap]
  exact fun _ hy => h P hy

end Submodule

end
