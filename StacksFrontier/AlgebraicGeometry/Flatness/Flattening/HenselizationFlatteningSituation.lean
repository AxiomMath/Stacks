module

public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.HenselizationFlatComparison
public import StacksFrontier.RingTheory.EssentialFiniteness.BaseChange
public import StacksFrontier.RingTheory.Flat.HenselianFlatteningTheorem

/-!
# The local flattening situation over the henselization in the proof of Stacks 05U9

Claim 1 of the proof of Stacks 05U9 replaces the base `A` by its henselization `A^h`, the local
algebra `B` by the localization `B'` of `A^h ⊗_A B` at the maximal ideal
`𝔪_B ⊗ A^h + B ⊗ 𝔪_{A^h}`, and the module `N` by `N' = B' ⊗_B N`, and then applies the local
flattening theorem of Stacks 05PG over the henselian base `A^h`.

This file records that `(A^h, B', N')` is an instance of the standing data of Stacks 05MK: `B'`
is a local ring receiving a local homomorphism from `A^h`, essentially of finite type over it,
and `N'` is a finite `B'`-module, finitely presented when `N` is. It also records that `B → B'`
is faithfully flat. The maximal ideal of `A^h ⊗_A B` used is `Stacks.ResidueFibre.tensorPrime`.

## Main results

* `Stacks.ResidueFibre.isLocalHom_algebraMap_localizationTensorPrime_left` and
  `Stacks.ResidueFibre.isLocalHom_algebraMap_localizationTensorPrime_right`: `A^h → B'` and
  `B → B'` are local.
* `Stacks.ResidueFibre.faithfullyFlat_localizationTensorPrime`: `B → B'` is faithfully flat.
* `Stacks.ResidueFibre.essFiniteType_localizationTensorPrime`: `B'` is essentially of finite
  type over `A^h`.
* `Stacks.ResidueFibre.finite_tensorPrime_tensorProduct` and
  `Stacks.ResidueFibre.finitePresentation_tensorPrime_tensorProduct`: `N'` is finite, resp. of
  finite presentation, over `B'`.
* `Stacks.ResidueFibre.flatAtPointSituation`: the resulting instance of Stacks 05MK.

## Implementation notes

The right `B`-algebra structure on `A^h ⊗_A B` (`Algebra.TensorProduct.rightAlgebra`) is enabled
locally, as Mathlib does not make it an instance.

## References

* [Stacks Project, Tag 05U9](https://stacks.math.columbia.edu/tag/05U9)
* [Stacks Project, Tag 05MK](https://stacks.math.columbia.edu/tag/05MK)
* [Stacks Project, Tag 05PG](https://stacks.math.columbia.edu/tag/05PG)
-/

@[expose] public section

universe u v w

open IsLocalRing TensorProduct

namespace Stacks.ResidueFibre

section Situation

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {A : Type u} [CommRing A] [IsLocalRing A]
variable {B : Type v} [CommRing B] [IsLocalRing B] [Algebra A B]
  [IsLocalHom (algebraMap A B)]
variable (Ah : Type u) [CommRing Ah] [IsLocalRing Ah] [Algebra A Ah]
  [IsLocalRing.IsHenselization A (ResidueField A) Ah]

/-- **The structure map `A^h → B'` is local.** -/
instance isLocalHom_algebraMap_localizationTensorPrime_left :
    IsLocalHom
      (algebraMap Ah (Localization.AtPrime (tensorPrime (A := A) (B := B) Ah))) := by
  have : (tensorPrime (A := A) (B := B) Ah).IsPrime := (tensorPrime_isMaximal Ah).isPrime
  refine ((local_hom_TFAE
    (algebraMap Ah (Localization.AtPrime (tensorPrime (A := A) (B := B) Ah)))).out 5 1).mp ?_
  have hB' : (maximalIdeal (Localization.AtPrime (tensorPrime (A := A) (B := B) Ah))).comap
      (algebraMap (Ah ⊗[A] B) (Localization.AtPrime (tensorPrime (A := A) (B := B) Ah))) =
      tensorPrime (A := A) (B := B) Ah := Localization.AtPrime.under_maximalIdeal
  rw [IsScalarTower.algebraMap_eq Ah (Ah ⊗[A] B)
      (Localization.AtPrime (tensorPrime (A := A) (B := B) Ah)),
    ← Ideal.comap_comap, hB', tensorPrime_comap_left]

/-- **The structure map `B → B'` is local.** -/
instance isLocalHom_algebraMap_localizationTensorPrime_right :
    IsLocalHom
      (algebraMap B (Localization.AtPrime (tensorPrime (A := A) (B := B) Ah))) := by
  have : (tensorPrime (A := A) (B := B) Ah).IsPrime := (tensorPrime_isMaximal Ah).isPrime
  refine ((local_hom_TFAE
    (algebraMap B (Localization.AtPrime (tensorPrime (A := A) (B := B) Ah)))).out 5 1).mp ?_
  have hB' : (maximalIdeal (Localization.AtPrime (tensorPrime (A := A) (B := B) Ah))).comap
      (algebraMap (Ah ⊗[A] B) (Localization.AtPrime (tensorPrime (A := A) (B := B) Ah))) =
      tensorPrime (A := A) (B := B) Ah := Localization.AtPrime.under_maximalIdeal
  rw [IsScalarTower.algebraMap_eq B (Ah ⊗[A] B)
      (Localization.AtPrime (tensorPrime (A := A) (B := B) Ah)),
    ← Ideal.comap_comap, hB', tensorPrime_comap_right]

/-- **`B → B'` is faithfully flat.** -/
theorem faithfullyFlat_localizationTensorPrime :
    Module.FaithfullyFlat B
      (Localization.AtPrime (tensorPrime (A := A) (B := B) Ah)) := by
  have : (tensorPrime (A := A) (B := B) Ah).IsPrime := (tensorPrime_isMaximal Ah).isPrime
  have : IsLocalHom (algebraMap A Ah) :=
    IsLocalRing.IsHenselization.isLocalHom (L := ResidueField A)
  have : Module.Flat A Ah := IsLocalRing.IsHenselization.flat (L := ResidueField A)
  have : Module.Flat B (Ah ⊗[A] B) := by
    have hsym : Algebra.IsPushout A B Ah (Ah ⊗[A] B) := Algebra.IsPushout.symm inferInstance
    exact Module.Flat.of_linearEquiv
      (Algebra.IsPushout.equiv A B Ah (Ah ⊗[A] B)).symm.toLinearEquiv
  have : Module.Flat B (Localization.AtPrime (tensorPrime (A := A) (B := B) Ah)) :=
    Module.Flat.trans B (Ah ⊗[A] B) _
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

/-- **`B'` is essentially of finite type over `A^h`** when `B` is essentially of finite type
over `A`. -/
theorem essFiniteType_localizationTensorPrime [Algebra.EssFiniteType A B] :
    Algebra.EssFiniteType Ah
      (Localization.AtPrime (tensorPrime (A := A) (B := B) Ah)) :=
  inferInstance

/-- **`A^h → B'` is essentially of finite presentation when `A → B` is.** -/
theorem essentiallyOfFinitePresentation_algebraMap_localizationTensorPrime
    (hB : (algebraMap A B).EssentiallyOfFinitePresentation) :
    (algebraMap Ah
      (Localization.AtPrime (tensorPrime (A := A) (B := B) Ah))).EssentiallyOfFinitePresentation :=
  by
  have : (tensorPrime (A := A) (B := B) Ah).IsPrime := (tensorPrime_isMaximal Ah).isPrime
  have hloc : (algebraMap (Ah ⊗[A] B)
      (Localization.AtPrime (tensorPrime (A := A) (B := B) Ah))).EssentiallyOfFinitePresentation :=
    RingHom.EssentiallyOfFinitePresentation.of_isLocalization (C := Ah ⊗[A] B)
      (tensorPrime (A := A) (B := B) Ah).primeCompl
  rw [IsScalarTower.algebraMap_eq Ah (Ah ⊗[A] B)
    (Localization.AtPrime (tensorPrime (A := A) (B := B) Ah))]
  exact essFinitePresentation_comp
    (RingHom.EssentiallyOfFinitePresentation.baseChange_algebraMap (S := Ah) hB) hloc

variable (N : Type w) [AddCommGroup N] [Module B N]

/-- **`N' = B' ⊗_B N` is a finite `B'`-module.** -/
theorem finite_tensorPrime_tensorProduct [Module.Finite B N] :
    Module.Finite (Localization.AtPrime (tensorPrime (A := A) (B := B) Ah))
      (Localization.AtPrime (tensorPrime (A := A) (B := B) Ah) ⊗[B] N) :=
  inferInstance

/-- **`N' = B' ⊗_B N` is of finite presentation over `B'` when `N` is over `B`.** -/
theorem finitePresentation_tensorPrime_tensorProduct [Module.FinitePresentation B N] :
    Module.FinitePresentation (Localization.AtPrime (tensorPrime (A := A) (B := B) Ah))
      (Localization.AtPrime (tensorPrime (A := A) (B := B) Ah) ⊗[B] N) :=
  inferInstance

/-- **The standing data of Stacks 05MK over the henselization, in the proof of Stacks 05U9.**
The base is the henselization `A^h`, the local algebra is the localization `B'` of `A^h ⊗_A B`
at `Stacks.ResidueFibre.tensorPrime`, and the module is `N' = B' ⊗_B N`. -/
noncomputable def flatAtPointSituation : Module.FlatAtPointSituation.{u, max u v, max u v w} where
  A := Ah
  B := Localization.AtPrime (tensorPrime (A := A) (B := B) Ah)
  M := Localization.AtPrime (tensorPrime (A := A) (B := B) Ah) ⊗[B] N

/-- The base ring of `flatAtPointSituation` is the henselization `A^h`. -/
@[simp]
theorem flatAtPointSituation_A : (flatAtPointSituation (A := A) (B := B) Ah N).A = Ah := rfl

/-- The local algebra of `flatAtPointSituation` is the localization `B'` of `A^h ⊗_A B` at the
prime `Stacks.ResidueFibre.tensorPrime`. -/
@[simp]
theorem flatAtPointSituation_B : (flatAtPointSituation (A := A) (B := B) Ah N).B =
    Localization.AtPrime (tensorPrime (A := A) (B := B) Ah) := rfl

/-- The module of `flatAtPointSituation` is `N' = B' ⊗_B N`. -/
@[simp]
theorem flatAtPointSituation_M : (flatAtPointSituation (A := A) (B := B) Ah N).M =
    Localization.AtPrime (tensorPrime (A := A) (B := B) Ah) ⊗[B] N := rfl

end Situation

end Stacks.ResidueFibre

end
