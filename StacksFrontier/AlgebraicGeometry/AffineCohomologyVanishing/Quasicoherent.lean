module

public import StacksFrontier.AlgebraicGeometry.AffinePushforward.Basic
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.AlgebraicGeometry.HigherDirectImage.Basic
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Quasi-coherence of the higher direct images along an affine morphism

Let `f : X ⟶ S` be an affine morphism of schemes and let `F` be a quasi-coherent `𝒪_X`-module.
This file assembles the statement that `Rᵖ f_* F` is quasi-coherent **in every degree**, which
is the affine case of [Stacks, Tag 01XJ], from three facts that are already available:

* for `p < 0` the higher direct image vanishes, with no hypothesis at all
  (`Stacks.AlgebraicGeometry.HigherDirectImage.isQuasicoherent_higherDirectImage_of_neg`);
* for `p = 0` it is the direct image `f_* F`, which is quasi-coherent along an affine morphism
  by [Stacks, Tag 02KG]
  (`Stacks.AlgebraicGeometry.AffinePushforward.pushforward_isQuasicoherent_of_isAffineHom`);
* for `p > 0` it vanishes by [Stacks, Tag 01XC]
  (`Stacks.Cohomology.Affine.HigherDirectImage.isZero_rightDerived_pushforward_of_isAffineHom`),
  and a zero sheaf of modules is quasi-coherent.

Both indexings of the higher right derived functors are covered. The `ℤ`-indexed
`CategoryTheory.Functor.rightDerivedPlus` is the one Tag 01XC is stated for in this
repository; Mathlib's `ℕ`-indexed `CategoryTheory.Functor.rightDerived` is the one that
consumers in the chapter on limits of schemes use, and the two are compared by
`Stacks.DerivedIndexing.rightDerivedIso`.

## Main results

* `Stacks.Cohomology.Affine.HigherDirectImage.isZero_rightDerivedNat_pushforward_of_isAffineHom`
  is [Stacks, Tag 01XC] for Mathlib's `ℕ`-indexed `CategoryTheory.Functor.rightDerived`.
* `isQuasicoherent_rightDerivedPlus_pushforward_of_isAffineHom` and
  `isQuasicoherent_rightDerivedNat_pushforward_of_isAffineHom`, both in
  `Stacks.Cohomology.Affine.HigherDirectImage`, are the affine case of [Stacks, Tag 01XJ], in
  the `ℤ`-indexing and in the `ℕ`-indexing respectively.

## Implementation notes

`Nat` in a name means Mathlib's `ℕ`-indexed `CategoryTheory.Functor.rightDerived`. The
distinction has to be made explicitly, because in
`Stacks.Cohomology.Affine.HigherDirectImage` the name
`isZero_rightDerived_pushforward_of_isAffineHom` is already taken by a statement about
`rightDerivedPlus` whose degree happens to be an integer, so neither of the two names there
refers to `CategoryTheory.Functor.rightDerived`.

No `@[stacks]` attribute is placed here. Tag 01XJ asserts quasi-coherence of the higher direct
images along a quasi-compact quasi-separated morphism; only the affine case is proved, and Tag
01XC is already carried in the file this one builds on.

## References

* [Stacks Project, Tag 01XJ](https://stacks.math.columbia.edu/tag/01XJ)
* [Stacks Project, Tag 01XC](https://stacks.math.columbia.edu/tag/01XC)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.Cohomology.Affine.HigherDirectImage

variable {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules)
  [IsAffineHom f] [F.IsQuasicoherent]

/-- **[Stacks, Tag 01XC] for Mathlib's `ℕ`-indexed right derived functors.** If `f : X ⟶ S` is
an affine morphism of schemes and `F` is a quasi-coherent `𝒪_X`-module, then
`(Rⁿ f_*) F = 0` for every `n > 0`, where `Rⁿ f_*` is
`CategoryTheory.Functor.rightDerived (Scheme.Modules.pushforward f) n`.

The vanishing is transported from the `ℤ`-indexed `rightDerivedPlus` form along
`Stacks.DerivedIndexing.isZero_rightDerived_obj_iff`. -/
@[ega "III 1.3.2"]
theorem isZero_rightDerivedNat_pushforward_of_isAffineHom (n : ℕ) (hn : 0 < n) :
    IsZero (((Scheme.Modules.pushforward f).rightDerived n).obj F) :=
  (Stacks.DerivedIndexing.isZero_rightDerived_obj_iff
      (Scheme.Modules.pushforward f) n F).2
    (isZero_rightDerivedPlus_pushforward_of_isAffineHom f F n hn)

/-- **The affine case of [Stacks, Tag 01XJ].** The higher direct images of a quasi-coherent
module along an affine morphism of schemes are quasi-coherent in every degree.

In negative degrees and in positive degrees they vanish; in degree `0` the higher direct image
is the direct image, which is quasi-coherent by [Stacks, Tag 02KG]. -/
theorem isQuasicoherent_rightDerivedPlus_pushforward_of_isAffineHom (p : ℤ) :
    (((Scheme.Modules.pushforward f).rightDerivedPlus p).obj F).IsQuasicoherent := by
  rcases lt_trichotomy p 0 with hp | rfl | hp
  · exact Stacks.AlgebraicGeometry.HigherDirectImage.isQuasicoherent_higherDirectImage_of_neg
      f F p hp
  · exact (Stacks.AlgebraicGeometry.HigherDirectImage.isQuasicoherent_higherDirectImage_zero_iff
      f F).2 inferInstance
  · exact Stacks.AlgebraicGeometry.HigherDirectImage.isQuasicoherent_of_isZero
      (R := S.ringCatSheaf) (isZero_rightDerived_pushforward_of_isAffineHom f F p hp)

/-- **The affine case of [Stacks, Tag 01XJ], for Mathlib's `ℕ`-indexed right derived
functors.** The higher direct images of a quasi-coherent module along an affine morphism of
schemes are quasi-coherent in every degree. -/
theorem isQuasicoherent_rightDerivedNat_pushforward_of_isAffineHom (n : ℕ) :
    (((Scheme.Modules.pushforward f).rightDerived n).obj F).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent S.ringCatSheaf).prop_of_iso
    ((Stacks.DerivedIndexing.rightDerivedIso (Scheme.Modules.pushforward f) n).app F).symm
    (isQuasicoherent_rightDerivedPlus_pushforward_of_isAffineHom f F n)

end Stacks.Cohomology.Affine.HigherDirectImage

end
