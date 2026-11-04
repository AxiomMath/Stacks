module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.Ring.Epi.Basic
public import StacksFrontier.AlgebraicGeometry.HigherDirectImage.RightDerivedPlus

/-!
# Quasi-coherence of higher direct images

Let `f : X ⟶ S` be a morphism of schemes. The higher direct images of a sheaf of modules on `X`
are the higher right derived functors of `AlgebraicGeometry.Scheme.Modules.pushforward f`,
computed in the bounded below derived categories of the Grothendieck abelian categories
`X.Modules` and `S.Modules`:
`R ᵖ f_* = (Scheme.Modules.pushforward f).rightDerivedPlus p`.

This file establishes what holds for quasi-coherence of `R ᵖ f_* F` in degrees `p ≤ 0`, for an
arbitrary morphism of schemes and an arbitrary module:

* in negative degrees `R ᵖ f_* F` vanishes, hence is quasi-coherent, with no hypothesis on `f`
  or on `F` at all;
* in degree `0` the pushforward functor, being a right adjoint, is left exact, so
  `R ⁰ f_* F ≅ f_* F`, and quasi-coherence of `R ⁰ f_* F` is *equivalent* to quasi-coherence of
  `f_* F`.

The degree `0` statement is therefore exactly [Stacks, Tag 01LC] (pushforward along a
quasi-compact quasi-separated morphism preserves quasi-coherence), and the genuinely
cohomological content of [Stacks, Tag 01XJ] part (1) is confined to the degrees `p > 0`.

The affine case of the degree `0` statement is available from Mathlib and is recorded here:
for a ring map `φ : R ⟶ S` the pushforward along `Spec.map φ` of a quasi-coherent
`𝒪_{Spec S}`-module is quasi-coherent.

## Main results

* `Stacks.AlgebraicGeometry.HigherDirectImage.isQuasicoherent_of_isZero`: a zero sheaf of
  modules is quasi-coherent.
* `Stacks.AlgebraicGeometry.HigherDirectImage.isZero_higherDirectImage_of_neg`:
  `R ᵖ f_* F = 0` for `p < 0`.
* `Stacks.AlgebraicGeometry.HigherDirectImage.isQuasicoherent_higherDirectImage_of_neg`:
  `R ᵖ f_* F` is quasi-coherent for `p < 0`.
* `Stacks.AlgebraicGeometry.HigherDirectImage.higherDirectImageZeroIso`: `R ⁰ f_* F ≅ f_* F`.
* `Stacks.AlgebraicGeometry.HigherDirectImage.isQuasicoherent_higherDirectImage_zero_iff`:
  `R ⁰ f_* F` is quasi-coherent if and only if `f_* F` is.
* `Stacks.AlgebraicGeometry.HigherDirectImage.isQuasicoherent_pushforward_specMap`: pushforward
  along a morphism of affine schemes preserves quasi-coherence.

## Implementation notes

The derived category instances on the module categories of a scheme are the ones the source's
statement uses, namely `CategoryTheory.HasDerivedCategory.standard`, installed as a local
instance; `EnoughInjectives` comes from Grothendieck abelianness and is found by instance
search.

A zero sheaf of modules is quasi-coherent because it is isomorphic to the free sheaf on the
empty index type, which is an initial, hence zero, object; free sheaves are locally free and
therefore quasi-coherent, and quasi-coherence is closed under isomorphisms.

## References

* [Stacks Project, Tag 01XJ](https://stacks.math.columbia.edu/tag/01XJ)
* [Stacks Project, Tag 01LC](https://stacks.math.columbia.edu/tag/01LC)
-/

@[expose] public section

open CategoryTheory Limits
open AlgebraicGeometry

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.AlgebraicGeometry.HigherDirectImage

/-! ### Zero sheaves of modules are quasi-coherent -/

section Zero

variable {C : Type*} [Category* C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The free sheaf of modules on the empty index type is a zero object: it is initial, because
morphisms out of a free sheaf on `I` are families of sections indexed by `I`. -/
theorem isZero_free_pempty : IsZero (SheafOfModules.free (R := R) (PEmpty.{u + 1})) :=
  IsInitial.isZero (IsInitial.ofUnique
    (h := fun Y => Equiv.unique (β := PEmpty.{u + 1} → Y.sections) Y.freeHomEquiv))

variable [HasBinaryProducts C] [∀ X : C, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- A zero sheaf of modules is quasi-coherent. -/
theorem isQuasicoherent_of_isZero {M : SheafOfModules.{u} R} (hM : IsZero M) :
    M.IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent R).prop_of_iso
    (hM.iso (isZero_free_pempty (R := R))).symm inferInstance

end Zero

/-! ### Higher direct images in non-positive degrees -/

variable {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules)

/-- **Higher direct images vanish in negative degrees**: `R ᵖ f_* F = 0` for `p < 0`. This needs
no hypothesis on the morphism `f` nor on the module `F`. -/
theorem isZero_higherDirectImage_of_neg (p : ℤ) (hp : p < 0) :
    IsZero (((Scheme.Modules.pushforward f).rightDerivedPlus p).obj F) :=
  Stacks.RightDerivedPlus.isZero_rightDerivedPlus_obj _ p hp F

/-- **Higher direct images are quasi-coherent in negative degrees**, for trivial reasons: they
vanish. This is the part of [Stacks, Tag 01XJ] part (1) that holds with no hypothesis on `f` or
on `F`. -/
theorem isQuasicoherent_higherDirectImage_of_neg (p : ℤ) (hp : p < 0) :
    (((Scheme.Modules.pushforward f).rightDerivedPlus p).obj F).IsQuasicoherent :=
  isQuasicoherent_of_isZero (R := S.ringCatSheaf) (isZero_higherDirectImage_of_neg f F p hp)

/-- **The zeroth higher direct image is the pushforward**: `R ⁰ f_* F ≅ f_* F`.

The pushforward functor on sheaves of modules over schemes is a right adjoint, hence left exact,
so it agrees with its own zeroth right derived functor by [Stacks, Tag 05TD] part (3). -/
noncomputable def higherDirectImageZeroIso :
    ((Scheme.Modules.pushforward f).rightDerivedPlus 0).obj F ≅
      (Scheme.Modules.pushforward f).obj F :=
  Stacks.RightDerivedPlus.rightDerivedPlusZeroObjIso _ F

/-- **Quasi-coherence of `R ⁰ f_* F` is quasi-coherence of `f_* F`.** Together with
`isQuasicoherent_higherDirectImage_of_neg`, this reduces [Stacks, Tag 01XJ] part (1) to
[Stacks, Tag 01LC] in degree `0` and to the degrees `p > 0`. -/
theorem isQuasicoherent_higherDirectImage_zero_iff :
    (((Scheme.Modules.pushforward f).rightDerivedPlus 0).obj F).IsQuasicoherent ↔
      ((Scheme.Modules.pushforward f).obj F).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent S.ringCatSheaf).prop_iff_of_iso (higherDirectImageZeroIso f F)

/-! ### Pushforward along a morphism of affine schemes -/

/-- **Pushforward along a morphism of affine schemes preserves quasi-coherence.** For a ring map
`φ : R ⟶ S` and a quasi-coherent `𝒪_{Spec S}`-module `M`, the pushforward
`(Spec.map φ)_* M` is quasi-coherent.

This is the affine case of [Stacks, Tag 01LC]; it is the content of
`AlgebraicGeometry.isIso_fromTildeΓ_pushforward` once quasi-coherence on an affine scheme is
read through `AlgebraicGeometry.isQuasicoherent_iff_isIso_fromTildeΓ`. -/
instance isQuasicoherent_pushforward_specMap {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (M : (Spec S).Modules) [M.IsQuasicoherent] :
    ((Scheme.Modules.pushforward (Spec.map φ)).obj M).IsQuasicoherent := by
  rw [_root_.AlgebraicGeometry.isQuasicoherent_iff_isIso_fromTildeΓ]
  exact _root_.AlgebraicGeometry.isIso_fromTildeΓ_pushforward φ M

end Stacks.AlgebraicGeometry.HigherDirectImage
