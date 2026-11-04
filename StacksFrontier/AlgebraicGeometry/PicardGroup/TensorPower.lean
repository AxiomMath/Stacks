module

public import StacksFrontier.AlgebraicGeometry.PicardGroup.Pullback
public import StacksCore.Tactic.StacksAttribute

/-!
# Picard classes of tensor powers

Let `O` be a sheaf of commutative rings on a site and let `L` be an invertible sheaf of
`O`-modules. The integer tensor powers `L^{⊗ n}` of
[Stacks, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU) are again invertible, so each has
a class in the Picard group; this file proves that the class of `L^{⊗ n}` is `n` times the class
of `L`.

Together with `Stacks.SheafOfModules.picardClass_eq_iff` this is what turns a computation in the
Picard group into an isomorphism of tensor powers, and conversely.

## Main definitions

* `Stacks.SheafOfModules.schemeTensorPower`: `L^{⊗ n}` for an invertible module on a scheme,
  with the invertibility hypothesis explicit rather than an instance.

## Main results

* `Stacks.SheafOfModules.picardClass_tensorPower`: the class of `L^{⊗ n}` is `n • [L]`.
* `Stacks.SheafOfModules.picardClass_schemeTensorPower`: the same statement on a scheme.

## Implementation notes

The proof is an induction on `n : ℤ` through `Int.induction_on`, whose only inputs are the
successor comparison `L^{⊗ n} ⊗ L ≅ L^{⊗ (n + 1)}` of Tag 01CU and the fact that addition of
Picard classes is the tensor product. For negative exponents the successor comparison is read
backwards, so the step cancels one factor of `L` instead of adding one; no separate treatment
of the inverse tensor power is needed.

As in `StacksFrontier/AlgebraicGeometry/PicardGroup/Pullback.lean`, the scheme-level statements
carry invertibility as an explicit argument rather than as an instance: the invertibility
classes of the library are keyed on
`Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO`, while the modules of a scheme
that the Picard group is applied to live over `Stacks.RingedSpace.ringSheaf X`, and instance
search does not cross that boundary at reducible transparency even though the two are equal by
`rfl`.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CX](https://stacks.math.columbia.edu/tag/01CX)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory RingedSpaceModuleAdjunction TopologicalSpace

universe v u w

namespace Stacks.SheafOfModules

section Site

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

/-- **The Picard class of the `n`th tensor power of an invertible sheaf of modules is `n` times
its Picard class.** -/
theorem picardClass_tensorPower
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    [hL : IsInvertible O hO L] (n : ℤ) :
    picardClass O hO (TensorPower.tensorPower O hO L n)
        (TensorPower.isInvertible_tensorPower O hO L n) =
      n • picardClass O hO L hL := by
  have key : ∀ m k : ℤ, m + 1 = k →
      picardClass O hO (TensorPower.tensorPower O hO L k)
          (TensorPower.isInvertible_tensorPower O hO L k) =
        picardClass O hO (TensorPower.tensorPower O hO L m)
          (TensorPower.isInvertible_tensorPower O hO L m) + picardClass O hO L hL := by
    intro m k hk
    have hpow := TensorPower.isInvertible_tensorPower O hO L m
    rw [picardClass_tensorSheaf O hO _ L hpow hL
      (by have := hpow; exact isInvertible_tensorSheaf O hO _ L)]
    exact (picardClass_eq_iff O hO _ _ _ _).mpr
      ⟨(TensorPower.tensorPowerSuccIso O hO L m ≪≫ TensorPower.tensorPowerReindex O hO L hk).symm⟩
  induction n using Int.induction_on with
  | zero =>
      rw [zero_smul, picardClass_eq_zero_iff]
      exact ⟨Iso.refl _⟩
  | succ i ih => rw [key i _ rfl, ih, add_smul, one_smul]
  | pred i ih =>
      have h1 := key (-(i : ℤ) - 1) (-(i : ℤ)) (by ring)
      rw [ih] at h1
      rw [sub_smul, one_smul]
      exact eq_sub_of_add_eq h1.symm

end Site

section Scheme

/-- **The `n`th tensor power of an invertible module on a scheme**, in the spelling the Picard
group of a scheme is stated at and with the invertibility hypothesis explicit.

Every argument is supplied by hand rather than by instance search: the invertibility of `L`
would have to be found for `L` at the type `SheafOfModules (structureSheaf X.presheaf _)`
while it is given for `L` at the equal but not reducibly equal type
`SheafOfModules (structureSheafRing X.toRingedSpace)`, and instance search does not cross that
boundary. -/
noncomputable def schemeTensorPower (X : Scheme.{u})
    (L : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    (hL : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf L) (n : ℤ) :
    SheafOfModules.{u} (structureSheafRing X.toRingedSpace) :=
  @TensorPower.tensorPower _ _ _ X.presheaf X.ringCatIsSheaf _ _ L
    (@TensorPower.isEquivalence_tensorRightFunctor _ _ _ X.presheaf X.ringCatIsSheaf _ _ L hL) n

/-- Every tensor power of an invertible module on a scheme is invertible. -/
theorem isInvertible_schemeTensorPower (X : Scheme.{u})
    (L : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    (hL : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf L) (n : ℤ) :
    Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf
      (schemeTensorPower X L hL n) :=
  @TensorPower.isInvertible_tensorPower _ _ _ X.presheaf X.ringCatIsSheaf _ _ L hL n

/-- **The class in `Pic(X)` of `L^{⊗ n}` is `n` times the class of `L`.** -/
theorem picardClass_schemeTensorPower (X : Scheme.{u})
    (L : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    (hL : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf L) (n : ℤ) :
    picardClass X.presheaf X.ringCatIsSheaf (schemeTensorPower X L hL n)
        (isInvertible_schemeTensorPower X L hL n) =
      n • picardClass X.presheaf X.ringCatIsSheaf L hL :=
  @picardClass_tensorPower _ _ _ X.presheaf X.ringCatIsSheaf _ _ L hL n

end Scheme

end Stacks.SheafOfModules

end
