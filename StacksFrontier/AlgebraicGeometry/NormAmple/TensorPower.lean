module
public import StacksFrontier.AlgebraicGeometry.NormInvertible.TensorAdditive
public import StacksFrontier.AlgebraicGeometry.SectionExtension.Multiplication
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.Norm

/-!
# The norm of a tensor power

Let `f : X ⟶ Y` be a finite morphism of schemes carrying a norm `N` of degree `d` on functions
(`Stacks.Norm.MorphismNorm`, Tag 0BD1) and let `L` be an invertible `𝒪_X`-module. This file
proves that the norm of `L^{⊗ n}` is isomorphic to the `n`-th tensor power of the norm of `L`,
for every `n : ℕ`.

The argument is the Picard group, not a direct induction on the construction. The norm induces a
*homomorphism* of Picard groups (`Stacks.Divisors.exists_normPicardAddMonoidHom`, the additivity
clause of [Stacks, Tag 0BCY](https://stacks.math.columbia.edu/tag/0BCY)), the class of a tensor
power is the multiple of the class, and equality of Picard classes *is* isomorphism of sheaves
(`Stacks.SheafOfModules.picardClass_eq_iff`). So the comparison costs one computation in
`Pic(X)` and one in `Pic(Y)`; in particular the case `n = 0`, which asks for
`Norm(𝒪_X) ≅ 𝒪_Y`, comes out of `F 0 = 0`.

## Main results

* `Stacks.SheafOfModules.Invertible.picardClass_tensorPowerModule'`: the class of `L^{⊗ n}` in
  the Picard group is `n` times the class of `L`.
* `Stacks.Divisors.nonempty_normInvertible_tensorPowerModule'_iso`: **the norm of a tensor power
  is isomorphic to the tensor power of the norm.**

## Implementation notes

The exponents are natural numbers, not integers: the induction is `tensorPowerSuccIso` with
`tensorPower_zero` as its base, and `Stacks.SheafOfModules.Invertible.tensorPowerModule' L (n : ℤ)`
is the spelling that `AlgebraicGeometry.Scheme.Modules.IsAmple` and Tag 09NV use. Negative
exponents are not needed and are not treated.

The invertibility hypotheses are taken as explicit arguments rather than instances wherever a
statement mentions more than one of them. `Stacks.SheafOfModules.IsInvertible` and
`AlgebraicGeometry.SheafOfModules.IsInvertible` are both propositions, so any witness will do;
making them explicit is what keeps the two spellings from having to be reconciled by instance
search. The bridge used is `Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry`.

## References

* [Stacks Project, Tag 0BCY](https://stacks.math.columbia.edu/tag/0BCY)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CX](https://stacks.math.columbia.edu/tag/01CX)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.SheafOfModules.Invertible

variable {X : RingedSpace.{u, u}}

/-- **The class of a tensor power in the Picard group is the multiple of the class.** -/
theorem picardClass_tensorPowerModule'
    (L : _root_.SheafOfModules.{u} (structureSheafRing X))
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X).property L]
    (hL : IsInvertible X.presheaf (structureSheafRing X).property L) (n : ℕ)
    (hn : IsInvertible X.presheaf (structureSheafRing X).property
      (tensorPowerModule' L (n : ℤ))) :
    picardClass X.presheaf (structureSheafRing X).property (tensorPowerModule' L (n : ℤ)) hn
      = n • picardClass X.presheaf (structureSheafRing X).property L hL := by
  induction n with
  | zero =>
      refine Eq.trans ?_ (zero_nsmul _).symm
      refine Eq.trans ?_ (picardClass_zero X.presheaf (structureSheafRing X).property)
      refine (picardClass_eq_iff _ _ _ _ hn _).2 ⟨?_⟩
      exact eqToIso (tensorPower_zero X.presheaf (structureSheafRing X).property L)
  | succ n ih =>
      have hpow : IsInvertible X.presheaf (structureSheafRing X).property
          (tensorPowerModule' L (n : ℤ)) := inferInstance
      have htens := isInvertible_tensorSheaf X.presheaf (structureSheafRing X).property
        (tensorPowerModule' L (n : ℤ)) L
      have e : _ ≅ tensorPowerModule' L ((n + 1 : ℕ) : ℤ) :=
        tensorPowerSuccIso X.presheaf (structureSheafRing X).property L (n : ℤ) ≪≫
          eqToIso (congrArg (tensorPower X.presheaf (structureSheafRing X).property L)
            (Nat.cast_succ n).symm)
      refine Eq.trans ((picardClass_eq_iff _ _ _ _ hn htens).2 ⟨e.symm⟩) ?_
      refine Eq.trans (picardClass_tensorSheaf X.presheaf (structureSheafRing X).property
        (tensorPowerModule' L (n : ℤ)) L hpow hL htens).symm ?_
      rw [ih hpow, succ_nsmul]

end Stacks.SheafOfModules.Invertible

namespace Stacks.Divisors

open Stacks.Norm (MorphismNormMap MorphismNorm HasNormOfDegree IsDeterminantNorm)

open Stacks.SheafOfModules Stacks.SheafOfModules.Invertible

variable {X Y : Scheme.{u}}

/-- **The norm of a tensor power is isomorphic to the tensor power of the norm.** -/
theorem nonempty_normInvertible_tensorPowerModule'_iso (f : X ⟶ Y) [IsFinite f] {d : ℕ}
    (N : MorphismNorm f d) (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property L]
    (hNL : AlgebraicGeometry.SheafOfModules.IsInvertible Y.presheaf
      (structureSheafRing Y.toRingedSpace).property
      (normInvertible f N.toMorphismNormMap L)) (n : ℕ) :
    Nonempty (normInvertible f N.toMorphismNormMap (tensorPowerModule' L (n : ℤ))
      ≅ @tensorPowerModule' Y.toRingedSpace
        (normInvertible f N.toMorphismNormMap L) hNL (n : ℤ)) := by
  obtain ⟨F, hF⟩ := exists_normPicardAddMonoidHom f N
  have hL : IsInvertible X.presheaf (structureSheafRing X.toRingedSpace).property L :=
    (isInvertible_iff_algebraicGeometry _ _ L).2 ‹_›
  have hSn : IsInvertible X.presheaf (structureSheafRing X.toRingedSpace).property
      (tensorPowerModule' L (n : ℤ)) := inferInstance
  have norm_inv : ∀ M : X.Modules,
      IsInvertible X.presheaf (structureSheafRing X.toRingedSpace).property M →
      IsInvertible Y.presheaf (structureSheafRing Y.toRingedSpace).property
        (normInvertible f N.toMorphismNormMap M) := fun M hM =>
    isInvertible_normInvertible f _ M
      (hasTrivializingTargetCover_of_isFinite_of_isInvertible f M hM)
  have hNS := norm_inv _ hSn
  have hNL' := norm_inv L hL
  have hNLpow : IsInvertible Y.presheaf (structureSheafRing Y.toRingedSpace).property
      (@tensorPowerModule' Y.toRingedSpace (normInvertible f N.toMorphismNormMap L) hNL
        (n : ℤ)) := inferInstance
  refine (picardClass_eq_iff Y.presheaf (structureSheafRing Y.toRingedSpace).property _ _
    hNS hNLpow).1 ?_
  calc picardClass Y.presheaf (structureSheafRing Y.toRingedSpace).property
        (normInvertible f N.toMorphismNormMap (tensorPowerModule' L (n : ℤ))) hNS
      = F (picardClass X.presheaf (structureSheafRing X.toRingedSpace).property
          (tensorPowerModule' L (n : ℤ)) hSn) := (hF _ hSn).symm
    _ = F (n • picardClass X.presheaf (structureSheafRing X.toRingedSpace).property L hL) := by
        rw [picardClass_tensorPowerModule' L hL n hSn]
    _ = n • F (picardClass X.presheaf (structureSheafRing X.toRingedSpace).property L hL) :=
        map_nsmul F n _
    _ = n • picardClass Y.presheaf (structureSheafRing Y.toRingedSpace).property
          (normInvertible f N.toMorphismNormMap L) hNL' := by rw [hF L hL]
    _ = picardClass Y.presheaf (structureSheafRing Y.toRingedSpace).property
          (@tensorPowerModule' Y.toRingedSpace (normInvertible f N.toMorphismNormMap L) hNL
            (n : ℤ)) hNLpow :=
        (picardClass_tensorPowerModule' (normInvertible f N.toMorphismNormMap L) hNL' n
          hNLpow).symm

end Stacks.Divisors

end
