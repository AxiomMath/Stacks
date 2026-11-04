module

public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.Derived.FlatBaseChange
public import StacksFrontier.Homology.DerivedIndexing.Basic
import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Basic

/-!
# Vanishing of higher direct images survives flat base change

Consider a cartesian square of schemes
```
X' --g'--> X
|f'        |f
S' --g-->  S
```
with `g` flat and `f` quasi-compact and quasi-separated. For a quasi-coherent `𝒪_X`-module `ℱ`,
the base change map `g^* R^n f_* ℱ ⟶ R^n f'_* (g')^* ℱ` is an isomorphism ([Stacks, Tag 02KH]),
so `R^n f_* ℱ = 0` implies `R^n f'_* (g')^* ℱ = 0`. For `ℱ = 𝒪_X`, whose pullback is `𝒪_{X'}`,
this says that `R^n f_* 𝒪_X = 0` implies `R^n f'_* 𝒪_{X'} = 0`.

## Main results

* `isZero_rightDerived_pushforward_of_isPullback`:
  `R^n f_* ℱ = 0` implies `R^n f'_* (g')^* ℱ = 0`.
* `isZero_rightDerived_pushforward_unit_of_isPullback`:
  `R^n f_* 𝒪_X = 0` implies `R^n f'_* 𝒪_{X'} = 0`.

## Implementation notes

The statements use the `ℕ`-indexed right derived functors `CategoryTheory.Functor.rightDerived`
of the direct image, computed with injective resolutions; the proof passes to the `ℤ`-indexed
`rightDerivedPlus` of [Stacks, Tag 02KH] through
`Stacks.DerivedIndexing.isZero_rightDerived_obj_iff`, for which any model of the derived categories
may be used.

## References

* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.FlatBaseChangeDerived

variable {X X' S S' : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S'} {g : S' ⟶ S} {g' : X' ⟶ X}

/-- **Vanishing of a higher direct image survives flat base change.** For a cartesian square of
schemes with `g` flat and `f` quasi-compact and quasi-separated, and a quasi-coherent
`𝒪_X`-module `ℱ`, if `R^n f_* ℱ = 0` then `R^n f'_* (g')^* ℱ = 0`: the latter is
`g^* R^n f_* ℱ` by [Stacks, Tag 02KH]. -/
theorem isZero_rightDerived_pushforward_of_isPullback (H : IsPullback g' f' f g) [Flat g]
    [QuasiCompact f] [QuasiSeparated f] (F : X.Modules) [F.IsQuasicoherent] (n : ℕ)
    (h : IsZero (((Scheme.Modules.pushforward f).rightDerived n).obj F)) :
    IsZero (((Scheme.Modules.pushforward f').rightDerived n).obj
      ((Scheme.Modules.pullback g').obj F)) := by
  let := HasDerivedCategory.standard X.Modules
  let := HasDerivedCategory.standard S.Modules
  let := HasDerivedCategory.standard X'.Modules
  let := HasDerivedCategory.standard S'.Modules
  rw [Stacks.DerivedIndexing.isZero_rightDerived_obj_iff] at h ⊢
  exact ((Scheme.Modules.pullback g).map_isZero h).of_iso (higherBaseChangeIso H F n).symm

/-- **`R^n f_* 𝒪_X = 0` survives flat base change.** For a cartesian square of schemes with `g`
flat and `f` quasi-compact and quasi-separated, if `R^n f_* 𝒪_X = 0` then `R^n f'_* 𝒪_{X'} = 0`,
the pullback of `𝒪_X` along `g'` being `𝒪_{X'}`. -/
theorem isZero_rightDerived_pushforward_unit_of_isPullback (H : IsPullback g' f' f g) [Flat g]
    [QuasiCompact f] [QuasiSeparated f] (n : ℕ)
    (h : IsZero (((Scheme.Modules.pushforward f).rightDerived n).obj
      (SheafOfModules.unit X.ringCatSheaf))) :
    IsZero (((Scheme.Modules.pushforward f').rightDerived n).obj
      (SheafOfModules.unit X'.ringCatSheaf)) :=
  have := Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit X
  (isZero_rightDerived_pushforward_of_isPullback H _ n h).of_iso
    (((Scheme.Modules.pushforward f').rightDerived n).mapIso
      (Scheme.Modules.pullbackUnitIso g')).symm

end Stacks.AlgebraicGeometry.FlatBaseChangeDerived

end
