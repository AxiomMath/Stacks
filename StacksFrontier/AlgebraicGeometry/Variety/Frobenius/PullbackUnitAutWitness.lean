module

public import Mathlib.Data.ZMod.Basic
public import StacksFrontier.AlgebraicGeometry.Picard.FrobeniusTorsion
public import StacksFrontier.AlgebraicGeometry.Variety.Frobenius.PullbackUnitAut

/-!
# The Frobenius power formula on automorphisms is non-degenerate, and its exponent is sharp

`AlgebraicGeometry.pullbackUnitAut_absoluteFrobenius` says that pullback along the absolute
Frobenius of a scheme in characteristic `p` is the `p`-fold composite power on automorphisms of
the structure sheaf. Two things could make that statement empty: the automorphism group of the
free sheaf of rank one could be trivial, in which case both sides are the identity for every `p`;
or the exponent could be immaterial, in which case the same equation would hold with any other
exponent. This file refutes both, at `Z = Spec(ℤ/3ℤ)` and `p = 3`, with the automorphism
`Stacks.SheafOfModules.negUnitAut`, whose value at `1` is `-1`.

## Main results

* `AlgebraicGeometry.negUnitAut_ringSheaf_specZModThree_ne_refl`: the automorphism used is not
  the identity, so the theorem is not quantified over a one-element group.
* `AlgebraicGeometry.pullbackUnitAut_absoluteFrobenius_specZModThree_negUnitAut`: the power
  formula at that scheme, prime and automorphism — the concrete instance of the general theorem.
* `AlgebraicGeometry.pullbackUnitAut_absoluteFrobenius_ne_autPow_succ`: **the same formula with
  `p + 1` in place of `p` is false there.** So the exponent is forced by the mathematics and not
  by the shape of the proof.

## Implementation notes

`-1 ≠ 1` in the ring of global sections is pulled back from `ℤ/3ℤ` along
`AlgebraicGeometry.Scheme.ΓSpecIso`; everything else is the value-at-`1` calculus of
`StacksFrontier/Topology/Sheaves/Functors/Module/UnitEndomorphismSections.lean`, with
`(-1) ^ 3 = -1` and `(-1) ^ 4 = 1`. The separation is at the same prime and the same scheme as
the instance it is about, rather than at a degenerate object: `ℤ/3ℤ` is a field of
characteristic `3` and `Spec(ℤ/3ℤ)` is a one-point scheme that is neither empty nor of
characteristic `2`, where `-1 = 1` would make the control vacuous.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace RingedSpaceModuleAdjunction
open Stacks.SheafOfModules (negUnitAut negUnitAut_hom_val_app_one unitAut_autPow_val_app_one
  unitAut_val_app_one_congr)
open Stacks.Frobenius

namespace AlgebraicGeometry

/-- `Spec(ℤ/3ℤ)` is a scheme in characteristic `3`. -/
theorem isInCharacteristic_specZModThree :
    IsInCharacteristic (Spec (CommRingCat.of (ZMod 3))) 3 :=
  isInCharacteristic_spec (ZMod 3) 3 (by decide)

/-- In the global sections of `Spec(ℤ/3ℤ)`, `-1` and `1` are different. -/
theorem neg_one_ne_one_specZModThree :
    (-1 : (structureSheafRing (Spec (CommRingCat.of (ZMod 3))).toRingedSpace).obj.obj (op ⊤)) ≠
      1 := by
  intro h
  have e := (Scheme.ΓSpecIso (CommRingCat.of (ZMod 3))).commRingCatIsoToRingEquiv
  have h2 : e (-1) = e 1 := congrArg e h
  rw [map_neg, map_one] at h2
  exact absurd h2 (by decide)

/-- The value at `1` of the `n`-fold composite of `Stacks.SheafOfModules.negUnitAut` on
`Spec(ℤ/3ℤ)` is `(-1) ^ n`. -/
theorem negUnitAut_autPow_val_app_one_specZModThree (n : ℕ) :
    ((negUnitAut (structureSheafRing (Spec (CommRingCat.of (ZMod 3))).toRingedSpace)).autPow
        n).hom.val.app (op ⊤)
        (1 : (structureSheafRing (Spec (CommRingCat.of (ZMod 3))).toRingedSpace).obj.obj (op ⊤)) =
      (-1 : (structureSheafRing (Spec (CommRingCat.of (ZMod 3))).toRingedSpace).obj.obj
        (op ⊤)) ^ n :=
  unitAut_autPow_val_app_one _ (op ⊤) _ (negUnitAut_hom_val_app_one (op ⊤)) n

/-- **The automorphism group of the free sheaf of modules of rank one on `Spec(ℤ/3ℤ)` is not
trivial**: `-𝟙` is not the identity. -/
theorem negUnitAut_ringSheaf_specZModThree_ne_refl :
    negUnitAut (structureSheafRing (Spec (CommRingCat.of (ZMod 3))).toRingedSpace) ≠
      Iso.refl (SheafOfModules.unit
        (structureSheafRing (Spec (CommRingCat.of (ZMod 3))).toRingedSpace)) := by
  intro h
  exact neg_one_ne_one_specZModThree
    ((negUnitAut_hom_val_app_one (op ⊤)).symm.trans (unitAut_val_app_one_congr h (op ⊤)))

/-- The Frobenius power formula at `Spec(ℤ/3ℤ)`, `p = 3` and the non-identity automorphism
`-𝟙`: the concrete instance of `AlgebraicGeometry.pullbackUnitAut_absoluteFrobenius`. -/
theorem pullbackUnitAut_absoluteFrobenius_specZModThree_negUnitAut :
    pullbackUnitAut
        ((absoluteFrobenius (Spec (CommRingCat.of (ZMod 3))) 3
          isInCharacteristic_specZModThree).toLRSHom.toShHom)
        (negUnitAut (structureSheafRing (Spec (CommRingCat.of (ZMod 3))).toRingedSpace)) =
      (negUnitAut (structureSheafRing (Spec (CommRingCat.of (ZMod 3))).toRingedSpace)).autPow 3 :=
  pullbackUnitAut_absoluteFrobenius _ 3 _ _

/-- **The exponent in `AlgebraicGeometry.pullbackUnitAut_absoluteFrobenius` is sharp.** At
`Spec(ℤ/3ℤ)` with `p = 3` and the automorphism `-𝟙`, pullback along the absolute Frobenius is
*not* the `(p + 1)`-fold composite power. -/
theorem pullbackUnitAut_absoluteFrobenius_ne_autPow_succ :
    pullbackUnitAut
        ((absoluteFrobenius (Spec (CommRingCat.of (ZMod 3))) 3
          isInCharacteristic_specZModThree).toLRSHom.toShHom)
        (negUnitAut (structureSheafRing (Spec (CommRingCat.of (ZMod 3))).toRingedSpace)) ≠
      (negUnitAut (structureSheafRing (Spec (CommRingCat.of (ZMod 3))).toRingedSpace)).autPow
        4 := by
  intro h
  have key := pullbackUnitAut_absoluteFrobenius_specZModThree_negUnitAut.symm.trans h
  have hpow :
      ((-1 : (structureSheafRing (Spec (CommRingCat.of (ZMod 3))).toRingedSpace).obj.obj
        (op ⊤)) ^ 3) =
      ((-1 : (structureSheafRing (Spec (CommRingCat.of (ZMod 3))).toRingedSpace).obj.obj
        (op ⊤)) ^ 4) :=
    (negUnitAut_autPow_val_app_one_specZModThree 3).symm.trans
      ((unitAut_val_app_one_congr key (op ⊤)).trans
        (negUnitAut_autPow_val_app_one_specZModThree 4))
  exact neg_one_ne_one_specZModThree
    ((Odd.neg_one_pow (by norm_num)).symm.trans (hpow.trans (Even.neg_one_pow (by norm_num))))

end AlgebraicGeometry

end
