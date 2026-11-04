module

public import StacksFrontier.AlgebraicGeometry.AmpleBridge.BaseChange
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedFamiliesFibered
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Base change of a polarized family, with the new base as first factor

The base change of a polarized family of Stacks 0D1M along a morphism `g : V ⟶ x.base` of base
schemes, whose total space is the fibre product `V ×_{x.base} x.total` with the new base as its
first factor, together with the morphism of polarized families onto the original family that it
carries.

## Main definitions

* `AlgebraicGeometry.PolarizedFamily.stageBaseChange`: the base change of a polarized family along
  a morphism of base schemes, with the new base as the first factor of the fibre product.
* `AlgebraicGeometry.PolarizedFamily.stageBaseChangeHom`: the morphism of polarized families from
  that base change to the original family.

## Main results

* `AlgebraicGeometry.PolarizedFamily.isInvertible_pullback_snd_lineBundle`: the pullback of the
  polarization of a polarized family along the second projection of the fibre product is
  invertible.

## Implementation notes

`AlgebraicGeometry.PolarizedFamily.baseChange` writes the total space of a base change as
`x.total ×_{x.base} V`, the convention of `CategoryTheory.Over.pullback`; the base change here is
in the opposite orientation, `V ×_{x.base} x.total`.

## References

* [Stacks Project, Tag 0D1M](https://stacks.math.columbia.edu/tag/0D1M)
* [Stacks Project, Tag 0893](https://stacks.math.columbia.edu/tag/0893)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.PolarizedFamily

variable {B : BigFppfSite.{u}}

/-- The polarization of a polarized family stays invertible after base change along a morphism of
base schemes, written with the new base as the first factor of the fibre product. -/
theorem isInvertible_pullback_snd_lineBundle (x : PolarizedFamily B) {V : B.Schemes}
    (g : V ⟶ x.base) :
    AlgebraicGeometry.SheafOfModules.IsInvertible
      (Limits.pullback (B.inclusion.map g) x.toBase).presheaf
      (Limits.pullback (B.inclusion.map g) x.toBase).ringCatSheaf.2
      ((Scheme.Modules.pullback (Limits.pullback.snd (B.inclusion.map g) x.toBase)).obj
        x.lineBundle) :=
  have := x.invertible
  Stacks.RingedSpace.algebraicGeometryIsInvertible_modulePullback
    (Limits.pullback.snd (B.inclusion.map g) x.toBase).toLRSHom.toShHom x.lineBundle

/-- **The base change of a polarized family along a morphism `g : V ⟶ x.base` of base schemes**:
the total space is the fibre product with the new base as its first factor, and the polarization is
pulled back along the projection to the original total space. -/
@[ega "II 4.6.13" "(iii)"]
def stageBaseChange (x : PolarizedFamily B) {V : B.Schemes} (g : V ⟶ x.base) :
    PolarizedFamily B where
  base := V
  total := Limits.pullback (B.inclusion.map g) x.toBase
  toBase := Limits.pullback.fst (B.inclusion.map g) x.toBase
  proper := MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsProper)
    (IsPullback.of_hasPullback (B.inclusion.map g) x.toBase).flip x.proper
  flat := MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Flat)
    (IsPullback.of_hasPullback (B.inclusion.map g) x.toBase).flip x.flat
  finitePresentation :=
    ⟨MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @LocallyOfFinitePresentation)
        (IsPullback.of_hasPullback (B.inclusion.map g) x.toBase).flip x.finitePresentation.1,
      MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @QuasiCompact)
        (IsPullback.of_hasPullback (B.inclusion.map g) x.toBase).flip x.finitePresentation.2.1,
      MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @QuasiSeparated)
        (IsPullback.of_hasPullback (B.inclusion.map g) x.toBase).flip x.finitePresentation.2.2⟩
  lineBundle :=
    (Scheme.Modules.pullback (Limits.pullback.snd (B.inclusion.map g) x.toBase)).obj x.lineBundle
  invertible := x.isInvertible_pullback_snd_lineBundle g
  relativelyAmple :=
    have := x.invertible
    have := x.isInvertible_pullback_snd_lineBundle g
    Stacks.AmpleBridge.relativelyAmpleBaseChange
      (IsPullback.of_hasPullback (B.inclusion.map g) x.toBase).flip x.lineBundle
      x.relativelyAmple

/-- **The morphism of polarized families carried by a base change**: the projections of the fibre
product, with the identity comparison of polarizations. -/
def stageBaseChangeHom (x : PolarizedFamily B) {V : B.Schemes} (g : V ⟶ x.base) :
    x.stageBaseChange g ⟶ x where
  baseMap := g
  totalMap := Limits.pullback.snd (B.inclusion.map g) x.toBase
  cartesian := (IsPullback.of_hasPullback (B.inclusion.map g) x.toBase).flip
  lineBundleIso := Iso.refl _

/-- The base of the base change of a polarized family is the given scheme. -/
@[simp]
theorem stageBaseChange_base (x : PolarizedFamily B) {V : B.Schemes} (g : V ⟶ x.base) :
    (x.stageBaseChange g).base = V := rfl

/-- The total space of the base change of a polarized family along `g : V ⟶ x.base` is the fibre
product of `g` with the structure morphism, taken with `V` as its first factor. -/
@[simp]
theorem stageBaseChange_total (x : PolarizedFamily B) {V : B.Schemes} (g : V ⟶ x.base) :
    (x.stageBaseChange g).total = Limits.pullback (B.inclusion.map g) x.toBase := rfl

/-- The structure morphism of the base change of a polarized family is the first projection of the
fibre product. -/
@[simp]
theorem stageBaseChange_toBase (x : PolarizedFamily B) {V : B.Schemes} (g : V ⟶ x.base) :
    (x.stageBaseChange g).toBase = Limits.pullback.fst (B.inclusion.map g) x.toBase := rfl

/-- The polarization of the base change of a polarized family is the pullback of the original
polarization along the second projection of the fibre product. -/
@[simp]
theorem stageBaseChange_lineBundle (x : PolarizedFamily B) {V : B.Schemes} (g : V ⟶ x.base) :
    (x.stageBaseChange g).lineBundle =
      (Scheme.Modules.pullback
        (Limits.pullback.snd (B.inclusion.map g) x.toBase)).obj x.lineBundle := rfl

/-- The morphism carried by a base change has the given morphism of base schemes as its base
map. -/
@[simp]
theorem stageBaseChangeHom_baseMap (x : PolarizedFamily B) {V : B.Schemes} (g : V ⟶ x.base) :
    (x.stageBaseChangeHom g).baseMap = g := rfl

/-- The morphism carried by a base change has the second projection of the fibre product as its map
of total spaces. -/
@[simp]
theorem stageBaseChangeHom_totalMap (x : PolarizedFamily B) {V : B.Schemes} (g : V ⟶ x.base) :
    (x.stageBaseChangeHom g).totalMap =
      Limits.pullback.snd (B.inclusion.map g) x.toBase := rfl

/-- The morphism carried by a base change has the identity as its comparison of polarizations. -/
@[simp]
theorem stageBaseChangeHom_lineBundleIso (x : PolarizedFamily B) {V : B.Schemes}
    (g : V ⟶ x.base) : (x.stageBaseChangeHom g).lineBundleIso = Iso.refl _ := rfl

end AlgebraicGeometry.PolarizedFamily

end
