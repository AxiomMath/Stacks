module

public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Basic
public import StacksFrontier.AlgebraicGeometry.HigherDirectImage.RightDerivedPlus
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.SituationBaseChange

/-!
# Top-degree base-change situations from affine morphisms

`Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation` packages a morphism `f : X ⟶ Y` of
quasi-compact quasi-separated schemes, a degree `d` above which the higher direct images of every
quasi-coherent module vanish, and a cartesian square. An affine morphism of quasi-compact
quasi-separated schemes, together with any degree `d` and any cartesian square, is such a
situation, since its higher direct images of quasi-coherent modules vanish in every positive
degree.

At `d = 0` the degree-`d` higher direct image along the base change `f'` is the ordinary direct
image, which is nonzero at the structure sheaf of a source carrying a nonzero function; at
`d > 0` the degree-`d` higher direct image is zero.

## Main definitions

* `Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.ofIsAffineHom`: a top-degree
  base-change situation from an affine morphism of quasi-compact quasi-separated schemes, a
  degree, and an arbitrary cartesian square.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.ofIsAffineHomBaseChange`: the same with
  the canonical cartesian square over a morphism `g : Y' ⟶ Y`.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.ofIsAffineHomSelf`: the same with the
  identity square, so that the base-changed morphism is `f` itself.

## Main results

* `Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.nonempty`: the type of situations is
  nonempty.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.topDirectImageIsoPushforward`: at
  `d = 0` the degree-`d` higher direct image along `f'` is the ordinary direct image.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.not_isZero_topDirectImage_unit`: at
  `d = 0` it is nonzero at the structure sheaf of a source with a nonzero function.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.isZero_topDirectImage_of_pos`: it is
  zero whenever `d > 0`.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.isZero_cohomology_of_pos`: the
  cohomology of the source of a base change of an affine morphism over an affine base vanishes in
  positive degrees, for every quasi-coherent module.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 01XC](https://stacks.math.columbia.edu/tag/01XC)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.AffineBase

universe u

namespace Stacks.AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

noncomputable section

namespace TopDegreeBaseChangeSituation

/-- The top-degree base-change situation of an affine morphism `f` of quasi-compact
quasi-separated schemes, a degree `d` and a cartesian square: `Rⁱ f_* F` vanishes for every
quasi-coherent `F` and every `i > 0`, hence for every `i > d`. -/
def ofIsAffineHom {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (d : ℕ) [IsAffineHom f]
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y) (sq : IsPullback g' f' f g) :
    TopDegreeBaseChangeSituation.{u} where
  X := X
  Y := Y
  f := f
  d := d
  isCompact_X := ‹CompactSpace X›
  isQuasiSeparated_X := ‹QuasiSeparatedSpace X›
  isCompact_Y := ‹CompactSpace Y›
  isQuasiSeparated_Y := ‹QuasiSeparatedSpace Y›
  vanishes_above i hi F hF :=
    have := hF
    Stacks.Cohomology.Affine.isZero_rightDerived_pushforward_of_isAffineHom f F i
      (lt_of_le_of_lt (Int.natCast_nonneg d) hi)
  X' := X'
  Y' := Y'
  g' := g'
  f' := f'
  g := g
  isPullback := sq

section Projections

variable {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (d : ℕ) [IsAffineHom f]
  [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
  (g' : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y) (sq : IsPullback g' f' f g)

/-- The morphism of `ofIsAffineHom f d g' f' g sq` is `f`. -/
@[simp]
theorem ofIsAffineHom_f : (ofIsAffineHom f d g' f' g sq).f = f := rfl

/-- The degree of `ofIsAffineHom f d g' f' g sq` is `d`. -/
@[simp]
theorem ofIsAffineHom_d : (ofIsAffineHom f d g' f' g sq).d = d := rfl

/-- The base-changed morphism of `ofIsAffineHom f d g' f' g sq` is `f'`. -/
@[simp]
theorem ofIsAffineHom_f' : (ofIsAffineHom f d g' f' g sq).f' = f' := rfl

end Projections

/-- The situation of an affine morphism with the pullback square of `f` along `g`. -/
def ofIsAffineHomBaseChange {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (d : ℕ) (g : Y' ⟶ Y) [IsAffineHom f]
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y] :
    TopDegreeBaseChangeSituation.{u} :=
  ofIsAffineHom f d (pullback.fst f g) (pullback.snd f g) g (IsPullback.of_hasPullback f g)

/-- The situation of an affine morphism with the identity square, in which the base-changed
morphism is `f` itself. -/
def ofIsAffineHomSelf {X Y : Scheme.{u}} (f : X ⟶ Y) (d : ℕ) [IsAffineHom f]
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y] :
    TopDegreeBaseChangeSituation.{u} :=
  ofIsAffineHom f d (𝟙 X) f (𝟙 Y) (IsPullback.of_horiz_isIso ⟨by simp⟩)

section Self

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (d : ℕ) [IsAffineHom f]
  [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]

/-- The base-changed morphism of `ofIsAffineHomSelf f d` is `f`. -/
@[simp]
theorem ofIsAffineHomSelf_f' : (ofIsAffineHomSelf f d).f' = f := rfl

/-- The degree of `ofIsAffineHomSelf f d` is `d`. -/
@[simp]
theorem ofIsAffineHomSelf_d : (ofIsAffineHomSelf f d).d = d := rfl

end Self

/-- There is a top-degree base-change situation: the identity of `Spec (ULift ℤ)` gives one. -/
instance nonempty : Nonempty TopDegreeBaseChangeSituation.{u} :=
  ⟨ofIsAffineHomSelf (𝟙 (Spec (CommRingCat.of (ULift.{u} ℤ)))) 0⟩

/-- At `d = 0` the degree-`d` higher direct image along `f'` is the ordinary direct image
`f'_* F'`. -/
def topDirectImageIsoPushforward {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f]
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y) (sq : IsPullback g' f' f g) (F' : X'.Modules) :
    ((Scheme.Modules.pushforward f').rightDerivedPlus
        (((ofIsAffineHom f 0 g' f' g sq).d : ℕ) : ℤ)).obj F' ≅
      (Scheme.Modules.pushforward f').obj F' :=
  Stacks.RightDerivedPlus.rightDerivedPlusZeroObjIso _ F'

/-- The direct image of the structure sheaf is nonzero as soon as the source has a nonzero
function. -/
theorem not_isZero_pushforward_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Nontrivial Γ(X, (⊤ : X.Opens))] :
    ¬ IsZero ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)) := by
  intro h
  have h1 : IsZero ((SheafOfModules.evaluation Y.ringCatSheaf (op (⊤ : Y.Opens))).obj
      ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf))) :=
    Functor.map_isZero _ h
  have h2 : Subsingleton Γ(X, f ⁻¹ᵁ (⊤ : Y.Opens)) := ModuleCat.isZero_iff_subsingleton.mp h1
  rw [show f ⁻¹ᵁ (⊤ : Y.Opens) = ⊤ from by simp] at h2
  exact not_subsingleton _ h2

/-- At `d = 0` the degree-`d` higher direct image of the structure sheaf of a source with a
nonzero function is nonzero. -/
theorem not_isZero_topDirectImage_unit {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f]
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
    [Nontrivial Γ(X, (⊤ : X.Opens))] :
    ¬ IsZero (((Scheme.Modules.pushforward (ofIsAffineHomSelf f 0).f').rightDerivedPlus
      (((ofIsAffineHomSelf f 0).d : ℕ) : ℤ)).obj (SheafOfModules.unit X.ringCatSheaf)) :=
  fun h => not_isZero_pushforward_unit f
    (h.of_iso (topDirectImageIsoPushforward f (𝟙 X) f (𝟙 Y)
      (IsPullback.of_horiz_isIso ⟨by simp⟩) (SheafOfModules.unit X.ringCatSheaf)).symm)

/-- For `d > 0` the degree-`d` higher direct image along an affine morphism of a quasi-coherent
module is zero. -/
theorem isZero_topDirectImage_of_pos {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (d : ℕ) (hd : 0 < d)
    [IsAffineHom f] [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y]
    [QuasiSeparatedSpace Y] (g' : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
    (sq : IsPullback g' f' f g) (F : X.Modules) [F.IsQuasicoherent] :
    IsZero (((Scheme.Modules.pushforward (ofIsAffineHom f d g' f' g sq).f).rightDerivedPlus
      (((ofIsAffineHom f d g' f' g sq).d : ℕ) : ℤ)).obj F) :=
  Stacks.Cohomology.Affine.isZero_rightDerived_pushforward_of_isAffineHom f F (d : ℤ)
    (by exact_mod_cast hd)

/-- The cohomology of the source of a base change of an affine morphism over an affine base
vanishes in positive degrees, for every quasi-coherent module. -/
theorem isZero_cohomology_of_pos {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f]
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y) (sq : IsPullback g' f' f g) [IsAffine Y']
    (i : ℤ) (hi : 0 < i) (F' : X'.Modules) [F'.IsQuasicoherent] :
    IsZero (((moduleGlobalSections X').rightDerivedPlus i).obj F') := by
  exact @isZero_cohomology_of_lt (ofIsAffineHom f 0 g' f' g sq) ‹_› i (by exact_mod_cast hi)
    F' ‹_›

end TopDegreeBaseChangeSituation

end

end Stacks.AlgebraicGeometry

end
