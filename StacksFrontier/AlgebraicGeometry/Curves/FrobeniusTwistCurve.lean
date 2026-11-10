module

public import StacksFrontier.AlgebraicGeometry.Properties.Regular
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.PullbackDegree
public import StacksFrontier.AlgebraicGeometry.Variety.Frobenius.RelativeFrobeniusDegree
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.Regular

/-!
# The Frobenius twist of a smooth proper curve

Let `k` be a field of characteristic `p > 0` and let `X` be a smooth proper curve over `k`. Its
Frobenius twist `X^{(p)} = X ×_{Spec k, F} Spec k` is again a smooth proper curve over `k`, and
it is regular, hence normal; the relative Frobenius `F_{X/k} : X ⟶ X^{(p)}` is a morphism over
`k` which is nonconstant, carries the generic point of `X` to the generic point of `X^{(p)}`,
and has degree `p`.

Smoothness and properness of the twist are stability of those properties under base change.
Regularity then comes from [Stacks, Tag 056S] and normality from [Stacks, Tag 0569]; normal
local rings are reduced, so the twist is reduced, which by [Stacks, Tag 0CCF] makes it a variety
over `k`. The relative Frobenius is a universal homeomorphism ([Stacks, Tag 0CCB]), so it does
not change the dimension of the underlying space and the twist is one-dimensional; being a
homeomorphism it is also injective, so it cannot be constant on a curve. Its degree is
`p ^ dim X = p` by [Stacks, Tag 0CCF].

## Main results

The elided prefix throughout is `AlgebraicGeometry`.

* `smooth_frobeniusTwist_curve`, `isProper_frobeniusTwist_curve`,
  `isRegular_frobeniusTwist_curve`, `isNormal_frobeniusTwist_curve`,
  `isReduced_frobeniusTwist_curve` and `isCurve_frobeniusTwist_curve`: the Frobenius twist of a
  smooth proper curve over `k` is a smooth proper curve over `k`, and is regular and normal.
* `relativeFrobenius_curve_comp`: the relative Frobenius is a morphism over `k`.
* `not_constant_relativeFrobenius_curve` and `map_genericPoint_relativeFrobenius_curve`: the
  relative Frobenius of a curve is nonconstant and carries the generic point to the generic
  point.
* `degreeOver_relativeFrobenius_curve`: the degree of [Stacks, Tag 02NY] of the relative
  Frobenius of a smooth proper curve is `p`.

## Implementation notes

The twist is the chosen categorical pullback along the absolute Frobenius of `Spec k`, so the
properties stable under base change are obtained by rewriting the structure morphism of the
twist as the second projection and appealing to typeclass inference, and the hypotheses on `X`
are the ones a consumer of `AlgebraicGeometry.curveDegree_pullback_eq_degreeOver_mul` has at
hand.

The degree is stated for `AlgebraicGeometry.degreeOver` with its instance arguments written out,
at the curve structure of the twist supplied by `isCurve_frobeniusTwist_curve`, so that it is the
subterm appearing in `AlgebraicGeometry.curveDegree_pullback_eq_degreeOver_mul` at the relative
Frobenius; `AlgebraicGeometry.locallyOfFiniteType_of_isCurve_comp` and
`AlgebraicGeometry.isDominant_of_not_constant` are the same instance arguments that consumer
uses.

Each fact here is the one-fold case of a fact about the `n`-fold twist, through
`AlgebraicGeometry.nFoldFrobeniusTwist_one`, which identifies the Frobenius twist with the
one-fold iterated twist; the derivations are given directly because the `n`-fold statements
reach the one-fold case only across that identification of objects and its `eqToHom`.

The image of the residue-field map of the relative Frobenius at the generic point is the
compositum of `k` with the `p`-th powers of the function field for every point of every scheme
over `k`, by `AlgebraicGeometry.fieldRange_residueFieldMap_relativeFrobenius`, which applies
here with no hypothesis on `X` at all; so no curve form of it is stated.

## References

* [Stacks Project, Tag 0CC9](https://stacks.math.columbia.edu/tag/0CC9)
* [Stacks Project, Tag 0CCB](https://stacks.math.columbia.edu/tag/0CCB)
* [Stacks Project, Tag 0CCF](https://stacks.math.columbia.edu/tag/0CCF)
* [Stacks Project, Tag 02NY](https://stacks.math.columbia.edu/tag/02NY)
* [Stacks Project, Tag 056S](https://stacks.math.columbia.edu/tag/056S)
* [Stacks Project, Tag 0569](https://stacks.math.columbia.edu/tag/0569)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Frobenius

universe u

namespace AlgebraicGeometry

/-- The relative Frobenius is a homeomorphism on underlying spaces, being a universal
homeomorphism. -/
private theorem isHomeomorph_relativeFrobenius (p : ℕ) [Fact p.Prime] {S : Scheme.{u}}
    (hS : IsInCharacteristic S p) (Z : Over S) :
    IsHomeomorph (relativeFrobenius S p hS Z).left :=
  (relativeFrobenius_universalHomeomorphism S p hS Z).universally_isHomeomorph
    _ _ _ IsPullback.of_id_snd

/-- **The Frobenius twist of a smooth scheme over a field is smooth.** The structure morphism of
the twist is the base change of that of `X` along the absolute Frobenius of `Spec k`. -/
theorem smooth_frobeniusTwist_curve {k : Type u} [Field k] (p : ℕ) [Fact p.Prime]
    (hS : IsInCharacteristic (Spec (.of k)) p) {X : Scheme.{u}} (pX : X ⟶ Spec (.of k))
    [Smooth pX] :
    Smooth ((frobeniusTwist (Spec (.of k)) p hS).obj (Over.mk pX)).hom := by
  change Smooth (pullback.snd pX (absoluteFrobenius (Spec (.of k)) p hS))
  infer_instance

/-- **The Frobenius twist of a proper scheme over a field is proper.** The structure morphism of
the twist is the base change of that of `X` along the absolute Frobenius of `Spec k`. -/
theorem isProper_frobeniusTwist_curve {k : Type u} [Field k] (p : ℕ) [Fact p.Prime]
    (hS : IsInCharacteristic (Spec (.of k)) p) {X : Scheme.{u}} (pX : X ⟶ Spec (.of k))
    [IsProper pX] :
    IsProper ((frobeniusTwist (Spec (.of k)) p hS).obj (Over.mk pX)).hom := by
  change IsProper (pullback.snd pX (absoluteFrobenius (Spec (.of k)) p hS))
  infer_instance

/-- **Stacks Project, Tag 056S at the Frobenius twist.** The Frobenius twist of a smooth scheme
over a field is regular, being itself smooth over the field. -/
theorem isRegular_frobeniusTwist_curve {k : Type u} [Field k] (p : ℕ) [Fact p.Prime]
    (hS : IsInCharacteristic (Spec (.of k)) p) {X : Scheme.{u}} (pX : X ⟶ Spec (.of k))
    [Smooth pX] :
    IsRegular ((frobeniusTwist (Spec (.of k)) p hS).obj (Over.mk pX)).left :=
  have : Smooth ((frobeniusTwist (Spec (.of k)) p hS).obj (Over.mk pX)).hom :=
    smooth_frobeniusTwist_curve p hS pX
  isRegular_of_smooth_over_field ((frobeniusTwist (Spec (.of k)) p hS).obj (Over.mk pX)).hom

/-- **Stacks Project, Tag 0569 at the Frobenius twist.** The Frobenius twist of a smooth scheme
over a field is normal, being regular. -/
theorem isNormal_frobeniusTwist_curve {k : Type u} [Field k] (p : ℕ) [Fact p.Prime]
    (hS : IsInCharacteristic (Spec (.of k)) p) {X : Scheme.{u}} (pX : X ⟶ Spec (.of k))
    [Smooth pX] :
    IsNormal ((frobeniusTwist (Spec (.of k)) p hS).obj (Over.mk pX)).left :=
  isNormal_of_isRegular _ (isRegular_frobeniusTwist_curve p hS pX)

/-- The Frobenius twist of a smooth scheme over a field is reduced: it is normal, and a normal
local ring is a domain. -/
theorem isReduced_frobeniusTwist_curve {k : Type u} [Field k] (p : ℕ) [Fact p.Prime]
    (hS : IsInCharacteristic (Spec (.of k)) p) {X : Scheme.{u}} (pX : X ⟶ Spec (.of k))
    [Smooth pX] :
    IsReduced ((frobeniusTwist (Spec (.of k)) p hS).obj (Over.mk pX)).left := by
  have : IsNormal ((frobeniusTwist (Spec (.of k)) p hS).obj (Over.mk pX)).left :=
    isNormal_frobeniusTwist_curve p hS pX
  have : ∀ x : ((frobeniusTwist (Spec (.of k)) p hS).obj (Over.mk pX)).left,
      _root_.IsReduced
        (((frobeniusTwist (Spec (.of k)) p hS).obj (Over.mk pX)).left.presheaf.stalk x) :=
    fun _ => inferInstance
  exact isReduced_of_isReduced_stalk _

/-- **The Frobenius twist of a smooth curve over a field is a curve over the field.** It is a
variety by [Stacks, Tag 0CCF], being reduced, and the relative Frobenius is a homeomorphism of
its underlying space with that of `X`, so it is one-dimensional. -/
theorem isCurve_frobeniusTwist_curve {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (hS : IsInCharacteristic (Spec (.of k)) p) {X : Scheme.{u}} (pX : X ⟶ Spec (.of k))
    [IsCurve k pX] [Smooth pX] :
    IsCurve k ((frobeniusTwist (Spec (.of k)) p hS).obj (Over.mk pX)).hom where
  toIsVariety := isVariety_frobeniusTwist_of_isReduced pX p (isReduced_frobeniusTwist_curve p hS pX)
  topologicalKrullDim_eq_one :=
    (IsHomeomorph.topologicalKrullDim_eq _
        (isHomeomorph_relativeFrobenius p hS (Over.mk pX))).symm.trans
      (IsCurve.topologicalKrullDim_eq_one pX)

/-- **The relative Frobenius of `X` is a morphism over the base.** This is its compatibility
`CategoryTheory.Over.w` with the structure morphisms, read at the structure morphism
`AlgebraicGeometry.frobeniusTwist_obj_hom` of the twist. -/
theorem relativeFrobenius_curve_comp {k : Type u} [Field k] (p : ℕ) [Fact p.Prime]
    (hS : IsInCharacteristic (Spec (.of k)) p) {X : Scheme.{u}} (pX : X ⟶ Spec (.of k)) :
    (relativeFrobenius (Spec (.of k)) p hS (Over.mk pX)).left ≫
        ((frobeniusTwist (Spec (.of k)) p hS).obj (Over.mk pX)).hom = pX :=
  (relativeFrobenius (Spec (.of k)) p hS (Over.mk pX)).w

/-- **The relative Frobenius of a curve is nonconstant.** It is a homeomorphism on underlying
spaces, hence injective, so a constant value would make the space of `X` a single point and `X`
zero-dimensional. -/
theorem not_constant_relativeFrobenius_curve {k : Type u} [Field k] (p : ℕ) [Fact p.Prime]
    (hS : IsInCharacteristic (Spec (.of k)) p) {X : Scheme.{u}} (pX : X ⟶ Spec (.of k))
    [IsCurve k pX] :
    ¬ ∃ y : ((frobeniusTwist (Spec (.of k)) p hS).obj (Over.mk pX)).left,
      ∀ x : X, (relativeFrobenius (Spec (.of k)) p hS (Over.mk pX)).left.base x = y := by
  rintro ⟨y, hy⟩
  have : Subsingleton (X : Type u) := ⟨fun a b =>
    (isHomeomorph_relativeFrobenius p hS (Over.mk pX)).injective ((hy a).trans (hy b).symm)⟩
  have hle := topologicalKrullDim_zero_of_discreteTopology (X : Type u)
  rw [IsCurve.topologicalKrullDim_eq_one pX] at hle
  norm_num at hle

/-- **The relative Frobenius of a curve carries the generic point to the generic point.** It is
a nonconstant morphism of curves over the field. -/
theorem map_genericPoint_relativeFrobenius_curve {k : Type u} [Field k] (p : ℕ) [Fact p.Prime]
    [CharP k p] (hS : IsInCharacteristic (Spec (.of k)) p) {X : Scheme.{u}}
    (pX : X ⟶ Spec (.of k)) [IsCurve k pX] [Smooth pX] :
    letI : IsCurve k ((frobeniusTwist (Spec (.of k)) p hS).obj (Over.mk pX)).hom :=
      isCurve_frobeniusTwist_curve p hS pX
    (relativeFrobenius (Spec (.of k)) p hS (Over.mk pX)).left.base (genericPoint (X : Type u)) =
      genericPoint
        (((frobeniusTwist (Spec (.of k)) p hS).obj (Over.mk pX)).left : Type u) := by
  have := isCurve_frobeniusTwist_curve p hS pX
  exact map_genericPoint_of_not_constant k pX
    ((frobeniusTwist (Spec (.of k)) p hS).obj (Over.mk pX)).hom
    (relativeFrobenius (Spec (.of k)) p hS (Over.mk pX)).left
    (not_constant_relativeFrobenius_curve p hS pX)

/-- **Stacks Project, Tag 0CCF at a smooth proper curve.** The relative Frobenius of a smooth
proper curve over a field of characteristic `p` has degree `p`.

The degree is `AlgebraicGeometry.degreeOver` of [Stacks, Tag 02NY] with its instance arguments
written out as `AlgebraicGeometry.curveDegree_pullback_eq_degreeOver_mul` writes them, so that
this is the value of the degree factor in that formula at the relative Frobenius. -/
theorem degreeOver_relativeFrobenius_curve {k : Type u} [Field k] (p : ℕ) [Fact p.Prime]
    [CharP k p] (hS : IsInCharacteristic (Spec (.of k)) p) {X : Scheme.{u}}
    (pX : X ⟶ Spec (.of k)) [IsCurve k pX] [Smooth pX] [IsProper pX] :
    letI : IsCurve k ((frobeniusTwist (Spec (.of k)) p hS).obj (Over.mk pX)).hom :=
      isCurve_frobeniusTwist_curve p hS pX
    @degreeOver X ((frobeniusTwist (Spec (.of k)) p hS).obj (Over.mk pX)).left
        (relativeFrobenius (Spec (.of k)) p hS (Over.mk pX)).left inferInstance inferInstance
        (locallyOfFiniteType_of_isCurve_comp k pX
          ((frobeniusTwist (Spec (.of k)) p hS).obj (Over.mk pX)).hom
          (relativeFrobenius (Spec (.of k)) p hS (Over.mk pX)).left
          (relativeFrobenius_curve_comp p hS pX))
        (isDominant_of_not_constant k pX
          ((frobeniusTwist (Spec (.of k)) p hS).obj (Over.mk pX)).hom
          (relativeFrobenius (Spec (.of k)) p hS (Over.mk pX)).left
          (not_constant_relativeFrobenius_curve p hS pX)) = p := by
  have := isCurve_frobeniusTwist_curve p hS pX
  exact (degreeOver_relativeFrobenius pX p hS (isReduced_frobeniusTwist_curve p hS pX) 1
    (IsCurve.topologicalKrullDim_eq_one pX)).trans (pow_one p)

end AlgebraicGeometry
