module

public import StacksFrontier.AlgebraicGeometry.Chow.FirstChernClassTensor
public import StacksFrontier.AlgebraicGeometry.InvertibleClasses.Basic
public import StacksFrontier.AlgebraicGeometry.Picard.CurveDegreeHom
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.RiemannRochInvertibleDegree

/-!
# The Picard group of a proper curve in its zeroth Chow group

Let `k` be a field and let `X` be proper over `k` of dimension at most one. Capping with the
first Chern class of an invertible `𝒪_X`-module and the fundamental one-cycle `[X]_1` gives a
zero-cycle class

`c₁(ℒ) ∩ [X]_1 ∈ CH_0(X)`,

which depends only on the isomorphism class of `ℒ` and is additive in the tensor product. So it
descends to a homomorphism of abelian groups `Pic(X) ⟶ CH_0(X)`, and this file constructs it and
identifies its composite with the degree `CH_0(X) ⟶ ℤ` of [Stacks, Tag 0AZ1]: that composite is
the degree homomorphism `Pic(X) ⟶ ℤ` on the Picard group, so a Picard class of degree zero goes
to a zero-cycle class of degree zero and conversely.

## Main definitions

* `AlgebraicGeometry.invertibleCurveChowZeroClass` — the class `c₁(ℒ) ∩ [X]_1` in `CH_0(X)`.
* `AlgebraicGeometry.curvePicardChowZeroClass` — the same for the chosen representative of a
  Picard class.
* `AlgebraicGeometry.curvePicardToChowZero` — the homomorphism `Pic(X) ⟶ CH_0(X)`.

## Main results

* `AlgebraicGeometry.curvePicardToChowZero_picardClass` — its value on the class of `ℒ` is
  `c₁(ℒ) ∩ [X]_1`, for *any* representative and not only the chosen one.
* `AlgebraicGeometry.chowDegree_invertibleCurveChowZeroClass` — the degree of `c₁(ℒ) ∩ [X]_1` is
  `deg(ℒ)`.
* `AlgebraicGeometry.chowDegree_curvePicardToChowZero` — the composite of
  `curvePicardToChowZero` with the degree of [Stacks, Tag 0AZ1] is
  `AlgebraicGeometry.invertibleCurveDegreeHom`.
* `AlgebraicGeometry.chowDegree_curvePicardToChowZero_eq_zero_iff` — a Picard class has degree
  zero exactly when its zero-cycle class has degree zero: the degree-zero parts correspond.

## Implementation notes

**Which `c₁`.** The cap product is `Stacks.Chow.firstChernClassCapOfInvertible`, the first Chern
class of [Stacks, Tag 02SO] at the pinned component rule `Stacks.Chow.firstChernComponentCycleRule`
of an invertible module; its isomorphism invariance is
`Stacks.Chow.firstChernClassCapOfInvertible_congr` and its additivity in the module is
[Stacks, Tag 02SP], `Stacks.Chow.firstChernClassCapOfInvertible_tensorObj`. Those are exactly the
two inputs the descent to the Picard group needs, and both are unconditional.

**Which Chow group.** `CH_0(X)` is `Stacks.Chow.chowGroup` for `Stacks.Chow.fieldChowSituation k`
in degree zero, the Chow situation whose base is `Spec k` with the zero dimension function; this
is the spelling `Stacks.WeilCohomology.rationalPointChowClass` speaks, so the classes of rational
points live in the target of `curvePicardToChowZero` with no transport. The fundamental one-cycle
`[X]_1` is `Stacks.Chow.cycleAssociatedToClosedSubscheme` at the identity of `X` in degree one,
as in `AlgebraicGeometry.curveChernDegree`.

**Which Picard group.** The Picard group is `Stacks.Picard.ofScheme X`, the spelling
`AlgebraicGeometry.invertibleCurveDegreeHom` is built on, so that the degree comparison needs no
transport between constructions of `Pic(X)`. The construction follows that of
`AlgebraicGeometry.invertibleCurveDegreeHom` exactly: evaluate on the representative chosen by
`Stacks.Picard.picardRepresentative`, then show the value does not depend on the choice and is
additive.

**Where the degree comparison comes from.** Nothing about degrees is proved here. The identity
`deg(ℒ) = deg(c₁(ℒ) ∩ [X]_1)` is equation [Stacks, Tag 0BRY] for an invertible module,
`AlgebraicGeometry.curveDegree_eq_curveChernDegree_of_isInvertible`, read through
`AlgebraicGeometry.curveChernDegree_eq_chowDegree_firstChernClassCapOfInvertible` and the
identification of the invertible degree with the rank-one degree,
`AlgebraicGeometry.invertibleCurveDegree_eq_curveDegree_one`.

**Two spellings of invertibility.** `Stacks.Chow.firstChernClassCapOfInvertible` indexes
invertibility by `X.sheaf.obj` and `X.ringCatSheaf.property`, the degree of [Stacks, Tag 0AYR] by
`X.presheaf` and `X.ringCatSheaf.2`, and `Stacks.Picard.picardRepresentative` by `X.presheaf` and
`Stacks.RingedSpace.structureIsSheaf X.toRingedSpace`. The three are the same hypothesis — the
sheaf conditions are proofs of one `Prop` — and are passed between the statements by explicit
application, as in `AlgebraicGeometry.invertibleCurveDegreeHom`; no bridge is introduced.

No tag is attached. [Stacks, Tag 02SO] and [Stacks, Tag 02SP] are registered on the cap product
and its additivity, [Stacks, Tag 0BRY] on the degree equation, [Stacks, Tag 0AZ1] on the degree
homomorphism and [Stacks, Tag 01CX] on the Picard group; this file repackages them as a
homomorphism out of `Pic(X)`.

## References

* [Stacks Project, Tag 02SO](https://stacks.math.columbia.edu/tag/02SO)
* [Stacks Project, Tag 02SP](https://stacks.math.columbia.edu/tag/02SP)
* [Stacks Project, Tag 0BRY](https://stacks.math.columbia.edu/tag/0BRY)
* [Stacks Project, Tag 0AZ1](https://stacks.math.columbia.edu/tag/0AZ1)
* [Stacks Project, Tag 0AYR](https://stacks.math.columbia.edu/tag/0AYR)
* [Stacks Project, Tag 01CX](https://stacks.math.columbia.edu/tag/01CX)
-/

@[expose] public noncomputable section

open CategoryTheory Stacks.Chow
open Stacks.RingedSpace (structureIsSheaf)

universe u

namespace AlgebraicGeometry

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]

/-! ### The zero-cycle class of an invertible module -/

/-- **The zero-cycle class `c₁(ℒ) ∩ [X]_1` of an invertible module on a proper curve.** The cap
product of [Stacks, Tag 02SO] with the first Chern class of `ℒ`, applied to the fundamental
one-cycle of `X`. -/
def invertibleCurveChowZeroClass (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] :
    chowGroup (fieldChowSituation k) f 0 :=
  firstChernClassCapOfInvertible (fieldChowSituation k) f 0 L
    (cycleAssociatedToClosedSubscheme (fieldChowSituation k) f (𝟙 X) 1)

/-- Isomorphic invertible modules have the same zero-cycle class: this is the isomorphism
invariance of the cap product, `Stacks.Chow.firstChernClassCapOfInvertible_congr`. -/
theorem invertibleCurveChowZeroClass_congr (L N : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N] (e : L ≅ N) :
    invertibleCurveChowZeroClass k f L = invertibleCurveChowZeroClass k f N :=
  firstChernClassCapOfInvertible_congr (fieldChowSituation k) f 0 L N e _

/-- **The zero-cycle class is additive in the tensor product**: this is [Stacks, Tag 02SP],
`Stacks.Chow.firstChernClassCapOfInvertible_tensorObj`. -/
theorem invertibleCurveChowZeroClass_tensorObj (L N : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (Scheme.Modules.tensorObj L N)] :
    invertibleCurveChowZeroClass k f (Scheme.Modules.tensorObj L N) =
      invertibleCurveChowZeroClass k f L + invertibleCurveChowZeroClass k f N :=
  (firstChernClassCapOfInvertible_tensorObj (fieldChowSituation k) f 0 L N _).symm

/-- **The degree of `c₁(ℒ) ∩ [X]_1` is `deg(ℒ)`**: equation [Stacks, Tag 0BRY] for an invertible
module on a proper scheme of dimension at most one over a field, read through the cap product of
[Stacks, Tag 02SO] and the identification of the invertible degree with the rank-one degree. -/
theorem chowDegree_invertibleCurveChowZeroClass (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules)
    [hL : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] :
    chowDegree (fieldChowSituation k) (fieldChowSituation_dimensionFunction_eq_zero k) f
        (IsLocalRing.closedPoint k) (invertibleCurveChowZeroClass k f L) =
      @invertibleCurveDegree k _ X f _ hdim L hL := by
  have hL' : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L := hL
  have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1 :=
    SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible X L
  have h1 : @invertibleCurveDegree k _ X f _ hdim L hL = curveDegree k f hdim L 1 :=
    @invertibleCurveDegree_eq_curveDegree_one k _ X f _ hdim L hL
  have h2 : curveDegree k f hdim L 1 =
      curveChernDegree k f hdim (firstChernComponentCycleRule (fieldChowSituation k) f 0 L) :=
    curveDegree_eq_curveChernDegree_of_isInvertible k f hdim L
  rw [h1, h2, curveChernDegree_eq_chowDegree_firstChernClassCapOfInvertible k f hdim L]
  rfl

/-! ### The homomorphism out of the Picard group -/

/-- The zero-cycle class of the chosen representative of a Picard class. -/
def curvePicardChowZeroClass (x : Stacks.Picard.ofScheme X) :
    chowGroup (fieldChowSituation k) f 0 :=
  @invertibleCurveChowZeroClass k _ X f _
    (Stacks.Picard.picardRepresentative X.toRingedSpace x).obj
    (Stacks.Picard.picardRepresentative X.toRingedSpace x).property

/-- The zero-cycle class of the representative of the class of `ℒ` is the zero-cycle class of
`ℒ`: the two modules are isomorphic, and the class is an isomorphism invariant. -/
theorem curvePicardChowZeroClass_picardClass (L : X.Modules)
    (hL : Stacks.SheafOfModules.IsInvertible X.presheaf (structureIsSheaf X.toRingedSpace) L) :
    curvePicardChowZeroClass k f
        (Stacks.SheafOfModules.picardClass X.presheaf (structureIsSheaf X.toRingedSpace) L hL) =
      @invertibleCurveChowZeroClass k _ X f _ L hL := by
  have e := ((Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _ _ _).1
    (Stacks.Picard.classOf_picardRepresentative X.toRingedSpace
      (Stacks.SheafOfModules.picardClass X.presheaf (structureIsSheaf X.toRingedSpace)
        L hL))).some
  exact @invertibleCurveChowZeroClass_congr k _ X f _ _ _
    (Stacks.Picard.picardRepresentative X.toRingedSpace _).property hL e

/-- **The zero-cycle class of a Picard class on a proper curve, as a homomorphism
`Pic(X) ⟶ CH_0(X)`**, `[ℒ] ↦ c₁(ℒ) ∩ [X]_1`. It is well defined because the cap product is an
isomorphism invariant, and additive because the cap product is additive in the tensor product,
[Stacks, Tag 02SP]. -/
def curvePicardToChowZero :
    Stacks.Picard.ofScheme X →+ chowGroup (fieldChowSituation k) f 0 :=
  AddMonoidHom.mk' (curvePicardChowZeroClass k f) fun x y => by
    set Lx := Stacks.Picard.picardRepresentative X.toRingedSpace x with hLxdef
    set Ly := Stacks.Picard.picardRepresentative X.toRingedSpace y with hLydef
    have hLxy := @Stacks.SheafOfModules.isInvertible_tensorSheaf _ _ _ _ _ _ _ _ _
      Lx.property Ly.property
    have hsum : x + y = Stacks.SheafOfModules.picardClass X.presheaf
        (structureIsSheaf X.toRingedSpace) _ hLxy := by
      conv_lhs => rw [← Stacks.Picard.classOf_picardRepresentative X.toRingedSpace x,
        ← Stacks.Picard.classOf_picardRepresentative X.toRingedSpace y]
      exact Stacks.SheafOfModules.picardClass_tensorSheaf _ _ _ _ _ _ hLxy
    rw [hsum]
    refine (curvePicardChowZeroClass_picardClass k f _ hLxy).trans ?_
    exact @invertibleCurveChowZeroClass_tensorObj k _ X f _ Lx.obj Ly.obj
      Lx.property Ly.property hLxy

/-- **The homomorphism on the class of `ℒ` is `c₁(ℒ) ∩ [X]_1`**, for *any* representative and
not only the chosen one. -/
@[simp] theorem curvePicardToChowZero_picardClass (L : X.Modules)
    (hL : Stacks.SheafOfModules.IsInvertible X.presheaf (structureIsSheaf X.toRingedSpace) L) :
    curvePicardToChowZero k f
        (Stacks.SheafOfModules.picardClass X.presheaf (structureIsSheaf X.toRingedSpace) L hL) =
      @invertibleCurveChowZeroClass k _ X f _ L hL :=
  curvePicardChowZeroClass_picardClass k f L hL

/-- The homomorphism agrees with the zero-cycle class of the chosen representative. -/
theorem curvePicardToChowZero_apply (x : Stacks.Picard.ofScheme X) :
    curvePicardToChowZero k f x = curvePicardChowZeroClass k f x := rfl

/-! ### Compatibility with the degree -/

/-- **The degree of the zero-cycle class of a Picard class is the degree of that class.** The
degree of [Stacks, Tag 0AZ1] composed with `AlgebraicGeometry.curvePicardToChowZero` is the
degree homomorphism `AlgebraicGeometry.invertibleCurveDegreeHom` on `Pic(X)`. -/
theorem chowDegree_curvePicardToChowZero (hdim : topologicalKrullDim X ≤ 1)
    (x : Stacks.Picard.ofScheme X) :
    chowDegree (fieldChowSituation k) (fieldChowSituation_dimensionFunction_eq_zero k) f
        (IsLocalRing.closedPoint k) (curvePicardToChowZero k f x) =
      invertibleCurveDegreeHom k f hdim x :=
  @chowDegree_invertibleCurveChowZeroClass k _ X f _ hdim
    (Stacks.Picard.picardRepresentative X.toRingedSpace x).obj
    (Stacks.Picard.picardRepresentative X.toRingedSpace x).property

/-- **The degree-zero parts correspond.** A Picard class on a proper curve has degree zero
exactly when its zero-cycle class `c₁(ℒ) ∩ [X]_1` has degree zero, so
`AlgebraicGeometry.curvePicardToChowZero` carries `Pic⁰(X)` — the kernel of
`AlgebraicGeometry.invertibleCurveDegreeHom` — into the degree-zero part of `CH_0(X)`, and
nothing outside it. -/
theorem chowDegree_curvePicardToChowZero_eq_zero_iff (hdim : topologicalKrullDim X ≤ 1)
    (x : Stacks.Picard.ofScheme X) :
    chowDegree (fieldChowSituation k) (fieldChowSituation_dimensionFunction_eq_zero k) f
        (IsLocalRing.closedPoint k) (curvePicardToChowZero k f x) = 0 ↔
      invertibleCurveDegreeHom k f hdim x = 0 := by
  rw [chowDegree_curvePicardToChowZero k f hdim x]

/-- The zero-cycle class of a Picard class in the kernel of the degree homomorphism has degree
zero: the half of `AlgebraicGeometry.chowDegree_curvePicardToChowZero_eq_zero_iff` that
`Pic⁰(X) ⟶ CH_0(X)` consumes. -/
theorem chowDegree_curvePicardToChowZero_eq_zero (hdim : topologicalKrullDim X ≤ 1)
    {x : Stacks.Picard.ofScheme X} (hx : x ∈ (invertibleCurveDegreeHom k f hdim).ker) :
    chowDegree (fieldChowSituation k) (fieldChowSituation_dimensionFunction_eq_zero k) f
        (IsLocalRing.closedPoint k) (curvePicardToChowZero k f x) = 0 :=
  (chowDegree_curvePicardToChowZero_eq_zero_iff k f hdim x).2 hx

end AlgebraicGeometry

end
