module

public import StacksFrontier.AlgebraicGeometry.Picard.GaloisDescent.Pullback
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.DivisorDegreeTwist
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleCompare

/-!
# The degree homomorphism on the Picard group of a proper curve

Let `X` be a scheme proper over a field `k` of dimension at most one.  The degree
`AlgebraicGeometry.invertibleCurveDegree` of an invertible `𝒪_X`-module ([Stacks, Tag 0AYR])
depends only on its isomorphism class and is additive in the tensor product ([Stacks, Tag 0AYX],
`AlgebraicGeometry.invertibleCurveDegree_tensorSheaf_eq_add`), so it descends to a homomorphism

`deg : Pic(X) ⟶ ℤ`

on the Picard group `Stacks.Picard.ofScheme X`.  Its kernel is `Pic⁰(X)`, and every torsion class
lies in it because `ℤ` is torsion free: this is the first step of the proof of
[Stacks, Tag 0C1Z], which reads the short exact sequence `0 → Pic⁰(X) → Pic(X) → ℤ → 0`.

## Main definitions

* `Stacks.Picard.ofSchemeDegree`: the degree homomorphism `Pic(X) ⟶ ℤ`.
* `Stacks.Picard.ofSchemeDegreeZero`: its kernel `Pic⁰(X)`.

## Main results

* `Stacks.Picard.ofSchemeDegree_picardClass`: the degree of the class of `ℒ` is the degree of `ℒ`.
* `Stacks.Picard.torsionBy_le_ofSchemeDegreeZero`: the `m`-torsion of `Pic(X)` lies in `Pic⁰(X)`
  for every `m ≠ 0`.
* `Stacks.Picard.torsionByOfSchemeDegreeZeroAddEquiv`: the `m`-torsion of `Pic(X)` is the
  `m`-torsion of `Pic⁰(X)`.

## References

* [Stacks Project, Tag 0AYR](https://stacks.math.columbia.edu/tag/0AYR)
* [Stacks Project, Tag 0AYX](https://stacks.math.columbia.edu/tag/0AYX)
* [Stacks Project, Tag 0C1Z](https://stacks.math.columbia.edu/tag/0C1Z)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.Picard

open Stacks.RingedSpace (structureIsSheaf)

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
  (hdim : topologicalKrullDim X ≤ 1)

/-- An invertible module at the index of `Stacks.Picard.ofScheme` is invertible at the index
`AlgebraicGeometry.invertibleCurveDegree` is written over. -/
theorem isInvertible_ringCatSheaf_of_isInvertible (L : X.Modules)
    (hL : Stacks.SheafOfModules.IsInvertible X.presheaf (structureIsSheaf X.toRingedSpace) L) :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L :=
  (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ L).1 hL

/-- The degree of the chosen representative of a Picard class. -/
def ofSchemeDegreeFun (x : ofScheme X) : ℤ :=
  @invertibleCurveDegree k _ X f _ hdim (picardRepresentative X.toRingedSpace x).obj
    (isInvertible_ringCatSheaf_of_isInvertible _ (picardRepresentative X.toRingedSpace x).property)

/-- The degree of the representative of the class of `ℒ` is the degree of `ℒ`: the two modules
are isomorphic, and the degree is an isomorphism invariant. -/
theorem ofSchemeDegreeFun_picardClass (L : X.Modules)
    (hL : Stacks.SheafOfModules.IsInvertible X.presheaf (structureIsSheaf X.toRingedSpace) L) :
    ofSchemeDegreeFun k f hdim
        (Stacks.SheafOfModules.picardClass X.presheaf (structureIsSheaf X.toRingedSpace) L hL) =
      @invertibleCurveDegree k _ X f _ hdim L (isInvertible_ringCatSheaf_of_isInvertible L hL) := by
  have e := ((Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _ _ _).1
    (classOf_picardRepresentative X.toRingedSpace
      (Stacks.SheafOfModules.picardClass X.presheaf (structureIsSheaf X.toRingedSpace) L hL))).some
  let := isInvertible_ringCatSheaf_of_isInvertible L hL
  let := isInvertible_ringCatSheaf_of_isInvertible _
    (picardRepresentative X.toRingedSpace
      (Stacks.SheafOfModules.picardClass X.presheaf (structureIsSheaf X.toRingedSpace) L
        hL)).property
  exact invertibleCurveDegree_eq_of_iso k f hdim e

/-- **The degree homomorphism `deg : Pic(X) ⟶ ℤ`** of a scheme proper of dimension at most one
over a field: `[ℒ] ↦ deg ℒ`.  It is well defined because the degree is an isomorphism invariant,
and additive by [Stacks, Tag 0AYX],
`AlgebraicGeometry.invertibleCurveDegree_tensorSheaf_eq_add`. -/
def ofSchemeDegree : ofScheme X →+ ℤ :=
  AddMonoidHom.mk' (ofSchemeDegreeFun k f hdim) fun x y => by
    set Lx := picardRepresentative X.toRingedSpace x
    set Ly := picardRepresentative X.toRingedSpace y
    have hLxy : Stacks.SheafOfModules.IsInvertible X.presheaf
        (structureIsSheaf X.toRingedSpace)
        ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf,
          Presheaf.isSheaf_of_isSheaf_comp _ (X.presheaf) (forget₂ CommRingCat RingCat)
            ((structureIsSheaf X.toRingedSpace))⟩).obj (Lx.obj)).obj (Ly.obj))) :=
      @Stacks.SheafOfModules.isInvertible_tensorSheaf _ _ _ _ _ _ _ _ _ Lx.property Ly.property
    have hsum : x + y = Stacks.SheafOfModules.picardClass X.presheaf
        (structureIsSheaf X.toRingedSpace) _ hLxy := by
      conv_lhs => rw [← classOf_picardRepresentative X.toRingedSpace x,
        ← classOf_picardRepresentative X.toRingedSpace y]
      exact Stacks.SheafOfModules.picardClass_tensorSheaf _ _ _ _ _ _ hLxy
    rw [hsum]
    refine (ofSchemeDegreeFun_picardClass k f hdim _ hLxy).trans ?_
    let := isInvertible_ringCatSheaf_of_isInvertible _ Lx.property
    let := isInvertible_ringCatSheaf_of_isInvertible _ Ly.property
    let := isInvertible_ringCatSheaf_of_isInvertible _ hLxy
    exact invertibleCurveDegree_tensorSheaf_eq_add k f hdim Lx.obj Ly.obj

/-- **The degree of the class of an invertible module is the degree of that module.** -/
@[simp] theorem ofSchemeDegree_picardClass (L : X.Modules)
    (hL : Stacks.SheafOfModules.IsInvertible X.presheaf (structureIsSheaf X.toRingedSpace) L) :
    ofSchemeDegree k f hdim
        (Stacks.SheafOfModules.picardClass X.presheaf (structureIsSheaf X.toRingedSpace) L hL) =
      @invertibleCurveDegree k _ X f _ hdim L (isInvertible_ringCatSheaf_of_isInvertible L hL) :=
  ofSchemeDegreeFun_picardClass k f hdim L hL

/-- **`Pic⁰(X)`, the degree-zero Picard group**: the kernel of the degree homomorphism. -/
abbrev ofSchemeDegreeZero : AddSubgroup (ofScheme X) :=
  (ofSchemeDegree k f hdim).ker

/-- **A torsion class of `Pic(X)` has degree zero**, because `ℤ` is torsion free: for every
`m ≠ 0` the `m`-torsion of `Pic(X)` lies in `Pic⁰(X)`. -/
theorem torsionBy_le_ofSchemeDegreeZero {m : ℤ} (hm : m ≠ 0) :
    AddSubgroup.torsionBy (ofScheme X) m ≤ ofSchemeDegreeZero k f hdim := by
  intro x hx
  have hx' : m • x = 0 := hx
  have h : m * ofSchemeDegree k f hdim x = 0 := by
    have := congrArg (ofSchemeDegree k f hdim) hx'
    rwa [map_zsmul, map_zero, smul_eq_mul] at this
  exact (mul_eq_zero.1 h).resolve_left hm

/-- **The `m`-torsion of `Pic(X)` is the `m`-torsion of `Pic⁰(X)`**, for `m ≠ 0`. -/
def torsionByOfSchemeDegreeZeroAddEquiv {m : ℤ} (hm : m ≠ 0) :
    AddSubgroup.torsionBy (ofScheme X) m ≃+
      AddSubgroup.torsionBy (ofSchemeDegreeZero k f hdim) m where
  toFun x := ⟨⟨x.1, torsionBy_le_ofSchemeDegreeZero k f hdim hm x.2⟩,
    Subtype.ext x.2⟩
  invFun y := ⟨y.1.1, by
    change m • y.1.1 = 0
    exact congrArg Subtype.val (y.2 : m • y.1 = 0)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

end Stacks.Picard

end
