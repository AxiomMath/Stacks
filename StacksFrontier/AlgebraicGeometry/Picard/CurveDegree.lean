module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PicardTransport
public import StacksFrontier.AlgebraicGeometry.CurveDegreeTensor.Cohomological
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.Basic
public import StacksFrontier.AlgebraicGeometry.InvertibleClasses.Basic
public import StacksFrontier.AlgebraicGeometry.Picard.SmallEtaleAssociatedModulePicard

/-!
# The degree homomorphism on the Picard group of a proper curve

Let `X` be a proper scheme of dimension at most one over a field `k`. The degree of an
invertible `𝒪_X`-module depends only on its isomorphism class and is additive in the tensor
product, so it descends to a homomorphism of abelian groups

`deg : Pic(X) ⟶ 𝐙`,

whose kernel is the degree-zero Picard group `Pic⁰(X)`.

## Main definitions

* `AlgebraicGeometry.picardDegree` — the degree homomorphism `Pic(X) ⟶ 𝐙`.
* `AlgebraicGeometry.picardDegreeZero` — `Pic⁰(X)`, the kernel of the degree.

## Main results

* `AlgebraicGeometry.picardDegree_classOf` — the degree of the class of an invertible module is
  the degree of that module, which fixes the homomorphism rather than only asserting that one
  exists.
* `AlgebraicGeometry.mem_picardDegreeZero_of_nsmul_eq_zero` — a torsion class has degree zero, so
  the `n`-torsion of `Pic(X)` is the `n`-torsion of `Pic⁰(X)`.

## Implementation notes

`Pic(X)` is `Stacks.SheafOfModules.Picard.PicardGroup X.presheaf
(AlgebraicGeometry.SmallEtale.zariskiStructureIsSheaf X)`, the group of Tag 01CX, which is the
spelling in which Tag 03P8 produces it. Its invertible modules are
`AlgebraicGeometry.Scheme.Modules` on the nose, so `AlgebraicGeometry.invertibleCurveDegree`
applies to them with no transport; only the two invertibility predicates of Tag 01CS have to be
crossed, by `Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry`.

The degree is defined by choosing an invertible module in the class, which
`Stacks.SheafOfModules.Picard.exists_classOf_eq` provides, and
`AlgebraicGeometry.picardDegree_classOf` then shows the choice is immaterial: two invertible
modules with the same class are isomorphic by
`Stacks.SheafOfModules.Picard.classOf_eq_classOf_iff`, and the degree is an isomorphism invariant
by `AlgebraicGeometry.invertibleCurveDegree_eq_of_iso`. Additivity is Tag 0AYX at rank one,
`AlgebraicGeometry.curveDegree_tensorSheaf_eq_add`, for which the curve hypothesis is needed; the
definition itself and `picardDegree_classOf` need only properness and the dimension bound.

## References

* [Stacks Project, Tag 01CX](https://stacks.math.columbia.edu/tag/01CX)
* [Stacks Project, Tag 0AYR](https://stacks.math.columbia.edu/tag/0AYR)
* [Stacks Project, Tag 0AYX](https://stacks.math.columbia.edu/tag/0AYX)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

open AlgebraicGeometry.SmallEtale (zariskiStructureIsSheaf)

attribute [local instance] AlgebraicGeometry.SmallEtale.zariskiPicardAddCommGroup

/-- `Pic(X)`, the Picard group of Tag 01CX of a scheme `X`, in the spelling Tag 03P8 produces. -/
public abbrev schemePicard (X : Scheme.{u}) : Type u :=
  Stacks.SheafOfModules.Picard.PicardGroup X.presheaf (zariskiStructureIsSheaf X)

/-- The class in `Pic(X)` of an invertible `𝒪_X`-module. -/
public abbrev schemePicardClassOf (X : Scheme.{u}) (L : X.Modules)
    (hL : Stacks.SheafOfModules.IsInvertible X.presheaf (zariskiStructureIsSheaf X) L) :
    schemePicard X :=
  Stacks.SheafOfModules.Picard.classOf X.presheaf (zariskiStructureIsSheaf X) L hL

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
  (hdim : topologicalKrullDim X ≤ 1)

/-- The two invertibility predicates of Tag 01CS, crossed in the direction the degree needs. -/
public theorem isInvertible_of_stacks_isInvertible (X : Scheme.{u}) (L : X.Modules)
    (hL : Stacks.SheafOfModules.IsInvertible X.presheaf (zariskiStructureIsSheaf X) L) :
    SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L :=
  (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry X.presheaf
    (zariskiStructureIsSheaf X) L).1 hL

/-- **The degree of a Picard class on a proper scheme of dimension at most one over a field**:
the degree of any invertible module in the class, which
`AlgebraicGeometry.picardDegree_classOf` shows is well defined. -/
public def picardDegreeFun (x : schemePicard X) : ℤ :=
  letI := isInvertible_of_stacks_isInvertible X
    (Stacks.SheafOfModules.Picard.exists_classOf_eq X.presheaf (zariskiStructureIsSheaf X) x).choose
    (Stacks.SheafOfModules.Picard.exists_classOf_eq X.presheaf
      (zariskiStructureIsSheaf X) x).choose_spec.choose
  invertibleCurveDegree k f hdim
    (Stacks.SheafOfModules.Picard.exists_classOf_eq X.presheaf (zariskiStructureIsSheaf X) x).choose

/-- **The degree of the class of an invertible module is the degree of that module.** -/
public theorem picardDegreeFun_classOf (L : X.Modules)
    (hL : Stacks.SheafOfModules.IsInvertible X.presheaf (zariskiStructureIsSheaf X) L) :
    letI := isInvertible_of_stacks_isInvertible X L hL
    picardDegreeFun k f hdim (schemePicardClassOf X L hL) = invertibleCurveDegree k f hdim L := by
  let := isInvertible_of_stacks_isInvertible X L hL
  set x := schemePicardClassOf X L hL with hx
  obtain ⟨e⟩ := (Stacks.SheafOfModules.Picard.classOf_eq_classOf_iff X.presheaf
      (zariskiStructureIsSheaf X) _ L
      (Stacks.SheafOfModules.Picard.exists_classOf_eq X.presheaf
        (zariskiStructureIsSheaf X) x).choose_spec.choose hL).1
    ((Stacks.SheafOfModules.Picard.exists_classOf_eq X.presheaf
      (zariskiStructureIsSheaf X) x).choose_spec.choose_spec.trans hx)
  let := isInvertible_of_stacks_isInvertible X
    (Stacks.SheafOfModules.Picard.exists_classOf_eq X.presheaf (zariskiStructureIsSheaf X) x).choose
    (Stacks.SheafOfModules.Picard.exists_classOf_eq X.presheaf
      (zariskiStructureIsSheaf X) x).choose_spec.choose
  exact invertibleCurveDegree_eq_of_iso k f hdim e

variable [IsCurve k f]

/-- **Tag 0AYX at rank one**: the degree of a tensor product of invertible modules on a proper
curve is the sum of the degrees. -/
public theorem invertibleCurveDegree_tensorStalkSheaf_eq_add (L N : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨(X.toRingedSpace).presheaf, (X.toRingedSpace).IsSheaf⟩).obj (L)).obj (N))))] :
    invertibleCurveDegree k f hdim
        (((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨(X.toRingedSpace).presheaf, (X.toRingedSpace).IsSheaf⟩).obj (L)).obj (N)))) =
      invertibleCurveDegree k f hdim L + invertibleCurveDegree k f hdim N := by
  have h1 := invertibleCurveDegree_eq_curveDegree_one k f hdim
    (((((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨(X.toRingedSpace).presheaf, (X.toRingedSpace).IsSheaf⟩).obj (L)).obj (N))))
  have h2 := curveDegree_tensorSheaf_eq_add k f hdim L N 1 1
  have h3 := invertibleCurveDegree_eq_curveDegree_one k f hdim L
  have h4 := invertibleCurveDegree_eq_curveDegree_one k f hdim N
  rw [h1, h3, h4]
  exact h2.trans (by push_cast; ring)

/-- **The degree is additive in the Picard group.** This is Tag 0AYX at rank one. -/
public theorem picardDegreeFun_add (x y : schemePicard X) :
    picardDegreeFun k f hdim (x + y) =
      picardDegreeFun k f hdim x + picardDegreeFun k f hdim y := by
  obtain ⟨L, hL, rfl⟩ :=
    Stacks.SheafOfModules.Picard.exists_classOf_eq X.presheaf (zariskiStructureIsSheaf X) x
  obtain ⟨N, hN, rfl⟩ :=
    Stacks.SheafOfModules.Picard.exists_classOf_eq X.presheaf (zariskiStructureIsSheaf X) y
  have hLN := Stacks.SheafOfModules.isInvertible_tensorSheaf X.presheaf
    (zariskiStructureIsSheaf X) L N
  let := isInvertible_of_stacks_isInvertible X L hL
  let := isInvertible_of_stacks_isInvertible X N hN
  let := isInvertible_of_stacks_isInvertible X _ hLN
  rw [Stacks.SheafOfModules.Picard.classOf_tensor X.presheaf (zariskiStructureIsSheaf X) L N
    hL hN hLN, picardDegreeFun_classOf k f hdim _ hLN, picardDegreeFun_classOf k f hdim L hL,
    picardDegreeFun_classOf k f hdim N hN]
  exact invertibleCurveDegree_tensorStalkSheaf_eq_add k f hdim L N

/-- **The degree homomorphism `deg : Pic(X) ⟶ 𝐙`** of a curve proper over a field. -/
public def picardDegree : schemePicard X →+ ℤ :=
  AddMonoidHom.mk' (picardDegreeFun k f hdim) (picardDegreeFun_add k f hdim)

/-- **The degree of the class of an invertible module is the degree of that module**, which fixes
the homomorphism rather than only asserting that one exists. -/
public theorem picardDegree_classOf (L : X.Modules)
    (hL : Stacks.SheafOfModules.IsInvertible X.presheaf (zariskiStructureIsSheaf X) L) :
    letI := isInvertible_of_stacks_isInvertible X L hL
    picardDegree k f hdim (schemePicardClassOf X L hL) = invertibleCurveDegree k f hdim L :=
  picardDegreeFun_classOf k f hdim L hL

/-- **`Pic⁰(X)`, the degree-zero Picard group**: the kernel of the degree homomorphism. -/
public def picardDegreeZero : AddSubgroup (schemePicard X) :=
  (picardDegree k f hdim).ker

/-- A class lies in `Pic⁰(X)` if and only if its degree is zero. -/
@[simp] public theorem mem_picardDegreeZero_iff (x : schemePicard X) :
    x ∈ picardDegreeZero k f hdim ↔ picardDegree k f hdim x = 0 :=
  Iff.rfl

/-- **A torsion class of `Pic(X)` has degree zero**, because `𝐙` is torsion free. Hence the
`n`-torsion of `Pic(X)` and the `n`-torsion of `Pic⁰(X)` are the same subgroup, for every
`n ≥ 1`. -/
public theorem mem_picardDegreeZero_of_nsmul_eq_zero {n : ℕ} (hn : n ≠ 0) (x : schemePicard X)
    (hx : n • x = 0) : x ∈ picardDegreeZero k f hdim := by
  have h : (n : ℤ) * picardDegree k f hdim x = 0 := by
    have := congrArg (picardDegree k f hdim) hx
    rw [map_nsmul, map_zero, nsmul_eq_mul] at this
    exact this
  exact (mul_eq_zero.1 h).resolve_left (Nat.cast_ne_zero.2 hn)

end AlgebraicGeometry

end
