module

public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.DegreeZeroDivisibility
public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.FibreDegreeAdd
public import StacksFrontier.AlgebraicGeometry.Picard.CurvePicardDegree

/-!
# Divisibility of `Pic⁰` of a curve, on `Stacks.Picard.ofScheme`

The library has two models of the Picard group of a scheme: `Stacks.Picard.ofScheme`, on which
the étale cohomology of curves (`Stacks.Picard.picardDegree`, the Kummer and trace maps) is
written, and `AlgebraicGeometry.schemePicard`, on which the Jacobian and the divisibility of
`Pic⁰` (`AlgebraicGeometry.exists_nsmul_eq_of_mem_picardDegreeZero`) are written. They are
matched by `Stacks.GluePicard.picardModelAddEquiv`, which carries one degree to the other
(`Stacks.Picard.picardDegree_picardModelAddEquiv`). Hence the degree-zero classes of
`Stacks.Picard.ofScheme X` are `n`-divisible for `n` invertible in the algebraically closed
base field (`Stacks.Picard.exists_nsmul_eq_of_picardDegree_eq_zero`).

## Main results

* `Stacks.Picard.picardDegree_picardModelAddEquiv`: the two degrees agree.
* `Stacks.Picard.exists_nsmul_eq_of_picardDegree_eq_zero`: `Pic⁰(X)` is `n`-divisible.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Picard

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] [IsCurve k f]
  (hdim : topologicalKrullDim X ≤ 1)

/-- **The two degrees on the Picard group agree** under the identification
`Stacks.GluePicard.picardModelAddEquiv` of `Stacks.Picard.ofScheme X` with
`AlgebraicGeometry.schemePicard X`. -/
theorem picardDegree_picardModelAddEquiv (y : ofScheme X) :
    AlgebraicGeometry.picardDegree k f hdim
        (Stacks.GluePicard.picardModelAddEquiv X.toRingedSpace y) =
      Stacks.Picard.picardDegree f hdim y := by
  have hS : Stacks.SheafOfModules.IsInvertible X.presheaf
      (AlgebraicGeometry.SmallEtale.zariskiStructureIsSheaf X) (Stacks.PicardCurve.rep y) :=
    (Stacks.Picard.picardRepresentative X.toRingedSpace y).property
  have hy : Stacks.GluePicard.picardModelAddEquiv X.toRingedSpace y =
      schemePicardClassOf X (Stacks.PicardCurve.rep y) hS :=
    (congrArg (Stacks.GluePicard.picardModelAddEquiv X.toRingedSpace)
      (Stacks.Picard.classOf_picardRepresentative X.toRingedSpace y)).symm.trans
      (Stacks.GluePicard.picardModelAddEquiv_classOf _ _ hS)
  rw [hy, picardDegree_classOf]
  rfl

/-- **`Pic⁰(X)` is `n`-divisible** for a smooth proper curve `X` over an algebraically closed
field `k` and `n` invertible in `k`: every class of degree zero is `n` times a class. This is
Tag 03RP (4) for the Jacobian, transported to `Stacks.Picard.ofScheme`. -/
theorem exists_nsmul_eq_of_picardDegree_eq_zero [IsAlgClosed k] [Smooth f]
    {n : ℕ} (hn : IsUnit (n : k)) (L : ofScheme X) (hL : Stacks.Picard.picardDegree f hdim L = 0) :
    ∃ M : ofScheme X, n • M = L := by
  set e := Stacks.GluePicard.picardModelAddEquiv X.toRingedSpace
  have hx : e L ∈ picardDegreeZero k f hdim := by
    rw [AlgebraicGeometry.mem_picardDegreeZero_iff, picardDegree_picardModelAddEquiv, hL]
  obtain ⟨y, hy⟩ := exists_nsmul_eq_of_mem_picardDegreeZero f hdim hn ⟨e L, hx⟩
  refine ⟨e.symm y, ?_⟩
  rw [← map_nsmul, show n • (y : schemePicard X) = e L from congrArg Subtype.val hy,
    AddEquiv.symm_apply_apply]

end Stacks.Picard

end
