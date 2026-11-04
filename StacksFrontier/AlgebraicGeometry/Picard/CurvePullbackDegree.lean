module

public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.DegreeComponents
public import StacksFrontier.AlgebraicGeometry.Picard.CurvePicardDegree
public import StacksFrontier.AlgebraicGeometry.InvertibleClasses.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.PullbackDegree

/-!
# The degree of a pulled back Picard class

For a nonconstant morphism `g : X ⟶ Y` of proper curves over a field `k`, pullback of line
bundles multiplies degrees by the degree of `g`:

`deg (g^* L) = deg(X/Y) · deg L`  for `L ∈ Pic(Y)`,

with `deg` the degree homomorphism `Stacks.Picard.picardDegree` and `deg(X/Y)` the degree of
the extension of function fields ([Stacks, Tag 0AYZ]).

## Main results

* `Stacks.Picard.picardDegree_schemePullbackClassHom`: the degree of the pullback of a Picard
  class along `g` is `deg(X/Y)` times the degree of the class.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.Picard

/-- **Pullback of line bundles along a nonconstant morphism of proper curves multiplies degrees
by the degree of the morphism** ([Stacks, Tag 0AYZ]): `deg (g^* L) = deg(X/Y) · deg L`. -/
theorem picardDegree_schemePullbackClassHom {k : Type u} [Field k] {X Y : Scheme.{u}}
    (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k)) [IsCurve k pX] [IsProper pX]
    [IsCurve k pY] [IsProper pY] (hdimX : topologicalKrullDim X ≤ 1)
    (hdimY : topologicalKrullDim Y ≤ 1) (g : X ⟶ Y) (hg : g ≫ pY = pX)
    (hgnc : ¬ ∃ y : Y, ∀ x : X, g.base x = y) (L : ofScheme Y) :
    picardDegree pX hdimX (schemePullbackClassHom g L) =
      (@degreeOver X Y g inferInstance inferInstance
          (locallyOfFiniteType_of_isCurve_comp k pX pY g hg)
          (isDominant_of_not_constant k pX pY g hgnc) : ℤ) * picardDegree pY hdimY L := by
  obtain ⟨e⟩ := Stacks.PicardCurve.nonempty_rep_schemePullbackClass_iso g L
  have hE : picardDegree pY hdimY L =
      curveDegree k pY hdimY (Stacks.PicardCurve.rep L) 1 := by
    rw [picardDegree_apply, picardDegreeFun]
    exact invertibleCurveDegree_eq_curveDegree_one k pY hdimY (Stacks.PicardCurve.rep L)
  have hP : picardDegree pX hdimX (schemePullbackClassHom g L) =
      curveDegree k pX hdimX (Stacks.PicardCurve.rep (schemePullbackClass g L)) 1 := by
    rw [picardDegree_apply, picardDegreeFun]
    exact invertibleCurveDegree_eq_curveDegree_one k pX hdimX
      (Stacks.PicardCurve.rep (schemePullbackClass g L))
  rw [hP, hE, curveDegree_eq_of_iso k pX hdimX 1 e]
  exact curveDegree_pullback_eq_degreeOver_mul k pX pY g hg hgnc _ 1

end Stacks.Picard

end
