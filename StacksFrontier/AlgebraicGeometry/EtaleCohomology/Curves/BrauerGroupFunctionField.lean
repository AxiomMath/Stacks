module

public import Mathlib.AlgebraicGeometry.FunctionField
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.TranscendenceDegreeOneBrauer
public import StacksFrontier.AlgebraicGeometry.FunctionField.DominantMap
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.ResidueField
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Trdeg
public import StacksCore.Tactic.StacksAttribute

/-!
# The Brauer group of the function field of a curve

The function field of a curve over an algebraically closed field `k` is a finitely generated
extension of `k` of transcendence degree one, so Tsen's theorem makes it a `C₁` field and its
Brauer group is trivial.

## Main results

* `AlgebraicGeometry.trdeg_residueField_genericPoint_eq_one`: the residue field of a curve at its
  generic point has transcendence degree one over the base field.
* `AlgebraicGeometry.isCField_one_residueField_genericPoint`: over an algebraically closed field
  that residue field is a `C₁` field.
* `AlgebraicGeometry.isCField_one_functionField`: the function field of a curve over an
  algebraically closed field is a `C₁` field.
* `AlgebraicGeometry.brauerGroup_functionField_eq_one`: its Brauer group is trivial.

## References

* [Stacks Project, Tag 03RF](https://stacks.math.columbia.edu/tag/03RF)
* [Stacks Project, Tag 0A21](https://stacks.math.columbia.edu/tag/0A21)
* [Stacks Project, Tag 03RC](https://stacks.math.columbia.edu/tag/03RC)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open CommRingCat

universe u

namespace AlgebraicGeometry

/-- The residue field of a curve at its generic point has transcendence degree one over the base
field. -/
theorem trdeg_residueField_genericPoint_eq_one (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsCurve k f] :
    letI : Algebra k (X.residueField (genericPoint X)) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
        X.Γevaluation (genericPoint X)).hom.toAlgebra
    Algebra.trdeg k (X.residueField (genericPoint X)) = 1 := by
  let : Algebra k (X.residueField (genericPoint X)) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
      X.Γevaluation (genericPoint X)).hom.toAlgebra
  have h := topologicalKrullDim_eq_trdeg_residueField k X f (genericPoint X)
    (genericPoint_spec X)
  rw [IsCurve.topologicalKrullDim_eq_one (k := k) (f := f)] at h
  have h1 : (1 : ℕ∞) = Cardinal.toENat (Algebra.trdeg k (X.residueField (genericPoint X))) :=
    mod_cast h
  simpa using h1.symm

/-- The residue field of a curve over an algebraically closed field at its generic point is a
`C₁` field. -/
theorem isCField_one_residueField_genericPoint (k : Type u) [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve k f] :
    IsCField (X.residueField (genericPoint X)) 1 := by
  let : Algebra k (X.residueField (genericPoint X)) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
      X.Γevaluation (genericPoint X)).hom.toAlgebra
  have : Algebra.EssFiniteType k (X.residueField (genericPoint X)) :=
    residueField_essFiniteType k f (genericPoint X)
  exact isCField_one_of_essFiniteType_trdeg_eq_one k (X.residueField (genericPoint X))
    (trdeg_residueField_genericPoint_eq_one k f)

/-- The function field of a curve over an algebraically closed field is a `C₁` field. -/
theorem isCField_one_functionField (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsCurve k f] : IsCField X.functionField 1 :=
  IsCField.of_ringEquiv (isCField_one_residueField_genericPoint k f)
    (genericResidueEquiv X).symm

/-- The Brauer group of the function field of a curve over an algebraically closed field is
trivial. -/
@[stacks 03RF, sga "4½ Arcata 3.2.4" "q = 2 (Brauer group)", sga "4½ Arcata 3.2.2" "special case"]
theorem brauerGroup_functionField_eq_one (k : Type u) [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve k f]
    (y : BrauerGroup X.functionField) : y = 1 :=
  brauerGroup_eq_one_of_isCField X.functionField (isCField_one_functionField k f) y

end AlgebraicGeometry

end
