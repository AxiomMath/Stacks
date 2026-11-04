module

public import StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.Cohomology
public import StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.Evaluation

/-!
# Restriction and evaluation preserve acyclicity

Let `F : E ⥤ C` be a functor of differential graded categories over a commutative ring `R`.
The complex of the restriction `F^* M` at an object `e` of `E` is the complex of `M` at
`F e`, on the nose, so a right differential graded `C`-module whose complexes are all acyclic
restricts to a right differential graded `E`-module whose complexes are all acyclic.

For the one-object subcategory `E = C(K, K)` this says that evaluation at `K` carries acyclic
modules to acyclic modules, which is what makes evaluation descend from `K(Mod^dg(C))` to the
derived categories: `D(C) = K(Mod^dg(C))/Ac` and `D(E) = K(Mod^dg(E))/Ac`, and the exact
functor `ev_K` of
`StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.RestrictionExact` sends the first
class of objects into the second. Evaluation at `K` sees only the object `K`, so for it
acyclicity of `ev_K M` is exactly acyclicity of the single complex `M(K)`.

## Main results

* `DGCategory.RightModule.cochainComplex_restrict`: the complex of `F^* M` at `e` is the
  complex of `M` at `F e`.
* `DGCategory.RightModule.isAcyclic_restrict`: restriction preserves acyclicity.
* `DGCategory.isAcyclic_evaluation` and `DGCategory.isAcyclic_evaluation_iff`: evaluation at
  `K` preserves acyclicity, and `ev_K M` is acyclic exactly when the complex `M(K)` is.

## References

* [Stacks Project, Tag 09LK](https://stacks.math.columbia.edu/tag/09LK)
-/

@[expose] public section

namespace DGCategory

universe w v u r

variable {R : Type r} [CommRing R]

namespace RightModule

variable {E C : DGCategory.{v, u} R}

/-- The complex of the restriction `F^* M` at `e` is the complex of `M` at `F e`. -/
@[simp] theorem cochainComplex_restrict (F : DGFunctor E C) (M : RightModule.{w} C)
    (e : E.Obj) : (restrict F M).cochainComplex e = M.cochainComplex (F.obj e) := rfl

/-- The cohomology of the restriction `F^* M` at `e` is the cohomology of `M` at `F e`. -/
@[simp] theorem cohomology_restrict (F : DGFunctor E C) (M : RightModule.{w} C) (e : E.Obj)
    (n : ℤ) : (restrict F M).cohomology e n = M.cohomology (F.obj e) n := rfl

/-- **Restriction preserves acyclicity.** -/
theorem isAcyclic_restrict (F : DGFunctor E C) {M : RightModule.{w} C} (hM : M.IsAcyclic) :
    (restrict F M).IsAcyclic := fun e => hM (F.obj e)

end RightModule

variable (C : DGCategory.{v, u} R) (K : C.Obj)

/-- **Evaluation at `K` preserves acyclicity**, so it descends to the derived categories. -/
theorem isAcyclic_evaluation {M : RightModule.{w} C} (hM : M.IsAcyclic) :
    ((evaluationDGFunctor.{w} C K).obj M).IsAcyclic :=
  RightModule.isAcyclic_restrict (endDGInclusion C K) hM

/-- Evaluation at `K` sees only the object `K`: the evaluation of `M` is acyclic exactly when
the single complex `M(K)` is. -/
theorem isAcyclic_evaluation_iff (M : RightModule.{w} C) :
    ((evaluationDGFunctor.{w} C K).obj M).IsAcyclic ↔ (M.cochainComplex K).Acyclic :=
  ⟨fun h => h PUnit.unit, fun h _ => h⟩

end DGCategory
