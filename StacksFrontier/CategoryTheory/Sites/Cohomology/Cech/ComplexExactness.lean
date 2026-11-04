module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.ComplexAsBoundedBelowFunctor
import StacksCore.Tactic.StacksAttribute

/-!
# Exactness of the Čech complex functor

Let `E` be a family of morphisms of a category with fixed target `X`, all of whose finite
nonempty fibre products exist. Stacks 03AQ is the assertion that the functor of Stacks 03AP,
sending a presheaf of abelian groups to its bounded-below Čech complex, is exact.

Exactness is proved factor by factor along the definition of the Čech complex functor. The
functor is a composite of four steps: restriction of a presheaf on `C` to a presheaf on
`Over X`, evaluation of the resulting presheaf on the formal coproducts
`U_{i_0} ×_X … ×_X U_{i_p}`, the alternating-face-map complex of the resulting cosimplicial
object, and extension by zero from an `ℕ`-grading to a `ℤ`-grading. Restriction and the
alternating-face-map complex are computed termwise, so they are exact as soon as evaluation
is; evaluation at a formal coproduct is a product of evaluations, so it is exact because
abelian groups satisfy `AB4` and `AB4*` in the relevant size; and extension by zero is exact
because in each degree it is either an evaluation or zero. Finally exactness transports from
the composite with the fully faithful inclusion `CochainComplex.Plus.ι` back to the functor.

## Main results

* `Stacks.CechSite.cechComplexPlusFunctor_exact`: the Čech complex functor on presheaves of
  abelian groups is exact.

## Implementation notes

Presheaves of abelian groups are the functor category `Cᵒᵖ ⥤ AddCommGrpCat`, and exactness is
Mathlib's bundled `CategoryTheory.Limits.exactFunctor`, namely preservation of finite limits
together with preservation of finite colimits.

The universe of the abelian groups is enlarged to `max w uAb` so that it contains the universe
`w` indexing the products which the Čech complex takes; this is what makes those products, and
the `AB4*` property controlling their exactness, available.

## References

* [Stacks Project, Tag 03AQ](https://stacks.math.columbia.edu/tag/03AQ)
* [Stacks Project, Tag 03AP](https://stacks.math.columbia.edu/tag/03AP)
* [Stacks Project, Tag 03AM](https://stacks.math.columbia.edu/tag/03AM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u uAb vA uA

namespace Stacks.CechSite

variable {C : Type u} [Category.{v} C] {X : C} (E : PreZeroHypercover.{w} X)

/-- Taking the bounded-below Čech complex of a presheaf of abelian groups is an exact functor. -/
@[stacks 03AQ]
theorem cechComplexPlusFunctor_exact
    [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀),
      HasProduct (fun a ↦ Over.mk (E.f (i a)))] :
    exactFunctor
      (CategoryTheory.Functor Cᵒᵖ AddCommGrpCat.{max w uAb})
      (CochainComplex.Plus AddCommGrpCat.{max w uAb})
      (cechComplexPlusFunctor (A := AddCommGrpCat.{max w uAb}) E) := by
  let A := AddCommGrpCat.{max w uAb}
  have : AB4StarOfSize.{w} A := ⟨fun I ↦
    HasExactLimitsOfShape.of_domain_equivalence A
      (Discrete.equivalence (Equiv.ulift.{uAb} : ULift.{uAb} I ≃ I))⟩
  have : PreservesFiniteLimits (FormalCoproduct.evalOp.{w} (Over X) A) :=
    preservesFiniteLimits_of_evaluation _ fun T ↦
      preservesFiniteLimits_of_natIso (evalOpCompEvaluationIso T.unop).symm
  have : PreservesFiniteColimits (FormalCoproduct.evalOp.{w} (Over X) A) :=
    preservesFiniteColimits_of_evaluation _ fun T ↦
      preservesFiniteColimits_of_natIso (evalOpCompEvaluationIso T.unop).symm
  have : PreservesFiniteLimits (AlgebraicTopology.alternatingCofaceMapComplex A) :=
    ⟨fun J _ _ ↦ by
      refine HomologicalComplex.preservesLimitsOfShape_of_eval _ fun n ↦ ?_
      change PreservesLimitsOfShape J ((evaluation SimplexCategory A).obj (SimplexCategory.mk n))
      infer_instance⟩
  have : PreservesFiniteColimits (AlgebraicTopology.alternatingCofaceMapComplex A) :=
    ⟨fun J _ _ ↦ by
      refine HomologicalComplex.preservesColimitsOfShape_of_eval _ fun n ↦ ?_
      change PreservesColimitsOfShape J ((evaluation SimplexCategory A).obj (SimplexCategory.mk n))
      infer_instance⟩
  have : PreservesFiniteLimits (cechComplexFunctor (A := A) E) := by
    unfold cechComplexFunctor FormalCoproduct.cochainComplexFunctor
      FormalCoproduct.cosimplicialObjectFunctor
    infer_instance
  have : PreservesFiniteColimits (cechComplexFunctor (A := A) E) := by
    unfold cechComplexFunctor FormalCoproduct.cochainComplexFunctor
      FormalCoproduct.cosimplicialObjectFunctor
    infer_instance
  have : PreservesFiniteLimits (ComplexShape.embeddingUpNat.extendFunctor A) :=
    ⟨fun J _ _ ↦ by
      refine HomologicalComplex.preservesLimitsOfShape_of_eval _ fun i' ↦ ?_
      by_cases h : ∃ i, ComplexShape.embeddingUpNat.f i = i'
      · obtain ⟨i, hi⟩ := h
        exact preservesLimitsOfShape_of_natIso
          (ComplexShape.embeddingUpNat.extendFunctorCompEvalIso A hi).symm
      · exact Functor.preservesLimitsOfShape_of_isZero _
          ((Functor.isZero_iff _).2 fun K ↦ K.isZero_extend_X _ i' (by simpa using h)) _⟩
  have : PreservesFiniteColimits (ComplexShape.embeddingUpNat.extendFunctor A) :=
    ⟨fun J _ _ ↦ by
      refine HomologicalComplex.preservesColimitsOfShape_of_eval _ fun i' ↦ ?_
      by_cases h : ∃ i, ComplexShape.embeddingUpNat.f i = i'
      · obtain ⟨i, hi⟩ := h
        exact preservesColimitsOfShape_of_natIso
          (ComplexShape.embeddingUpNat.extendFunctorCompEvalIso A hi).symm
      · exact Functor.preservesColimitsOfShape_of_isZero _
          ((Functor.isZero_iff _).2 fun K ↦ K.isZero_extend_X _ i' (by simpa using h)) _⟩
  have : PreservesFiniteLimits
      (cechComplexPlusFunctor (A := A) E ⋙ CochainComplex.Plus.ι A) := by
    change PreservesFiniteLimits
      (cechComplexFunctor E ⋙ ComplexShape.embeddingUpNat.extendFunctor A)
    infer_instance
  have : PreservesFiniteColimits
      (cechComplexPlusFunctor (A := A) E ⋙ CochainComplex.Plus.ι A) := by
    change PreservesFiniteColimits
      (cechComplexFunctor E ⋙ ComplexShape.embeddingUpNat.extendFunctor A)
    infer_instance
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves _ (CochainComplex.Plus.ι A),
    preservesFiniteColimits_of_reflects_of_preserves _ (CochainComplex.Plus.ι A)⟩

end Stacks.CechSite
