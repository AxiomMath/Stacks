module

public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech

/-!
# Exactness of the Čech complex functor

Let `U : ι → C` be a family of objects of a category with finite products and let `A` be a
preadditive category with `ι`-indexed products. Mathlib's `CategoryTheory.cechComplexFunctor`
sends a presheaf `P : Cᵒᵖ ⥤ A` to its Čech cochain complex. This file proves that this functor
is exact: it preserves finite limits, and it preserves finite colimits as soon as `ι`-indexed
products in `A` are exact, Grothendieck's axiom AB4*. Hence it preserves homology, which is
what allows a Čech complex to be moved through a homology functor or through a right derived
functor.

The Čech complex functor is a composite of three layers, and the proof treats them one by one:
`CategoryTheory.Limits.FormalCoproduct.evalOp`, which evaluates a presheaf on formal
coproducts; restriction along the Čech simplicial object, which is a
`CategoryTheory.Functor.whiskeringLeft` and is already covered by Mathlib; and
`AlgebraicTopology.alternatingCofaceMapComplex`.

## Main definitions

* `evalOpCompEvaluationIso`: evaluating `FormalCoproduct.evalOp` at a formal coproduct `Y` is
  restriction along the discrete diagram of the summands of `Y` followed by `lim`.
* `alternatingCofaceMapComplexCompEval`: the degree `n` term of the alternating coface map
  complex of a cosimplicial object is its value at `⦋n⦌`.

## Main results

* `preservesFiniteLimits_evalOp` and `preservesFiniteColimits_evalOp`: evaluation of
  presheaves on formal coproducts is exact, the second half under AB4*.
* `preservesFiniteLimits_alternatingCofaceMapComplex` and
  `preservesFiniteColimits_alternatingCofaceMapComplex`.
* `preservesFiniteLimits_cechComplexFunctor`, `preservesFiniteColimits_cechComplexFunctor`,
  `cechComplexFunctor_exact` and `preservesHomology_cechComplexFunctor`: the Čech complex
  functor is exact and preserves homology.

## Implementation notes

The index type `ι` of the family lies in its own universe `w`, independent of the universes
of `C` and of `A`, exactly as `CategoryTheory.cechComplexFunctor` asks; the summand types of
the formal coproducts occurring in its construction lie in the same universe. Exactness of
those products is `CategoryTheory.AB4StarOfSize.{w} A`, which Mathlib provides for
`AddCommGrpCat.{w}` and for `ModuleCat.{w} R`.

Preservation of finite limits needs no hypothesis beyond finite limits in `A`, since `lim`
over a discrete diagram is a right adjoint. AB4* enters only for finite colimits, and only
through `FormalCoproduct.evalOp`.

Both comparison isomorphisms are identities on components. In `evalOpCompEvaluationIso` the
two sides are nevertheless not definitionally equal, because a product over a discrete
diagram of values of a presheaf is a different limit from the limit of the composite of the
presheaf with the discrete diagram; the components are therefore `HasLimit.isoOfNatIso` of
the identity natural isomorphism rather than `Iso.refl`.

## References

* [Stacks Project, Tag 01EJ](https://stacks.math.columbia.edu/tag/01EJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe w v v' u u'

namespace Stacks.CategoryTheory.CechComplex

noncomputable section

/-! ### Presheaves evaluated on formal coproducts -/

section FormalCoproducts

variable (C : Type u) [Category.{v} C] (A : Type u') [Category.{v'} A] [HasProducts.{w} A]

/-- Evaluating `CategoryTheory.Limits.FormalCoproduct.evalOp` at a formal coproduct `Y` is the
functor taking a presheaf to the product, over the summands of `Y`, of its values on those
summands: restriction along the discrete diagram of the summands, followed by `lim`. -/
def evalOpCompEvaluationIso (Y : (FormalCoproduct.{w} C)ᵒᵖ) :
    FormalCoproduct.evalOp.{w} C A ⋙ (evaluation (FormalCoproduct.{w} C)ᵒᵖ A).obj Y ≅
      (Functor.whiskeringLeft (Discrete Y.unop.I) Cᵒᵖ A).obj
          (Discrete.functor fun i ↦ op (Y.unop.obj i)) ⋙ lim :=
  NatIso.ofComponents
    (fun _ ↦ HasLimit.isoOfNatIso (Discrete.natIso fun _ ↦ Iso.refl _))
    (fun α ↦ limit.hom_ext fun ⟨i⟩ ↦ by simp [FormalCoproduct.evalOp])

/-- Evaluation of presheaves on formal coproducts preserves finite limits: evaluationwise it
is a restriction functor followed by `lim`, and both preserve limits. -/
instance preservesFiniteLimits_evalOp [HasFiniteLimits A] :
    PreservesFiniteLimits (FormalCoproduct.evalOp.{w} C A) :=
  preservesFiniteLimits_of_evaluation _ fun Y ↦
    preservesFiniteLimits_of_natIso (evalOpCompEvaluationIso.{w} C A Y).symm

/-- Evaluation of presheaves on formal coproducts preserves finite colimits, provided
products indexed by the summand types are exact, that is, provided `A` satisfies AB4*. -/
instance preservesFiniteColimits_evalOp [HasFiniteColimits A] [AB4StarOfSize.{w} A] :
    PreservesFiniteColimits (FormalCoproduct.evalOp.{w} C A) :=
  preservesFiniteColimits_of_evaluation _ fun Y ↦
    preservesFiniteColimits_of_natIso (evalOpCompEvaluationIso.{w} C A Y).symm

end FormalCoproducts

/-! ### The alternating coface map complex -/

section Cosimplicial

variable (A : Type u') [Category.{v'} A] [Preadditive A]

/-- The degree `n` term of the alternating coface map complex of a cosimplicial object is the
value of that object at `⦋n⦌`. -/
def alternatingCofaceMapComplexCompEval (n : ℕ) :
    AlgebraicTopology.alternatingCofaceMapComplex A ⋙
        HomologicalComplex.eval A (ComplexShape.up ℕ) n ≅
      (evaluation SimplexCategory A).obj ⦋n⦌ :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) fun _ ↦
    (Category.comp_id _).trans (Category.id_comp _).symm

/-- The alternating coface map complex functor preserves finite limits, because limits of
complexes are computed degreewise and each degree is an evaluation. -/
instance preservesFiniteLimits_alternatingCofaceMapComplex [HasFiniteLimits A] :
    PreservesFiniteLimits (AlgebraicTopology.alternatingCofaceMapComplex A) where
  preservesFiniteLimits _ _ _ :=
    HomologicalComplex.preservesLimitsOfShape_of_eval _ fun n ↦
      preservesLimitsOfShape_of_natIso (alternatingCofaceMapComplexCompEval A n).symm

/-- The alternating coface map complex functor preserves finite colimits, because colimits of
complexes are computed degreewise and each degree is an evaluation. -/
instance preservesFiniteColimits_alternatingCofaceMapComplex [HasFiniteColimits A] :
    PreservesFiniteColimits (AlgebraicTopology.alternatingCofaceMapComplex A) where
  preservesFiniteColimits _ _ _ :=
    HomologicalComplex.preservesColimitsOfShape_of_eval _ fun n ↦
      preservesColimitsOfShape_of_natIso (alternatingCofaceMapComplexCompEval A n).symm

end Cosimplicial

/-! ### The Čech complex functor -/

section Cech

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C]
  {A : Type u'} [Category.{v'} A] [Preadditive A] [HasProducts.{w} A]
  {ι : Type w} (U : ι → C)

/-- **The Čech complex functor preserves finite limits.** It is the composite of evaluation
on formal coproducts, restriction along the Čech simplicial object, and the alternating
coface map complex, each of which preserves finite limits. -/
instance preservesFiniteLimits_cechComplexFunctor [HasFiniteLimits A] :
    PreservesFiniteLimits (cechComplexFunctor (A := A) U) := by
  unfold cechComplexFunctor FormalCoproduct.cochainComplexFunctor
    FormalCoproduct.cosimplicialObjectFunctor
  infer_instance

/-- **The Čech complex functor preserves finite colimits** when products indexed by the index
type of the family are exact in `A`, Grothendieck's axiom AB4*. This is the only place the
axiom is used, and it is used only for the evaluation of presheaves on formal coproducts. -/
instance preservesFiniteColimits_cechComplexFunctor
    [HasFiniteColimits A] [AB4StarOfSize.{w} A] :
    PreservesFiniteColimits (cechComplexFunctor (A := A) U) := by
  unfold cechComplexFunctor FormalCoproduct.cochainComplexFunctor
    FormalCoproduct.cosimplicialObjectFunctor
  infer_instance

/-- **The Čech complex functor is exact**: it preserves both finite limits and finite
colimits, the latter under AB4* for the index type of the family. -/
theorem cechComplexFunctor_exact
    [HasFiniteLimits A] [HasFiniteColimits A] [AB4StarOfSize.{w} A] :
    exactFunctor (Cᵒᵖ ⥤ A) (CochainComplex A ℕ) (cechComplexFunctor (A := A) U) :=
  (exactFunctor_iff _).2 ⟨inferInstance, inferInstance⟩

/-- **The Čech complex functor preserves homology**, being exact. This is what allows the
Čech complex of a complex of presheaves to be compared with the Čech complex of its homology
presheaves, and a Čech complex to be pulled out of a right derived functor. -/
instance preservesHomology_cechComplexFunctor
    [HasZeroObject A] [HasFiniteLimits A] [HasFiniteColimits A] [AB4StarOfSize.{w} A] :
    (cechComplexFunctor (A := A) U).PreservesHomology :=
  inferInstance

end Cech

end

end Stacks.CategoryTheory.CechComplex

end
