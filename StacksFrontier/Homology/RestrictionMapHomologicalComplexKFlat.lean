module

public import StacksFrontier.Homology.ConstMapHomologicalComplexKFlat

/-!
# K-flatness of a complex of diagrams is a pointwise condition

Let `J` be a category and `D` a monoidal abelian category whose tensor product commutes with the
coproducts occurring in a total complex, so that both `CochainComplex D ℤ` and
`CochainComplex (J ⥤ D) ℤ` carry the total tensor product of `Mathlib.Algebra.Homology.Monoidal`
(the latter by `StacksFrontier.CategoryTheory.Monoidal.FunctorCategoryTensorColimits`).  This file
proves that a complex of diagrams is K-flat exactly when each of its evaluations is, and deduces
that **restriction of diagrams along a functor carries K-flat complexes to K-flat complexes**.

Both directions are pointwise.  Evaluation at an object of `J` is strong monoidal and exact, and
the evaluations jointly detect acyclicity
(`HomologicalComplex.acyclic_iff_forall_evaluation`), so the total tensor product and acyclicity
of a complex of diagrams are both read off the evaluations.  For the direction that needs an
acyclic complex of diagrams out of an acyclic complex of `D`, the constant diagram serves: it is
acyclic because acyclicity is pointwise, and its evaluations are all the complex one started
with.

## Main results

* `CochainComplex.KFlatBifunctor.kFlat_evaluation`: each evaluation of a K-flat complex of
  diagrams is K-flat.
* `CochainComplex.KFlatBifunctor.kFlat_of_forall_evaluation`: a complex of diagrams all of whose
  evaluations are K-flat is K-flat.
* `CochainComplex.KFlatBifunctor.kFlat_iff_forall_evaluation`: the two together.
* `CochainComplex.KFlatBifunctor.kFlat_whiskeringLeftMapHomologicalComplex`: **restriction of
  diagrams along a functor preserves K-flatness**, because the evaluations of a restricted
  diagram are evaluations of the diagram.

## Implementation notes

`CochainComplex.KFlatBifunctor.kFlat_constMapHomologicalComplex` of
`StacksFrontier.Homology.ConstMapHomologicalComplexKFlat` is the same pointwise argument run for
the constant diagram, and this file reuses its two ingredients — the monoidal structure of
evaluation on complexes (`CategoryTheory.Functor.evaluationMapHomologicalComplexMonoidal`) and
`HomologicalComplex.acyclic_iff_forall_evaluation` — rather than redoing them.

The composite `((Functor.whiskeringLeft J' J D).obj f) ⋙ (evaluation J' D).obj k` is
*definitionally* `(evaluation J D).obj (f.obj k)`, and so the evaluation of a restricted complex
of diagrams is the evaluation of the complex at the image object by `rfl`; that is what keeps the
last proof free of any transport.

## References

* [Stacks Project, Tag 06YN](https://stacks.math.columbia.edu/tag/06YN), K-flatness.
-/

@[expose] public noncomputable section

open CategoryTheory Limits MonoidalCategory

universe v₁ u₁ v₂ u₂ v₃ u₃

namespace CochainComplex.KFlatBifunctor

open CategoryTheory.Functor

variable {J : Type u₁} [Category.{v₁} J] {D : Type u₂} [Category.{v₂} D] [Abelian D]
  [MonoidalCategory D] [MonoidalPreadditive D]
  [HasCoproducts.{0} D] [HasColimitsOfSize.{0, 0} D] [HasInitial D]
  [∀ X : D, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : D, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  [∀ X : D, PreservesColimitsOfShape (Discrete PEmpty.{1}) (tensorLeft X)]
  [∀ X : D, PreservesColimitsOfShape (Discrete PEmpty.{1}) (tensorRight X)]

omit [HasColimitsOfSize.{0, 0} D] in
/-- **Each evaluation of a K-flat complex of diagrams is K-flat.**

Given an acyclic complex `G` of objects of `D`, the constant diagram at `G` is an acyclic complex
of diagrams, so tensoring it with `K` gives an acyclic complex of diagrams; evaluating at `k`
turns that into `G` tensored with the evaluation of `K`, by the tensorator of
`CategoryTheory.Functor.evaluationMapHomologicalComplexMonoidal` and the fact that evaluating a
constant diagram returns what it was constant at. -/
theorem kFlat_evaluation (K : CochainComplex (J ⥤ D) ℤ)
    (hK : KFlat (curriedTensor (J ⥤ D)) K) (k : J) :
    KFlat (curriedTensor D)
      ((((evaluation J D).obj k).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) := by
  intro G hG
  have hconst : (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj G).Acyclic := by
    rw [HomologicalComplex.acyclic_iff_forall_evaluation]
    exact fun _ => hG
  have h := hK _ hconst
  rw [show totalComplex (curriedTensor (J ⥤ D))
        (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ)).obj G) K =
      ((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ)).obj G ⊗ K from
      rfl, HomologicalComplex.acyclic_iff_forall_evaluation] at h
  intro n
  exact HomologicalComplex.ExactAt.of_iso (h k n)
    (Functor.Monoidal.μIso (((evaluation J D).obj k).mapHomologicalComplex (ComplexShape.up ℤ))
      (((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ)).obj G) K).symm

omit [HasColimitsOfSize.{0, 0} D] in
/-- **A complex of diagrams all of whose evaluations are K-flat is K-flat.**

Both the total tensor product and acyclicity of a complex of diagrams are read off the
evaluations, so this is the hypothesis applied at each object of `J`. -/
theorem kFlat_of_forall_evaluation (K : CochainComplex (J ⥤ D) ℤ)
    (hK : ∀ k : J, KFlat (curriedTensor D)
      ((((evaluation J D).obj k).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) :
    KFlat (curriedTensor (J ⥤ D)) K := by
  intro G hG
  rw [show totalComplex (curriedTensor (J ⥤ D)) G K = G ⊗ K from rfl,
    HomologicalComplex.acyclic_iff_forall_evaluation]
  intro k n
  exact HomologicalComplex.ExactAt.of_iso
    (hK k ((((evaluation J D).obj k).mapHomologicalComplex (ComplexShape.up ℤ)).obj G)
      ((HomologicalComplex.acyclic_iff_forall_evaluation G).1 hG k) n)
    (Functor.Monoidal.μIso (((evaluation J D).obj k).mapHomologicalComplex (ComplexShape.up ℤ))
      G K)

omit [HasColimitsOfSize.{0, 0} D] in
/-- **K-flatness of a complex of diagrams is a pointwise condition.** -/
theorem kFlat_iff_forall_evaluation (K : CochainComplex (J ⥤ D) ℤ) :
    KFlat (curriedTensor (J ⥤ D)) K ↔
      ∀ k : J, KFlat (curriedTensor D)
        ((((evaluation J D).obj k).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
  ⟨fun hK k => kFlat_evaluation K hK k, kFlat_of_forall_evaluation K⟩

variable {J' : Type u₃} [Category.{v₃} J']

omit [HasColimitsOfSize.{0, 0} D] in
/-- **Restriction of diagrams along a functor preserves K-flatness.**

Restriction along `f : J' ⥤ J` is precomposition with `f`, so the evaluation of a restricted
complex of diagrams at `k` is the evaluation of the complex at `f k`; K-flatness being pointwise
by `CochainComplex.KFlatBifunctor.kFlat_iff_forall_evaluation`, the statement follows. -/
theorem kFlat_whiskeringLeftMapHomologicalComplex (f : J' ⥤ J)
    (K : CochainComplex (J ⥤ D) ℤ) (hK : KFlat (curriedTensor (J ⥤ D)) K) :
    KFlat (curriedTensor (J' ⥤ D))
      ((((Functor.whiskeringLeft J' J D).obj f).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K) :=
  kFlat_of_forall_evaluation _ fun k => kFlat_evaluation K hK (f.obj k)

end CochainComplex.KFlatBifunctor

end
