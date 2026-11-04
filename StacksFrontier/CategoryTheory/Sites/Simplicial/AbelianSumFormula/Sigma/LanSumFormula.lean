module

public import Mathlib.CategoryTheory.Functor.Flat
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AbelianSumFormula.Sigma.CommaEquivalence

/-!
# The sum formula for the lower shriek of a component inclusion, objectwise

Let `Cs` be a simplicial site — case (A) of the simplicial-site situation of Stacks 09WE. Stacks
09WG(6) says that the restriction to the degree-`m` component of the abelian lower shriek of a
sheaf on the degree-`n` component is the direct sum, over the simplex maps `ψ : [n] → [m]`, of its
inverse images along the transition functors. At the level of presheaves and of a single object
`(m, W)` of the total site that is the statement below: the left Kan extension along the
component inclusion, evaluated at `(m, W)`, is the coproduct over `ψ : n ⟶ m` of the left Kan
extensions along the transition functors, evaluated at `W`.

The isomorphism is the composite of three identifications, all canonical: the evaluation of a
left Kan extension is the colimit over the opposite of a comma category
(`Stacks.Sites.AbelianSumFormula.lanObjObjIsoColimit`, which is Mathlib's
`CategoryTheory.lanEvaluationIsoColim` transported along `structuredArrowOpEquivalence`); that
comma category is the disjoint union of the comma categories of the transition functors
(`Stacks.Sites.AbelianSumFormula.sigmaDesc_summandInclusion_op_isEquivalence`); and a colimit over
a disjoint union is the coproduct of the colimits
(`Stacks.Sites.AbelianSumFormula.commaColimitSumIso`).

## Main results

* `Stacks.Sites.AbelianSumFormula.lanObjObjIsoColimit`: for any functor `L` of small categories,
  the evaluation at `V` of the left Kan extension along `L.op` is the colimit over
  `(StructuredArrow V L)ᵒᵖ`.
* `Stacks.Sites.AbelianSumFormula.lanObjObjSumIso`: **the sum formula of Stacks 09WG(6),
  objectwise and at the level of presheaves.**

## Implementation notes

What is proved here is the isomorphism at each object, not an isomorphism of presheaves on the
degree-`m` component; the natural form, in the object and in the presheaf, is
`Stacks.Sites.ComponentSumFormula.isIso_sigmaDesc_lanSumInclusion`.

Three reductions used below hold by `rfl`, which is what keeps the chain short:
`(structuredArrowOpEquivalence L V).functor ⋙ CostructuredArrow.proj L.op (op V)` is
`(StructuredArrow.proj V L).op`; `summandInclusion ψ ⋙ StructuredArrow.proj (m, W) ι` is
`StructuredArrow.proj W u_ψ`; and `(lanEvaluationIsoColim A L X).app P` is
`L.leftKanExtensionObjIsoColimit P X`, so the isomorphism below is simultaneously the natural one
in `P` and the one whose colimit injections Mathlib's
`CategoryTheory.Functor.ι_leftKanExtensionObjIsoColimit_hom` computes.

## References

* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 09WG](https://stacks.math.columbia.edu/tag/09WG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pseudofunctor Opposite

universe v u

namespace Stacks.Sites.AbelianSumFormula

variable {A : Type v} [Category.{u} A] [HasColimitsOfSize.{u, u} A]

/-- The evaluation at `V` of the left Kan extension of a presheaf along `L.op` is the colimit of
the presheaf over the opposite of the comma category of `L` over `V`. This is Mathlib's
`CategoryTheory.lanEvaluationIsoColim`, which is stated over the costructured arrows of `L.op`,
read over the structured arrows of `L` instead. -/
noncomputable def lanObjObjIsoColimit {C D : Type u} [SmallCategory C] [SmallCategory D]
    (L : C ⥤ D) (P : Cᵒᵖ ⥤ A) (V : D) :
    (L.op.lan.obj P).obj (op V) ≅ colimit ((StructuredArrow.proj V L).op ⋙ P) :=
  (lanEvaluationIsoColim A L.op (op V)).app P ≪≫
    (Functor.Final.colimitIso (structuredArrowOpEquivalence L V).functor
      (CostructuredArrow.proj L.op (op V) ⋙ P)).symm

variable {Cs : SimplicialSite.{u}} {m n : SimplexCategory} {W : Cs.underlying.obj m}

/-- **The sum formula of Stacks 09WG(6), objectwise and before sheafification.** In case (A) of
Stacks 09WE, the left Kan extension of a presheaf `P` on the degree-`n` component along the
component inclusion, evaluated at the object `(m, W)` of the total category, is the coproduct over
the simplex maps `ψ : n ⟶ m` of the left Kan extensions of `P` along the transition functors,
evaluated at `W`. -/
noncomputable def lanObjObjSumIso [HasColimitsOfShape (Discrete (n ⟶ m)) A]
    (P : (Cs.underlying.obj n)ᵒᵖ ⥤ A) :
    (∐ fun ψ : n ⟶ m => (((Cs.underlying.map ψ).toFunctor).op.lan.obj P).obj (op W)) ≅
      ((CoGrothendieck.ι Cs.totalPseudofunctor (op n)).op.lan.obj P).obj
        (op (⟨op m, W⟩ : CoGrothendieck Cs.totalPseudofunctor)) :=
  Limits.Sigma.mapIso (fun ψ : n ⟶ m => lanObjObjIsoColimit (Cs.underlying.map ψ).toFunctor P W) ≪≫
    commaColimitSumIso ((StructuredArrow.proj (⟨op m, W⟩ : CoGrothendieck Cs.totalPseudofunctor)
        (CoGrothendieck.ι Cs.totalPseudofunctor (op n))).op ⋙ P) ≪≫
      (lanObjObjIsoColimit (CoGrothendieck.ι Cs.totalPseudofunctor (op n)) P
        (⟨op m, W⟩ : CoGrothendieck Cs.totalPseudofunctor)).symm

end Stacks.Sites.AbelianSumFormula

end
