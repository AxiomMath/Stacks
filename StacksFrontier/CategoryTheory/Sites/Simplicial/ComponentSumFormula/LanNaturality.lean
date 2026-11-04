module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.AbelianSumFormula.Sigma.LanSumFormula
public import StacksFrontier.Topology.Sheaves.Functors.Module.PullbackPresheaf

/-!
# The evaluation of a left Kan extension, as a colimit over a comma category, is natural

For a functor `L : C ⥤ D` of small categories and a presheaf `P` on `C`, the evaluation of the
left Kan extension of `P` along `L.op` at an object `V` of `D` is the colimit of `P` over the
opposite of the comma category of `L` over `V`; that identification is
`Stacks.Sites.AbelianSumFormula.lanObjObjIsoColimit`. This file proves that it is natural in `V`:
the structure map of the Kan extension for a morphism `i : V' ⟶ V` corresponds to the canonical
comparison map of colimits along the functor `CategoryTheory.StructuredArrow.map i` which
precomposes a structured arrow with `i`.

## Main results

* `Stacks.Sites.ComponentSumFormula.colimit_pre_structuredArrowOpEquivalence`: the comparison of
  colimits over the structured arrows of `L` and over the costructured arrows of `L.op` commutes
  with precomposition by a morphism of `D`.
* `Stacks.Sites.ComponentSumFormula.lanObjObjIsoColimit_naturality`: the identification of the
  evaluation of a left Kan extension with a colimit over a comma category is natural in the
  object.

## Implementation notes

Three reductions hold by `rfl` and carry the proof. First, the square of comma categories relating
`CategoryTheory.StructuredArrow.map` to `CategoryTheory.CostructuredArrow.map` through
`CategoryTheory.structuredArrowOpEquivalence` commutes definitionally, because neither functor
touches the component that the equivalence rewrites. Second,
`CategoryTheory.lanEvaluationIsoColim` applied at a presheaf is
`CategoryTheory.Functor.leftKanExtensionObjIsoColimit`, which is the form the naturality
statement `Stacks.PresheafOfModules.Pullback.leftKanExtensionObjIsoColimit_naturality` is about.
Third, with `CategoryTheory.Functor.lan` made reducible, the Kan extension functor's action on a
morphism is that of `CategoryTheory.Functor.leftKanExtension`.

`CategoryTheory.Functor.Final.colimitIso` is by definition the canonical comparison map, so the
first statement is `CategoryTheory.Limits.colimit.pre_pre` applied to the two halves of the
definitional square. It has to be applied as a *term*: the diagram of the first comparison map is
stated through `CategoryTheory.StructuredArrow.proj` and the lemma's is stated through the
equivalence, and the two are definitionally but not syntactically equal, so `rw` finds no
occurrence of the pattern. For the same reason both proofs end on an `Eq.trans` term rather than
on a rewrite.

## References

* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 09WG](https://stacks.math.columbia.edu/tag/09WG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sites.AbelianSumFormula

universe v u

namespace Stacks.Sites.ComponentSumFormula

variable {A : Type v} [Category.{u} A] [HasColimitsOfSize.{u, u} A]
  {C D : Type u} [SmallCategory C] [SmallCategory D]

attribute [local implicit_reducible] CategoryTheory.Functor.lan

/-- Reading a colimit over the opposite of the comma category of `L` over `V` as a colimit over
the costructured arrows of `L.op` over `op V` is compatible with precomposition by a morphism
`i : V' ⟶ V` of the base. -/
theorem colimit_pre_structuredArrowOpEquivalence (L : C ⥤ D) (P : Cᵒᵖ ⥤ A)
    {V V' : D} (i : V' ⟶ V) :
    colimit.pre ((StructuredArrow.proj V' L).op ⋙ P) (StructuredArrow.map i).op ≫
        (Functor.Final.colimitIso (structuredArrowOpEquivalence L V').functor
          (CostructuredArrow.proj L.op (op V') ⋙ P)).hom =
      (Functor.Final.colimitIso (structuredArrowOpEquivalence L V).functor
          (CostructuredArrow.proj L.op (op V) ⋙ P)).hom ≫
        colimit.pre (CostructuredArrow.proj L.op (op V') ⋙ P) (CostructuredArrow.map i.op) := by
  rw [Functor.Final.colimitIso_hom, Functor.Final.colimitIso_hom]
  exact (colimit.pre_pre (F := CostructuredArrow.proj L.op (op V') ⋙ P)
      (E := (structuredArrowOpEquivalence L V').functor) (StructuredArrow.map (T := L) i).op).trans
    (colimit.pre_pre (F := CostructuredArrow.proj L.op (op V') ⋙ P)
      (E := CostructuredArrow.map (S := L.op) i.op) (structuredArrowOpEquivalence L V).functor).symm

/-- **The comma-category description of a left Kan extension's values is natural in the object.**
For a morphism `i : V' ⟶ V` of the base, the structure map of the left Kan extension of `P` along
`L.op` is, through `Stacks.Sites.AbelianSumFormula.lanObjObjIsoColimit`, the canonical comparison
map of colimits along the functor precomposing a structured arrow with `i`. -/
theorem lanObjObjIsoColimit_naturality (L : C ⥤ D) (P : Cᵒᵖ ⥤ A) {V V' : D} (i : V' ⟶ V) :
    (L.op.lan.obj P).map i.op ≫ (lanObjObjIsoColimit L P V').hom =
      (lanObjObjIsoColimit L P V).hom ≫
        colimit.pre ((StructuredArrow.proj V' L).op ⋙ P) (StructuredArrow.map i).op := by
  have hA := Stacks.PresheafOfModules.Pullback.leftKanExtensionObjIsoColimit_naturality L.op P i.op
  have hB := colimit_pre_structuredArrowOpEquivalence L P i
  have hB' := (Iso.inv_comp_eq _).mpr
    (((Iso.eq_comp_inv _).mpr hB).trans (Category.assoc _ _ _))
  show (L.op.leftKanExtension P).map i.op ≫
      (L.op.leftKanExtensionObjIsoColimit P (op V')).hom ≫
        (Functor.Final.colimitIso (structuredArrowOpEquivalence L V').functor
          (CostructuredArrow.proj L.op (op V') ⋙ P)).inv =
    ((L.op.leftKanExtensionObjIsoColimit P (op V)).hom ≫
        (Functor.Final.colimitIso (structuredArrowOpEquivalence L V).functor
          (CostructuredArrow.proj L.op (op V) ⋙ P)).inv) ≫
      colimit.pre ((StructuredArrow.proj V' L).op ⋙ P) (StructuredArrow.map i).op
  rw [← Category.assoc, hA, Category.assoc]
  exact (congrArg (fun z => (L.op.leftKanExtensionObjIsoColimit P (op V)).hom ≫ z)
    hB'.symm).trans (Category.assoc _ _ _).symm

end Stacks.Sites.ComponentSumFormula

end
