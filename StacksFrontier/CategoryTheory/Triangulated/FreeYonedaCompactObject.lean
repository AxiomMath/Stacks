module

public import Mathlib.CategoryTheory.Generator.Presheaf
public import StacksFrontier.CategoryTheory.Triangulated.CompactObjects

/-!
# Compactness of a free diagram on a representable

Let `C` be a category and `D` a preadditive category with enough coproducts. For `X : C` and
`P : D` the free diagram `CategoryTheory.Presheaf.freeYoneda X P` corepresents the evaluation at
`X`: morphisms `freeYoneda X P ⟶ F` are morphisms `P ⟶ F(X)`, by
`CategoryTheory.Presheaf.freeYonedaHomEquiv`. Evaluation at `X` commutes with direct sums, because
colimits of diagrams are computed pointwise; so `freeYoneda X P` is a compact object of `Cᵒᵖ ⥤ D`
as soon as `P` is a compact object of `D`.

This is the second of the two statements about the generating family `freeYoneda X P` that a
dévissage of a comparison on the unbounded derived category `D(Cᵒᵖ ⥤ D)` along compact generators
needs; the first is projectivity, `Stacks.CategoryHomology.freeYonedaProjective`.

## Main definitions

* `CategoryTheory.Presheaf.freeYonedaHomAddEquiv`: the corepresentation bijection
  `CategoryTheory.Presheaf.freeYonedaHomEquiv` as an additive equivalence. Composition is
  bilinear and the addition of diagram morphisms is componentwise, so the bijection — which is
  "compose with the coprojection at the identity, then evaluate at `X`" — is additive.

## Main results

* `CategoryTheory.Presheaf.isCompactObject_freeYoneda`: `freeYoneda X P` is a compact object of
  `Cᵒᵖ ⥤ D` when `P` is a compact object of `D`, at the same index universe.

## Implementation notes

The index universe `w` of the direct sums is a parameter independent of the universes of `C` and
`D`, and is given explicitly in both the hypothesis and the conclusion:
`CategoryTheory.IsCompactObject` carries that universe only inside the binder of its field, so
writing the conclusion without it would auto-bind a third, independent universe and assert
compactness against families the hypothesis says nothing about.

The proof does not go through
`CategoryTheory.isCompactObject_of_preservesColimitsOfShape_preadditiveCoyoneda`:
the corepresented functor of `freeYoneda X P` takes values in abelian groups of the hom universe
of `Cᵒᵖ ⥤ D`, while the corepresented functor of `P` takes values in abelian groups of the hom
universe of `D`, so the two cannot be compared by a natural isomorphism without an intervening
`ULift`. Instead the compactness map of `freeYoneda X P` is compared directly with that of `P`
against the evaluated cofan, through the corepresentation bijection.

## References

* [Stacks project, Tag 07LS](https://stacks.math.columbia.edu/tag/07LS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w uD vD v u

namespace CategoryTheory.Presheaf

variable {C : Type u} [Category.{v} C] {D : Type uD} [Category.{vD} D]
  [Preadditive D] [HasCoproducts.{v} D]

/-- The corepresentation bijection `(freeYoneda X P ⟶ F) ≃ (P ⟶ F(X))` is additive: it is
composition with a fixed coprojection followed by evaluation at `X`, and both operations are
additive. -/
lemma freeYonedaHomEquiv_add {X : C} {P : D} {F : Cᵒᵖ ⥤ D}
    (f g : freeYoneda X P ⟶ F) :
    freeYonedaHomEquiv (f + g) = freeYonedaHomEquiv f + freeYonedaHomEquiv g :=
  Preadditive.comp_add _ _ _ _ _ _

/-- **`CategoryTheory.Presheaf.freeYonedaHomEquiv` as an additive equivalence**,
`(freeYoneda X P ⟶ F) ≃+ (P ⟶ F(X))`. -/
def freeYonedaHomAddEquiv {X : C} {P : D} {F : Cᵒᵖ ⥤ D} :
    (freeYoneda X P ⟶ F) ≃+ (P ⟶ F.obj (op X)) :=
  ⟨freeYonedaHomEquiv, freeYonedaHomEquiv_add⟩

/-- **A free diagram on a representable is a compact object when its coefficient object is.**
Morphisms out of `freeYoneda X P` are morphisms out of `P` into the value at `X`, and the value at
`X` of a direct sum of diagrams is the direct sum of the values; so the compactness map of
`freeYoneda X P` against a family of diagrams is the compactness map of `P` against the family of
values at `X`, read through the corepresentation bijections. -/
theorem isCompactObject_freeYoneda [HasCoproducts.{w} D] (X : C) (P : D)
    (hP : IsCompactObject.{w} P) : IsCompactObject.{w} (freeYoneda X P) := by
  classical
  refine ⟨fun E _ ↦ ?_⟩
  change Function.Bijective (cofanMap (freeYoneda X P) (Limits.Sigma.ι E))
  have hc : IsColimit (Cofan.mk ((∐ E).obj (op X))
      (fun i ↦ (Limits.Sigma.ι E i).app (op X))) :=
    isColimitMapCoconeCofanMkEquiv ((evaluation Cᵒᵖ D).obj (op X)) E (Limits.Sigma.ι E)
      (isColimitOfPreserves _ (coproductIsCoproduct E))
  have hds : Function.Bijective (DirectSum.map fun i ↦
      (freeYonedaHomAddEquiv (X := X) (P := P) (F := E i)).toAddMonoidHom) :=
    bijective_directSumMap _ fun i ↦ (freeYonedaHomAddEquiv (F := E i)).bijective
  have hEq : ((freeYonedaHomAddEquiv (X := X) (P := P) (F := ∐ E)).toAddMonoidHom.comp
        (cofanMap (freeYoneda X P) (Limits.Sigma.ι E))) =
      (cofanMap P fun i ↦ (Limits.Sigma.ι E i).app (op X)).comp
        (DirectSum.map fun i ↦
          (freeYonedaHomAddEquiv (X := X) (P := P) (F := E i)).toAddMonoidHom) := by
    refine DirectSum.addHom_ext fun i y ↦ ?_
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, cofanMap_of, DirectSum.map_of,
      AddEquiv.coe_toAddMonoidHom]
    exact freeYonedaHomEquiv_comp y (Limits.Sigma.ι E i)
  refine ((freeYonedaHomAddEquiv (X := X) (P := P) (F := ∐ E)).bijective.of_comp_iff' _).mp ?_
  rw [← AddEquiv.coe_toAddMonoidHom, ← AddMonoidHom.coe_comp, hEq, AddMonoidHom.coe_comp]
  exact (bijective_cofanMap P hP (fun i ↦ (Limits.Sigma.ι E i).app (op X)) hc).comp hds

end CategoryTheory.Presheaf

end
