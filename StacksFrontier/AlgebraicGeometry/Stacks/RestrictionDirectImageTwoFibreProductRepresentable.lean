module

public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentabilitySmallerBase
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.SliceBaseChangePoint
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverFirstFactor

/-!
# The 2-fibre product of equation 075M is represented by an algebraic space over `S`

Let `𝒳` and `𝒴` be categories fibred in groupoids over the big fppf site of `S`, presented by
algebraic spaces `F` and `G` through equivalences `eF` and `eG`, and let `f : 𝒳 ⥤ 𝒴` be a
1-morphism of fibred categories. For an object `U` of the base site and a 1-morphism
`G₀ : (Sch/S)_{fppf}/U ⥤ 𝒴` over the base, the 2-fibre product of `G₀` and `f` over `𝒴` is
equivalent, over `AlgebraicGeometry.BigFppfOver B S hS`, to the category of elements of an
algebraic space `T` over `S`. In the proof of Stacks 073N, where `U` is an étale scheme chart `V`
of `G`, the representing algebraic space is `V ×_G F`.

## Main definitions

* `AlgebraicGeometry.Space.elementsSlicePoint`: the point `σ` of the category of elements of `G`
  with values in the scheme of `U`, read through `eG` and the iterated-slice equivalence.
* `AlgebraicGeometry.Space.elementsLegFunctor`: the 1-morphism `θ` of categories of elements that
  `f` becomes through `eF` and `eG`.

## Main results

* `AlgebraicGeometry.Space.exists_isAlgebraicSpace_nonempty_equivalenceOver_overForget`: a 2-fibre
  product whose first factor is a slice of the base is represented by an algebraic space over `S`.

## Implementation notes

The statement is made for an arbitrary slice of the base as first factor and an arbitrary
1-morphism out of it over the base as first leg.

Representability of a base change is available over the big fppf site of the scheme of `U`, as
`CategoryTheory.PresheafOfCategories.nonempty_equivalenceOver_twoFibreProductPresheaf`. The
2-fibre product is carried into that shape by three changes of presentation:

* the target `𝒴` is replaced by the category of elements of `G` along `eG`, by
  `CategoryTheory.TwoFibreProductOver.mapBase`, an equivalence because the forward 1-morphism of
  an equivalence over the site is full and faithful;
* the second factor `𝒳` is replaced by the category of elements of `F` along `eF`, by
  `CategoryTheory.TwoFibreProductOver.precomposeSnd`;
* the first factor, the slice of the big fppf site of `S` at `U`, is replaced by the big fppf site
  of the scheme of `U`, by `CategoryTheory.TwoFibreProductOver.precomposeFst` along
  `CategoryTheory.Over.iteratedSliceBackward`. The first leg is `CategoryTheory.Over.forget` of
  `U`, while representability is stated over `CategoryTheory.Over.map` of the structure morphism
  of `U`; the two are conjugate by the iterated-slice equivalence, and
  `CategoryTheory.Over.iteratedSliceBackward_forget` says the conjugation is an equality of
  functors.

The representing presheaf is then moved from the smaller base to `S` by the lower-shriek extension
of Stacks 03I5 (2): `StacksRepresentableCFG.EquivalenceOver.compRight` along
`CategoryTheory.Over.map` of `U`, followed by
`CategoryTheory.PresheafOfCategories.relocalizeElementsEquivalenceOver`. By
`CategoryTheory.PresheafOfCategories.exists_isPullback_relocalize_of_point`, this lower-shriek
extension is the fibre product of `F` and the presheaf of points of `U` over `G`, so it is an
algebraic space by Stacks 04T9, `AlgebraicGeometry.isAlgebraicSpace_of_isPullback`.

## References

* [Stacks Project, Tag 075M](https://stacks.math.columbia.edu/tag/075M)
* [Stacks Project, Tag 073N](https://stacks.math.columbia.edu/tag/073N)
* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
* [Stacks Project, Tag 02ZW](https://stacks.math.columbia.edu/tag/02ZW)
* [Stacks Project, Tag 04T9](https://stacks.math.columbia.edu/tag/04T9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.PresheafOfCategories

namespace AlgebraicGeometry.Space

universe u v w v' w'

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  {𝒳 : Type v} [Category.{w} 𝒳] {𝒴 : Type v'} [Category.{w'} 𝒴]
  (p : 𝒳 ⥤ BigFppfOver B S hS) (q : 𝒴 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
  (eF : StacksRepresentableCFG.EquivalenceOver p
    (presheafOfCategories (F ⋙ typeToCat)).p)
  (eG : StacksRepresentableCFG.EquivalenceOver q
    (presheafOfCategories (G ⋙ typeToCat)).p)
  (f : 𝒳 ⥤ 𝒴)

/-- **A point of the category of elements of `G` with values in the scheme of an object of the
base.** A 1-morphism `G₀ : (Sch/S)_{fppf}/U ⥤ 𝒴` over the base site, read through the presentation
`eG` of `𝒴` and through the iterated-slice equivalence identifying the slice
`(Sch/S)_{fppf}/U` with the big fppf site of the scheme of `U`, becomes a point of the category of
elements of `G` with values in that scheme. -/
noncomputable def elementsSlicePoint (U : BigFppfOver B S hS) (G₀ : Over U ⥤ 𝒴) :
    Over U.left ⥤ (presheafOfCategories (G ⋙ typeToCat)).obj :=
  Over.iteratedSliceBackward U ⋙ (G₀ ⋙ eG.hom.functor)

/-- `AlgebraicGeometry.Space.elementsSlicePoint` is a point *over* the big fppf site of the scheme
of `U`: composing it with the projection of the category of elements gives
`CategoryTheory.Over.map` of the structure morphism of `U`. -/
theorem elementsSlicePoint_comp (U : BigFppfOver B S hS) (G₀ : Over U ⥤ 𝒴)
    (hG₀ : G₀ ⋙ q = Over.forget U) :
    elementsSlicePoint B S hS G q eG U G₀ ⋙ discreteProjection G = Over.map U.hom := by
  change Over.iteratedSliceBackward U ⋙ G₀ ⋙ eG.hom.functor ⋙ discreteProjection G = _
  rw [eG.hom.w, hG₀, Over.iteratedSliceBackward_forget]

/-- **The 1-morphism of categories of elements that `f` becomes.** Through the presentation `eF`
of `𝒳` and the presentation `eG` of `𝒴`, the 1-morphism `f : 𝒳 ⥤ 𝒴` of equation 075M becomes a
1-morphism from the category of elements of `F` to that of `G`. -/
noncomputable def elementsLegFunctor :
    (presheafOfCategories (F ⋙ typeToCat)).obj ⥤
      (presheafOfCategories (G ⋙ typeToCat)).obj :=
  eF.inv.functor ⋙ (f ⋙ eG.hom.functor)

/-- `AlgebraicGeometry.Space.elementsLegFunctor` is a 1-morphism *over* the big fppf site of `S`:
composing it with the projection of the category of elements of `G` gives the projection of the
category of elements of `F`. -/
theorem elementsLegFunctor_comp (hf : p.IsFibredOneMorphism q f) :
    elementsLegFunctor B S hS F G p q eF eG f ⋙ discreteProjection G = discreteProjection F := by
  change eF.inv.functor ⋙ f ⋙ eG.hom.functor ⋙ discreteProjection G = _
  rw [eG.hom.w, hf.comp_eq, eF.inv.w]

include hp hq eF eG in
/-- **A 2-fibre product whose first factor is a slice of the base is represented by an algebraic
space over `S`.** Let `𝒳` and `𝒴` be categories fibred in groupoids over the big fppf site of `S`,
presented by algebraic spaces `F` and `G`, let `f : 𝒳 ⥤ 𝒴` be a 1-morphism of fibred categories,
let `U` be an object of the base site and let `G₀ : (Sch/S)_{fppf}/U ⥤ 𝒴` be a 1-morphism over the
base. Then the 2-fibre product of `G₀` and `f` over `𝒴`, viewed over the big fppf site of `S`
through its structure functor, is equivalent there to the category of elements of an algebraic
space over `S`. -/
theorem exists_isAlgebraicSpace_nonempty_equivalenceOver_overForget
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (hf : p.IsFibredOneMorphism q f) (U : BigFppfOver B S hS) (G₀ : Over U ⥤ 𝒴)
    (hG₀ : G₀ ⋙ q = Over.forget U) :
    ∃ T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u, IsAlgebraicSpace B S hS T ∧
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.structureFunctor (Over.forget U) p q G₀ f)
        (discreteProjection T)) := by
  have hbq : eG.hom.functor ⋙ discreteProjection G = q := eG.hom.w
  have haFp : eF.inv.functor ⋙ p = discreteProjection F := eF.inv.w
  have hθ : elementsLegFunctor B S hS F G p q eF eG f ⋙ discreteProjection G =
      discreteProjection F := elementsLegFunctor_comp B S hS F G p q eF eG f hf
  have hσ : elementsSlicePoint B S hS G q eG U G₀ ⋙ discreteProjection G = Over.map U.hom :=
    elementsSlicePoint_comp B S hS G q eG U G₀ hG₀
  have hfgF : (discreteProjection F).IsFiberedInGroupoids :=
    (isFiberedInSetoids_discreteProjection F).isFiberedInGroupoids
  have hfgG : (discreteProjection G).IsFiberedInGroupoids :=
    (isFiberedInSetoids_discreteProjection G).isFiberedInGroupoids
  have hfgforget : (Over.forget U).IsFiberedInGroupoids :=
    Functor.IsFiberedInGroupoids.over_forget U
  have hfgmap : (Over.map U.hom).IsFiberedInGroupoids :=
    Functor.IsFiberedInGroupoids.over_map U.hom
  have hfbq : (f ⋙ eG.hom.functor) ⋙ discreteProjection G = p := by
    rw [Functor.assoc, hbq, hf.comp_eq]
  have hG₀bq : (G₀ ⋙ eG.hom.functor) ⋙ discreteProjection G = Over.forget U := by
    rw [Functor.assoc, hbq, hG₀]
  have hθ' : eF.inv.functor ⋙ (f ⋙ eG.hom.functor) ⋙ discreteProjection G =
      discreteProjection F := by rw [hfbq, haFp]
  have hSF0 :
      (TwoFibreProductOver.structureFunctor (Over.forget U) p q G₀ f).IsFiberedInGroupoids :=
    TwoFibreProductOver.isFiberedInGroupoids _ _ _ _ _ hfgforget hp hq hG₀ hf.comp_eq
  have hSF1 : (TwoFibreProductOver.structureFunctor (Over.forget U) p (discreteProjection G)
      (G₀ ⋙ eG.hom.functor) (f ⋙ eG.hom.functor)).IsFiberedInGroupoids :=
    TwoFibreProductOver.isFiberedInGroupoids _ _ _ _ _ hfgforget hp hfgG hG₀bq hfbq
  have hSF2 : (TwoFibreProductOver.structureFunctor (Over.forget U) (discreteProjection F)
      (discreteProjection G) (G₀ ⋙ eG.hom.functor)
      (eF.inv.functor ⋙ (f ⋙ eG.hom.functor))).IsFiberedInGroupoids :=
    TwoFibreProductOver.isFiberedInGroupoids _ _ _ _ _ hfgforget hfgF hfgG hG₀bq hθ'
  have hSF3 : (TwoFibreProductOver.structureFunctor (Over.map U.hom) (discreteProjection F)
      (discreteProjection G) (Over.iteratedSliceBackward U ⋙ (G₀ ⋙ eG.hom.functor))
      (eF.inv.functor ⋙ (f ⋙ eG.hom.functor))).IsFiberedInGroupoids :=
    TwoFibreProductOver.isFiberedInGroupoids _ _ _ _ _ hfgmap hfgF hfgG hσ hθ'
  have : eG.hom.functor.Full := eG.isEquivalence_hom_functor.full
  have : eG.hom.functor.Faithful := eG.isEquivalence_hom_functor.faithful
  obtain ⟨e₁⟩ := StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence hSF0 hSF1
    (TwoFibreProductOver.mapBase G₀ f eG.hom.functor hbq) rfl
    (TwoFibreProductOver.isEquivalence_mapBase hbq)
  have : eF.inv.functor.IsEquivalence := eF.isEquivalence_inv_functor
  obtain ⟨e₂⟩ := StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence hSF2 hSF1
    (TwoFibreProductOver.precomposeSnd (G₀ ⋙ eG.hom.functor) (f ⋙ eG.hom.functor)
      eF.inv.functor haFp) rfl
    (TwoFibreProductOver.isEquivalence_precomposeSnd hfgforget hfgF hp haFp hfbq)
  obtain ⟨e₃⟩ := StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence hSF3 hSF2
    (TwoFibreProductOver.precomposeFst (Over.map U.hom) (Over.forget U) (discreteProjection F)
      (discreteProjection G) (G₀ ⋙ eG.hom.functor) (eF.inv.functor ⋙ (f ⋙ eG.hom.functor))
      (Over.iteratedSliceBackward U) (Over.iteratedSliceBackward_forget U))
    (TwoFibreProductOver.precomposeFst_comp_structureFunctor _ _ _ _ _ _ _ _)
    (TwoFibreProductOver.isEquivalence_precomposeFst _ _ _ _ _ _ _
      (Over.iteratedSliceBackward_forget U) hfgF hfgmap hfgforget
      ((Over.iteratedSliceEquiv U).symm.isEquivalence_functor) hG₀bq)
  obtain ⟨e₄⟩ := nonempty_equivalenceOver_twoFibreProductPresheaf U.hom
    (θ := elementsLegFunctor B S hS F G p q eF eG f) (hθ := hθ)
    (σ := elementsSlicePoint B S hS G q eG U G₀) (hσ := hσ)
  refine ⟨(OverShriek.relocalizePresheafFunctor U.hom).obj
    (twoFibreProductPresheaf (elementsSlicePoint B S hS G q eG U G₀) hσ
      (elementsLegFunctor B S hS F G p q eF eG f) hθ), ?_, ?_⟩
  · obtain ⟨β, cc, hpb⟩ := exists_isPullback_relocalize_of_point U.hom
      (elementsSlicePoint B S hS G q eG U G₀) hσ
      (elementsLegFunctor B S hS F G p q eF eG f) hθ
    exact isAlgebraicSpace_of_isPullback hF
      (isAlgebraicSpace_yoneda B S hS (Over.mk U.hom)) hG.isSheaf hG.diagonal_representable hpb
  · exact ⟨e₁.trans (e₂.symm.trans (e₃.symm.trans
      (((e₄.compRight (Over.map U.hom)).trans
        (relocalizeElementsEquivalenceOver U.hom _)).ofEq
              TwoFibreProductOver.fst_comp_eq)))⟩

end AlgebraicGeometry.Space

end
