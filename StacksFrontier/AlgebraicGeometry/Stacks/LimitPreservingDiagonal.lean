module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingMorphism
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CatCategoricalPullback

/-!
# Full faithfulness of the colimit comparison of a 1-morphism (Stacks 0CMW)

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of categories fibred in groupoids over the big fppf category of a
scheme `S`. Stacks 0CMW asserts that the diagonal `Δ : 𝒳 ⟶ 𝒳 ×_𝒴 𝒳` is limit preserving exactly
when, for every cofiltered inverse system of affine schemes over `S` with limit `U = lim Uᵢ`, the
canonical functor `colim 𝒳_{Uᵢ} ⟶ 𝒳_U ×_{𝒴_U} colim 𝒴_{Uᵢ}` is fully faithful. This file states
that second condition and proves that it holds for a limit preserving `f`.

## Main definitions

* `AlgebraicGeometry.Stack.IsFullyFaithfulOnAffineLimits`: **Stacks 0CMW**, condition (2).

## Main results

* `AlgebraicGeometry.Stack.isFullyFaithfulOnAffineLimits_of_isLimitPreserving`: condition (2) of
  Stacks 0CMW holds for a limit preserving 1-morphism.

## Implementation notes

The target `𝒳_U ×_{𝒴_U} colim 𝒴_{Uᵢ}` is the explicit 2-fibre product of categories, Mathlib's
`CategoryTheory.Limits.CategoricalPullback`, and the functor into it is the comparison
`CategoryTheory.Cat.toCategoricalPullbackFunctor` of the determinate square of Stacks 0CMR. The
condition is therefore stated with the same pinned data `T`, `H`, `η` as
`AlgebraicGeometry.Stack.IsLimitPreserving`: without them neither the functor out of the colimit
nor the 2-cell filling the square is determined by `f`, and the condition would quantify over an
arbitrary functor rather than the canonical one.

With that formulation the implication proved here is the content of the source's final clause in
the direction that does not need the colimit lemma: the square of Stacks 0CMR being 2-cartesian
makes the comparison an equivalence, hence fully faithful. The converse direction, and with it the
equivalence of the two conditions of Stacks 0CMW and the limit preservation of the diagonal, rest
on the statement — omitted in the source — that filtered colimits of categories commute with
2-fibre products.

## References

* [Stacks Project, Tag 0CMW](https://stacks.math.columbia.edu/tag/0CMW)
* [Stacks Project, Tag 0CMR](https://stacks.math.columbia.edu/tag/0CMR)
* [Stacks Project, Tag 07XL](https://stacks.math.columbia.edu/tag/07XL)
* [Stacks Project, Tag 04Z7](https://stacks.math.columbia.edu/tag/04Z7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u v w uX vX

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 𝒴 : CatFiberedInGroupoids.{u, vX, u + 1, uX} (BigFppfOver B S hS)}

/-- **Stacks 0CMW, condition (2).** For every cofiltered inverse system of affine schemes over `S`
whose image in schemes has a limiting cone `U = lim Uᵢ`, the canonical functor
`colim 𝒳_{Uᵢ} ⟶ 𝒳_U ×_{𝒴_U} colim 𝒴_{Uᵢ}` is fully faithful.

The square of Stacks 0CMR of which this functor is the comparison into the explicit 2-fibre
product is the determinate one: the vertical map out of the colimit is the colimit of the
componentwise maps `AlgebraicGeometry.Stack.splitFiberMap` of strict split fibres, and the filling
2-cell is, on every colimit generator, the canonical base-change comparison of the fibred
1-morphism underlying `f`. -/
abbrev IsFullyFaithfulOnAffineLimits (f : 𝒳 ⟶ 𝒴) : Prop :=
  letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
  letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
  ∀ (I : Type v) [Category.{w} I] [IsCofiltered I]
    (D : I ⥤ BigAffineFppf B S hS) (c : Cone D),
    IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c) →
      let E := D ⋙ BigAffineFppf.inclusion B S hS
      let d := (BigAffineFppf.inclusion B S hS).mapCone c
      ∃ (T : Deformation.Artin.fiberDiagram 𝒳.val.p E ⟶
          Deformation.Artin.fiberDiagram 𝒴.val.p E)
        (H : (colimit (Deformation.Artin.fiberDiagram 𝒳.val.p E) : Cat) ⥤
          (colimit (Deformation.Artin.fiberDiagram 𝒴.val.p E) : Cat))
        (η : (Deformation.Artin.colimitComparison 𝒳.val.p E d ⋙
            AsSmall.up.{vX, uX, max v w vX (u + 1) uX u}) ⋙
            AsSmall.down.{vX, uX, max v w vX (u + 1) uX u} ⋙
            Functor.fiberFunctorOfCompEq
              (CatFiberedInGroupoids.homFunctor_comp_p f) d.pt ⋙
              AsSmall.up.{vX, uX, max v w vX (u + 1) uX u} ≅
          H ⋙ Deformation.Artin.colimitComparison 𝒴.val.p E d ⋙
            AsSmall.up.{vX, uX, max v w vX (u + 1) uX u}),
        (∀ i : I, T.app (op i) =
          (AsSmall.down ⋙ splitFiberMap B S hS f (E.obj i) ⋙
            AsSmall.up).toCatHom) ∧
          (H = (colimMap T).toFunctor) ∧
          (∀ (i : I) (x : 𝒳.val.p.SplitFiber (E.obj i)),
            HEq
              (AsSmall.down.map
                ((η.app
                  ((colimit.ι (Deformation.Artin.fiberDiagram 𝒳.val.p E)
                      (op i)).toFunctor.obj
                    (AsSmall.up.{vX, max (u + 1) uX, max v w}.obj x))).hom))
              ((isFibredOneMorphism B S hS f).mapPullbackFiberIso x.obj
                (d.π.app i ≫ x.hom)).inv) ∧
          (Cat.toCategoricalPullbackFunctor
            ({ pt := (colimit (Deformation.Artin.fiberDiagram 𝒳.val.p E) : Cat)
               fst := (Deformation.Artin.colimitComparison 𝒳.val.p E d ⋙
                 AsSmall.up.{vX, uX, max v w vX (u + 1) uX u}).toCatHom
               snd := H.toCatHom
               iso := Cat.Hom.isoMk η } :
              Bicategory.TwoCommSq
                (AsSmall.down.{vX, uX, max v w vX (u + 1) uX u} ⋙
                  Functor.fiberFunctorOfCompEq
                  (CatFiberedInGroupoids.homFunctor_comp_p f) d.pt ⋙
                  AsSmall.up.{vX, uX, max v w vX (u + 1) uX u}).toCatHom
                (Deformation.Artin.colimitComparison 𝒴.val.p E d ⋙
                  AsSmall.up.{vX, uX, max v w vX (u + 1) uX u}).toCatHom)).Full ∧
          (Cat.toCategoricalPullbackFunctor
            ({ pt := (colimit (Deformation.Artin.fiberDiagram 𝒳.val.p E) : Cat)
               fst := (Deformation.Artin.colimitComparison 𝒳.val.p E d ⋙
                 AsSmall.up.{vX, uX, max v w vX (u + 1) uX u}).toCatHom
               snd := H.toCatHom
               iso := Cat.Hom.isoMk η } :
              Bicategory.TwoCommSq
                (AsSmall.down.{vX, uX, max v w vX (u + 1) uX u} ⋙
                  Functor.fiberFunctorOfCompEq
                  (CatFiberedInGroupoids.homFunctor_comp_p f) d.pt ⋙
                  AsSmall.up.{vX, uX, max v w vX (u + 1) uX u}).toCatHom
                (Deformation.Artin.colimitComparison 𝒴.val.p E d ⋙
                  AsSmall.up.{vX, uX, max v w vX (u + 1) uX u}).toCatHom)).Faithful

/-- **Stacks 0CMW, condition (2) for a limit preserving 1-morphism.** If the square of
Stacks 0CMR is 2-cartesian then its comparison functor into the explicit 2-fibre product is an
equivalence, so the canonical functor `colim 𝒳_{Uᵢ} ⟶ 𝒳_U ×_{𝒴_U} colim 𝒴_{Uᵢ}` is fully
faithful. -/
@[stacks 0CMW "condition (2) holds for a limit preserving 1-morphism"]
theorem isFullyFaithfulOnAffineLimits_of_isLimitPreserving (f : 𝒳 ⟶ 𝒴)
    (hf : IsLimitPreserving.{u, v, w, uX, vX} B S hS f) :
    IsFullyFaithfulOnAffineLimits.{u, v, w, uX, vX} B S hS f := by
  intro I _ _ D c hc
  obtain ⟨T, H, η, hT, hH, hη, hsq⟩ := hf I D c hc
  obtain ⟨hsq⟩ := hsq
  have := Cat.isEquivalence_toCategoricalPullbackFunctor hsq
  exact ⟨T, H, η, hT, hH, hη, inferInstance, inferInstance⟩

end AlgebraicGeometry.Stack

end
