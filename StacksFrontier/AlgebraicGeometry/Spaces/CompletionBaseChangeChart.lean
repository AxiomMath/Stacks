module

public import StacksFrontier.AlgebraicGeometry.Spaces.CompletionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.RelativeProperties

/-!
# Étale charts of the base change to the completion of a local base ring

Let `A` be a local ring with maximal ideal `𝔪`, let `A^` be its `𝔪`-adic completion and let
`X` be an algebraic space over `Spec A` with base change `Y = X ×_{Spec A} Spec A^`. This file
transports an étale chart of `X` to an étale chart of `Y`: for an object `U` of the big fppf
site over `Spec A` the fibre product `U ×_{Spec A} Spec A^` taken in the site represents the
fibre product `U ×_X Y` of presheaves, its structure morphism to `Y` is étale as soon as the
chart `U ⟶ X` is, and the underlying scheme of that fibre product is the fibre product of the
underlying schemes over `Spec A`.

## Main definitions

* `AlgebraicGeometry.Space.completionChart`: the object `U ×_{Spec A} Spec A^` of the big fppf
  site over `Spec A`.
* `AlgebraicGeometry.Space.completionChartMap`: its structure morphism to
  `X ×_{Spec A} Spec A^`.

## Main results

* `AlgebraicGeometry.Space.isPullback_completionChart`: the represented presheaf of
  `U ×_{Spec A} Spec A^` is the fibre product of `U` and `X ×_{Spec A} Spec A^` over `X`.
* `AlgebraicGeometry.Space.isEtale_completionChartMap`: the base change of an étale chart of
  `X` is an étale chart of `X ×_{Spec A} Spec A^`.
* `AlgebraicGeometry.Space.isPullback_toScheme_completionChart`: the underlying scheme of
  `U ×_{Spec A} Spec A^` is the fibre product of the underlying scheme of `U` and `Spec A^`
  over `Spec A`.

## Implementation notes

The terminal object of the big fppf site over `Spec A` is `Over.mk (𝟙 (B.obj hA))`, and the
structure morphism of an object `U` of that site is the unique morphism
`U ⟶ Over.mk (𝟙 (B.obj hA))`. Consequently a chart `yoneda.obj U ⟶ X` of an algebraic space
over `Spec A`, followed by its structure morphism, is the represented structure morphism of
`U`; this is what identifies the fibre product formed in the site with the fibre product of
presheaves.

## References

* [Stacks Project, Tag 0BHP](https://stacks.math.columbia.edu/tag/0BHP)
* [Stacks Project, Tag 0BHQ](https://stacks.math.columbia.edu/tag/0BHQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

noncomputable section

variable (A : Type u) [CommRing A] [IsLocalRing A]
variable (B : BigFppfSite.{u}) (hA : B.Contains (Spec (.of A)))
variable (hAc : B.Contains (Spec (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A))))

/-! ### The chart obtained by base change -/

/-- The base change `U ×_{Spec A} Spec A^` of an object `U` of the big fppf site over `Spec A`
to the `𝔪`-adic completion of `A`, formed in the site. -/
def completionChart (U : BigFppfOver B (Spec (.of A)) hA) : BigFppfOver B (Spec (.of A)) hA :=
  pullback (Over.homMk U.hom : U ⟶ Over.mk (𝟙 (B.obj hA)))
    (yoneda.preimage (completionBaseMap A B hA hAc))

variable {X : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u}
variable (f : X ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hA))))

omit [IsLocalRing A] in
/-- A chart of an algebraic space over `Spec A`, followed by the structure morphism of that
space, is the represented structure morphism of the chart. -/
theorem comp_eq_yoneda_structureHom {U : BigFppfOver B (Spec (.of A)) hA}
    (a : yoneda.obj U ⟶ X) :
    a ≫ f = yoneda.map (Over.homMk U.hom : U ⟶ Over.mk (𝟙 (B.obj hA))) := by
  rw [← yoneda.map_preimage (a ≫ f), Over.mkIdTerminal.hom_ext (yoneda.preimage (a ≫ f))
    (Over.homMk U.hom : U ⟶ Over.mk (𝟙 (B.obj hA)))]

/-- The fibre-product square defining `AlgebraicGeometry.Space.completionChart` still commutes
over `Spec A` after its first projection is composed with a chart `a : U ⟶ X`. -/
theorem completionChart_condition {U : BigFppfOver B (Spec (.of A)) hA}
    (a : yoneda.obj U ⟶ X) :
    (yoneda.map (pullback.fst (Over.homMk U.hom : U ⟶ Over.mk (𝟙 (B.obj hA)))
        (yoneda.preimage (completionBaseMap A B hA hAc))) ≫ a) ≫ f =
      yoneda.map (pullback.snd (Over.homMk U.hom : U ⟶ Over.mk (𝟙 (B.obj hA)))
        (yoneda.preimage (completionBaseMap A B hA hAc))) ≫ completionBaseMap A B hA hAc := by
  rw [Category.assoc, comp_eq_yoneda_structureHom A B hA f a, ← Functor.map_comp,
    pullback.condition, Functor.map_comp, Functor.map_preimage]

/-- The structure morphism `U ×_{Spec A} Spec A^ ⟶ X ×_{Spec A} Spec A^` induced by a chart
`a : U ⟶ X` of an algebraic space over `Spec A`. -/
def completionChartMap {U : BigFppfOver B (Spec (.of A)) hA} (a : yoneda.obj U ⟶ X) :
    yoneda.obj (completionChart A B hA hAc U) ⟶ completionSpace A B hA hAc f :=
  pullback.lift
    (yoneda.map (pullback.fst (Over.homMk U.hom : U ⟶ Over.mk (𝟙 (B.obj hA)))
      (yoneda.preimage (completionBaseMap A B hA hAc))) ≫ a)
    (yoneda.map (pullback.snd (Over.homMk U.hom : U ⟶ Over.mk (𝟙 (B.obj hA)))
      (yoneda.preimage (completionBaseMap A B hA hAc))))
    (completionChart_condition A B hA hAc f a)

/-- The first projection of `AlgebraicGeometry.Space.completionChart`, followed by a chart
`a : U ⟶ X`, is `AlgebraicGeometry.Space.completionChartMap` followed by the projection to
`X`. -/
private theorem yoneda_map_fst_comp {U : BigFppfOver B (Spec (.of A)) hA}
    (a : yoneda.obj U ⟶ X) :
    yoneda.map (pullback.fst (Over.homMk U.hom : U ⟶ Over.mk (𝟙 (B.obj hA)))
        (yoneda.preimage (completionBaseMap A B hA hAc))) ≫ a =
      completionChartMap A B hA hAc f a ≫ completionProjection A B hA hAc f :=
  (pullback.lift_fst _ _ _).symm

/-- The second projection of `AlgebraicGeometry.Space.completionChart` is
`AlgebraicGeometry.Space.completionChartMap` followed by the projection to `Spec A^`. -/
private theorem yoneda_map_snd_eq {U : BigFppfOver B (Spec (.of A)) hA}
    (a : yoneda.obj U ⟶ X) :
    yoneda.map (pullback.snd (Over.homMk U.hom : U ⟶ Over.mk (𝟙 (B.obj hA)))
        (yoneda.preimage (completionBaseMap A B hA hAc))) =
      completionChartMap A B hA hAc f a ≫ pullback.snd f (completionBaseMap A B hA hAc) :=
  (pullback.lift_snd _ _ _).symm

/-! ### The chart is the fibre product -/

/-- The represented presheaf of `U ×_{Spec A} Spec A^` is the fibre product of a chart
`a : U ⟶ X` and the projection `X ×_{Spec A} Spec A^ ⟶ X`. -/
theorem isPullback_completionChart {U : BigFppfOver B (Spec (.of A)) hA}
    (a : yoneda.obj U ⟶ X) :
    IsPullback (yoneda.map (pullback.fst (Over.homMk U.hom : U ⟶ Over.mk (𝟙 (B.obj hA)))
        (yoneda.preimage (completionBaseMap A B hA hAc))))
      (completionChartMap A B hA hAc f a) a (completionProjection A B hA hAc f) := by
  have hmap := (IsPullback.of_hasPullback
    (Over.homMk U.hom : U ⟶ Over.mk (𝟙 (B.obj hA)))
    (yoneda.preimage (completionBaseMap A B hA hAc))).map yoneda
  rw [Functor.map_preimage, ← comp_eq_yoneda_structureHom A B hA f a,
    yoneda_map_snd_eq A B hA hAc f a] at hmap
  exact hmap.of_bot (yoneda_map_fst_comp A B hA hAc f a)
    (IsPullback.of_hasPullback f (completionBaseMap A B hA hAc))

/-- The base change to `Spec A^` of an étale chart of an algebraic space over `Spec A` is an
étale chart of the base change `X ×_{Spec A} Spec A^`. -/
theorem isEtale_completionChartMap {U : BigFppfOver B (Spec (.of A)) hA}
    (a : yoneda.obj U ⟶ X) (ha : IsEtale B (Spec (.of A)) hA a) :
    IsEtale B (Spec (.of A)) hA (completionChartMap A B hA hAc f a) :=
  isEtale_of_isPullback_yoneda B (Spec (.of A)) hA
    (isPullback_completionChart A B hA hAc f a) ha

/-! ### The chart at the level of schemes -/

/-- The Yoneda preimage of `AlgebraicGeometry.Space.completionBaseMap` is the structure
morphism of `AlgebraicGeometry.Space.completionBase`. -/
private theorem preimage_completionBaseMap :
    yoneda.preimage (completionBaseMap A B hA hAc) =
      Over.homMk (completionBase A B hA hAc).hom (by simp) :=
  yoneda.map_injective (by rw [Functor.map_preimage]; rfl)

/-- The morphism of schemes underlying the Yoneda preimage of
`AlgebraicGeometry.Space.completionBaseMap` is the morphism `Spec A^ ⟶ Spec A` induced by
`A → A^`. -/
private theorem toScheme_map_preimage_completionBaseMap :
    (BigFppfOver.toScheme B (Spec (.of A)) hA).map
        (yoneda.preimage (completionBaseMap A B hA hAc)) =
      Spec.map (CommRingCat.ofHom
        (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A))) := by
  rw [preimage_completionBaseMap A B hA hAc]
  show B.inclusion.map (B.inclusion.preimage (X := B.obj hAc) (Y := B.obj hA)
    (Spec.map (CommRingCat.ofHom
      (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A))))) = _
  rw [Functor.map_preimage]

/-- The underlying scheme of `U ×_{Spec A} Spec A^` is the fibre product of the underlying
scheme of `U` and `Spec A^` over `Spec A`. -/
theorem isPullback_toScheme_completionChart (U : BigFppfOver B (Spec (.of A)) hA) :
    IsPullback
      ((BigFppfOver.toScheme B (Spec (.of A)) hA).map
        (pullback.fst (Over.homMk U.hom : U ⟶ Over.mk (𝟙 (B.obj hA)))
          (yoneda.preimage (completionBaseMap A B hA hAc))))
      ((BigFppfOver.toScheme B (Spec (.of A)) hA).map
        (pullback.snd (Over.homMk U.hom : U ⟶ Over.mk (𝟙 (B.obj hA)))
          (yoneda.preimage (completionBaseMap A B hA hAc))))
      ((BigFppfOver.toScheme B (Spec (.of A)) hA).map
        (Over.homMk U.hom : U ⟶ Over.mk (𝟙 (B.obj hA))))
      (Spec.map (CommRingCat.ofHom
        (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)))) := by
  have _ := preservesLimitsOfShape_walkingCospan_toScheme B (Spec (.of A)) hA
  rw [← toScheme_map_preimage_completionBaseMap A B hA hAc]
  exact (IsPullback.of_hasPullback (Over.homMk U.hom : U ⟶ Over.mk (𝟙 (B.obj hA)))
    (yoneda.preimage (completionBaseMap A B hA hAc))).map
      (BigFppfOver.toScheme B (Spec (.of A)) hA)

end

end AlgebraicGeometry.Space

end
