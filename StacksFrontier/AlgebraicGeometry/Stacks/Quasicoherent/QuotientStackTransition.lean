module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.CartesianTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.CartesianRelations
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCartesianOnAffineCharts
public import StacksFrontier.AlgebraicGeometry.Stacks.CoherenceConditionsCartesian
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.ComparisonAlgebraicSpacesIso
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuotientStackHomRestriction

/-!
# The transition morphism of the module on `U` attached to a module on `[U/R]` (towards 06WT)

Let `G = (U, R, s, t, c)` be a groupoid in algebraic spaces, `𝒳 = [U/R]` its quotient stack and
`x : 𝒮_U ⟶ [U/R]` the canonical projection.  The forward functor of Stacks 06WT sends a
quasi-coherent `𝒪_𝒳`-module `ℱ` to the pair `(𝒢, α)` with `𝒢 = x^*ℱ|_{U_étale}` and

```
α : t_small^*𝒢 ⟶ (x ∘ s)^*ℱ|_{R_étale} ⟶ s_small^*𝒢,
```

the comparison map of equation 076R of the triangle through the target (carried by the
2-morphism of Stacks 044S) followed by the inverse of the comparison map of the triangle through
the source.  This file proves the two facts that make this a definition: `𝒢` is quasi-coherent,
and both comparison maps are isomorphisms.

## Main results

* `AlgebraicGeometry.Space.isCartesianOnAffineCharts_etaleRestrictedModuleInverseImage`: the
  restriction `f^*ℱ|_{U_étale}` of a quasi-coherent module along any 1-morphism from a category
  represented by an algebraic space is cartesian on affine charts, hence quasi-coherent
  (`AlgebraicGeometry.Space.isQuasicoherentOnSite_etaleRestrictedModuleInverseImage`).
* `AlgebraicGeometry.Stack.isIso_quotientStackSourceComparison` and
  `AlgebraicGeometry.Stack.isIso_quotientStackTargetComparison`: the comparison maps of the two
  triangles of the source's diagram are isomorphisms for a quasi-coherent `ℱ`.

## Main definitions

* `AlgebraicGeometry.Stack.quotientStackTransition`: the transition morphism `α`.

## References

* [Stacks Project, Tag 06WT](https://stacks.math.columbia.edu/tag/06WT)
* [Stacks Project, Tag 076R](https://stacks.math.columbia.edu/tag/076R)
* [Stacks Project, Tag 044S](https://stacks.math.columbia.edu/tag/044S)
-/

@[expose] public section

open CategoryTheory Opposite Stacks.PresheafOfModules

universe u v w

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {U : AlgebraicSpaces B S hS}
  {𝒰 : Type v} [Category.{w} 𝒰] {𝒳 : Type*} [Category 𝒳]
  (p : 𝒰 ⥤ BigFppfOver B S hS) (r : 𝒳 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids) (hr : r.IsFiberedInGroupoids)
  (eU : StacksRepresentableCFG.EquivalenceOver p
    (presheafOfCategories (U.1 ⋙ typeToCat)).p)
  (f : 𝒰 ⥤ 𝒳) (hf : p.IsFibredOneMorphism r f)

/-- The coefficient homomorphism of `f^*ℱ|_{U_étale}` is an isomorphism at every chart. -/
theorem isIso_etaleChartStructureHom_app (Z : (SmallEtale B S hS U.1)ᵒᵖ) :
    IsIso ((etaleChartStructureHom B S hS p r hp hr eU f hf).hom.app Z) := by
  obtain ⟨W⟩ := Z
  rw [etaleChartStructureHom_app]
  exact Functor.map_isIso _ _

/-- **The restriction of a quasi-coherent module to the small étale site of an algebraic-space
chart is cartesian on affine charts**: for a 1-morphism `f : 𝒰 ⥤ 𝒳` from a category represented
by an algebraic space `U` and a quasi-coherent module `ℱ` on the fppf site of `𝒳`, the module
`f^*ℱ|_{U_étale}` has bijective base change comparisons between affine étale charts. -/
theorem isCartesianOnAffineCharts_etaleRestrictedModuleInverseImage
    (ℱ : SheafOfModules.{u} (Stack.ringStructureSheafCore B S hS r hr B.topology le_rfl))
    (hℱ : ℱ.IsQuasicoherentOnSite) :
    IsCartesianOnAffineCharts (etaleRestrictedModuleInverseImage B S hS p r hp hr eU f hf
      (FibredSite.restrictSiteModules B S hS r hr .etale ℱ)) := by
  intro V W hV hW g
  rw [bijective_sectionsBaseChange_iff_isIso_restrictionBaseChange.{u, u} B S hS U.1 U.2,
    ConcreteCategory.isIso_iff_bijective]
  refine (bijective_restrictionBaseChange_restrictScalars_pushforward₀_iff
    (etaleChartToFibred B S hS p eU f) (Stack.fibredRings B S hS r)
    (structurePresheaf B S hS U.1) (etaleChartStructureHom B S hS p r hp hr eU f hf).hom
    (isIso_etaleChartStructureHom_app B S hS p r hp hr eU f hf) ℱ.val g.op).2 ?_
  have hc := etaleChartToFibred_comp B S hS p r eU f hf
  have hAff : ∀ X, IsAffine ((SmallEtale.toOver B S hS U.1 ⋙ BigFppfOver.toScheme B S hS).obj X) →
      IsAffine ((r ⋙ BigFppfOver.toScheme B S hS).obj
        ((etaleChartToFibred B S hS p eU f).obj X)) := fun X hX => by
    have : IsAffine (((etaleChartToFibred B S hS p eU f ⋙ r) ⋙
        BigFppfOver.toScheme B S hS).obj X) := by rwa [hc]
    exact this
  exact Stack.bijective_restrictionBaseChange_fibredRings_of_isQuasicoherentOnSite B S hS r hr ℱ hℱ
    ((etaleChartToFibred B S hS p eU f).map g) (hAff V hV) (hAff W hW)

/-- **The restriction of a quasi-coherent module to the small étale site of an algebraic-space
chart is quasi-coherent.** -/
theorem isQuasicoherentOnSite_etaleRestrictedModuleInverseImage
    (ℱ : SheafOfModules.{u} (Stack.ringStructureSheafCore B S hS r hr B.topology le_rfl))
    (hℱ : ℱ.IsQuasicoherentOnSite) :
    (etaleRestrictedModuleInverseImage B S hS p r hp hr eU f hf
      (FibredSite.restrictSiteModules B S hS r hr .etale ℱ)).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_of_isCartesianOnAffineCharts _
    (isCartesianOnAffineCharts_etaleRestrictedModuleInverseImage B S hS p r hp hr eU f hf ℱ hℱ)

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Stack

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS} (G : GroupoidInAlgebraicSpaces C S hS B)

/-- **`x^*ℱ|_{U_étale}` is quasi-coherent** for a quasi-coherent module `ℱ` on `[U/R]`. -/
theorem isQuasicoherentOnSite_quotientStackObjectRestriction (F : QuotientStackModules G)
    (hF : F.IsQuasicoherentOnSite) :
    (quotientStackObjectRestriction G F).IsQuasicoherentOnSite :=
  Space.isQuasicoherentOnSite_etaleRestrictedModuleInverseImage C S hS _ _ _ _ _ _ _ F hF

/-- **The comparison map of the triangle through the source is an isomorphism** for a
quasi-coherent module on `[U/R]`. -/
theorem isIso_quotientStackSourceComparison (F : QuotientStackModules G)
    (hF : F.IsQuasicoherentOnSite) : IsIso (quotientStackSourceComparison G F) :=
  Space.isIso_comparisonAlgebraicSpacesModules C S hS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (fun _ _ k hx hy => bijective_restrictionBaseChange_fibredRings_of_isQuasicoherentOnSite C S hS
      (quotientStack G).p (isFiberedInGroupoids_quotientStack G) F hF k hx hy)
    (isQuasicoherentOnSite_quotientStackObjectRestriction G F hF)

/-- **The comparison map of the triangle through the target is an isomorphism** for a
quasi-coherent module on `[U/R]`. -/
theorem isIso_quotientStackTargetComparison (F : QuotientStackModules G)
    (hF : F.IsQuasicoherentOnSite) : IsIso (quotientStackTargetComparison G F) :=
  Space.isIso_comparisonAlgebraicSpacesModules C S hS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (fun _ _ k hx hy => bijective_restrictionBaseChange_fibredRings_of_isQuasicoherentOnSite C S hS
      (quotientStack G).p (isFiberedInGroupoids_quotientStack G) F hF k hx hy)
    (isQuasicoherentOnSite_quotientStackObjectRestriction G F hF)

/-- **The transition morphism of Stacks 06WT.**  For a quasi-coherent module `ℱ` on `[U/R]`, the
morphism `α : t_small^*(x^*ℱ|_{U_étale}) ⟶ s_small^*(x^*ℱ|_{U_étale})`: the comparison map of
equation 076R of the triangle through the target, carried by the 2-morphism of Stacks 044S,
followed by the inverse of the comparison map of the triangle through the source. -/
noncomputable def quotientStackTransition (F : QuotientStackModules G)
    (hF : F.IsQuasicoherentOnSite) :=
  haveI := isIso_quotientStackSourceComparison G F hF
  quotientStackTargetComparison G F ≫ inv (quotientStackSourceComparison G F)

/-- The transition morphism followed by the comparison through the source is the comparison
through the target. -/
@[reassoc]
theorem quotientStackTransition_comp_sourceComparison (F : QuotientStackModules G)
    (hF : F.IsQuasicoherentOnSite) :
    quotientStackTransition G F hF ≫ quotientStackSourceComparison G F =
      quotientStackTargetComparison G F := by
  have := isIso_quotientStackSourceComparison G F hF
  simp [quotientStackTransition]

/-- **The transition morphism is natural in the module**: the restriction `x^*ψ|_{U_étale}` of a
morphism of quasi-coherent modules on `[U/R]` commutes with the two transition morphisms. -/
theorem quotientStackTransition_naturality {F H : QuotientStackModules G}
    (hF : F.IsQuasicoherentOnSite) (hH : H.IsQuasicoherentOnSite) (ψ : F ⟶ H) :
    quotientStackTransition G F hF ≫
        (Space.modulePullback C S hS G.source).map (quotientStackObjectRestrictionMap G ψ) =
      (Space.modulePullback C S hS G.target).map (quotientStackObjectRestrictionMap G ψ) ≫
        quotientStackTransition G H hH := by
  have := isIso_quotientStackSourceComparison G H hH
  refine (Iso.cancel_iso_hom_right _ _ (asIso (quotientStackSourceComparison G H))).1 ?_
  calc (quotientStackTransition G F hF ≫
        (Space.modulePullback C S hS G.source).map (quotientStackObjectRestrictionMap G ψ)) ≫
        quotientStackSourceComparison G H
      = quotientStackTransition G F hF ≫ quotientStackSourceComparison G F ≫
          quotientStackArrowRestrictionMap (G := G) ψ := by
        rw [Category.assoc, quotientStackSource_square_restrictionMap (G := G) ψ]
    _ = quotientStackTargetComparison G F ≫ quotientStackArrowRestrictionMap (G := G) ψ := by
        rw [← Category.assoc, quotientStackTransition_comp_sourceComparison G F hF]
    _ = _ := by
        rw [quotientStackTarget_square_restrictionMap (G := G) ψ, asIso_hom, Category.assoc,
          quotientStackTransition_comp_sourceComparison G H hH]

end AlgebraicGeometry.Stack

end
