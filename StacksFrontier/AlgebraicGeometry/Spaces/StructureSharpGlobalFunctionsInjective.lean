module

public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleChartGlobalFunctions
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSharpGlobalFunctions

/-!
# Pullback of global functions along a morphism with invertible structure map is injective

Let `c : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` of a big fppf site `B` whose
structure map `c♯ : 𝒪_Y ⟶ c_*𝒪_X` of Stacks 03G8 is an isomorphism. Then pullback of global
regular functions `Γ(Y, 𝒪_Y) ⟶ Γ(X, 𝒪_X)` is injective.

A global function `s` of `Y` is a compatible family of regular functions `s_V` on the étale charts
`V` of `Y`. On such a chart the structure map sends `s_V` to the family of its pullbacks to the
étale charts of `X` above `X ×_Y V` (`AlgebraicGeometry.Space.chartProjection_structureMapApp`),
and each of these pullbacks is the value of `c^*s` on that chart of `X`
(`AlgebraicGeometry.Space.globalFunctionsMap_val_chart`). So `c^*s` determines `c♯(s_V)` for every
`V`, hence `s_V` itself because `c♯` is injective on sections
(`AlgebraicGeometry.Space.bijective_structureMapApp`).

## Main results

* `AlgebraicGeometry.Space.injective_globalFunctionsMap_of_isIso_structureSharp`: the
  injectivity.
* `AlgebraicGeometry.Space.bijective_globalFunctionsMap_of_comp_of_isIso_structureSharp`: if
  moreover pullback of global functions along `c ≫ g` is bijective, then so is pullback along `g`.

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The morphism of schemes from an étale chart of `X` above `X ×_Y V` to the étale chart `V` of
`Y` lies over `c`. -/
theorem yoneda_map_chartBaseChangeMap_comp {X Y : AlgebraicSpaces B S hS} (c : X ⟶ Y)
    (V : SmallEtale B S hS Y.1)
    (j : StructuredArrow (op (chartBaseChange B S hS c V)) (comparisonFunctor B S hS X).op) :
    yoneda.map (chartBaseChangeMap B S hS c V j) ≫
        ((SmallEtale.inclusion B S hS Y.obj).obj V).hom =
      ((SmallEtale.inclusion B S hS X.obj).obj j.right.unop).hom ≫ c.hom := by
  refine (congrArg (· ≫ ((SmallEtale.inclusion B S hS Y.obj).obj V).hom)
    (yoneda_map_chartBaseChangeMap B S hS c V j)).trans ?_
  let cV := (comparisonFunctor B S hS Y).obj V
  have hw := ((spacesBaseChange B S hS c).isPullback cV).w
  have hj := Over.w j.hom.unop.hom
  change ((j.hom.unop.hom.left ≫ (spacesBaseChange B S hS c).projection.app cV) ≫
    cV.1.hom).hom = _
  rw [Category.assoc, hw, ← Category.assoc, hj]
  rfl

/-- **Pullback of global functions along a morphism with invertible structure map is
injective.** If the structure map `c♯ : 𝒪_Y ⟶ c_*𝒪_X` of `c : X ⟶ Y` is an isomorphism, then
`Γ(Y, 𝒪_Y) ⟶ Γ(X, 𝒪_X)` is injective. -/
theorem injective_globalFunctionsMap_of_isIso_structureSharp {X Y : AlgebraicSpaces B S hS}
    (c : X ⟶ Y) (hc : IsIso (structureSharp B S hS c)) :
    Function.Injective (globalFunctionsMap B S hS c) := by
  intro s s' h
  refine Subtype.ext (funext fun V => ?_)
  refine (bijective_structureMapApp B S hS c V.unop hc).1 ?_
  refine chartProjection_ext B S hS c V.unop fun j => ?_
  have key := fun t => (chartProjection_structureMapApp B S hS c V.unop j (t.val V)).trans
    (globalFunctionsMap_val_chart B S hS c V.unop j.right.unop
      (chartBaseChangeMap B S hS c V.unop j)
      (yoneda_map_chartBaseChangeMap_comp B S hS c V.unop j) t).symm
  exact (key s).trans ((congrArg (fun t => t.val (op j.right.unop)) h).trans (key s').symm)

/-- **Two out of three for bijectivity on global functions.** If the structure map of
`c : X ⟶ Y` is an isomorphism and pullback of global functions along `c ≫ g` is bijective, then
pullback of global functions along `g : Y ⟶ Z` is bijective. -/
theorem bijective_globalFunctionsMap_of_comp_of_isIso_structureSharp
    {X Y Z : AlgebraicSpaces B S hS} (c : X ⟶ Y) (g : Y ⟶ Z)
    (hc : IsIso (structureSharp B S hS c))
    (hcg : Function.Bijective (globalFunctionsMap B S hS (c ≫ g))) :
    Function.Bijective (globalFunctionsMap B S hS g) := by
  have hinj := injective_globalFunctionsMap_of_isIso_structureSharp B S hS c hc
  rw [globalFunctionsMap_comp, RingHom.coe_comp] at hcg
  refine ⟨hcg.1.of_comp, fun y => ?_⟩
  obtain ⟨z, hz⟩ := hcg.2 (globalFunctionsMap B S hS c y)
  exact ⟨z, hinj hz⟩

end AlgebraicGeometry.Space

end
