module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartModuleGlueingEquivalence

/-!
# Glueing isomorphisms of modules from the étale charts

Let `X` be an algebraic space and `ℳ`, `𝒩` two `𝒪_X`-modules.  A family of isomorphisms
`α_U : ℳ|_U ≅ 𝒩|_U` over the étale scheme charts `U` of `X`, compatible with the transition
isomorphisms of the two restriction families, is the family of restrictions of a unique
isomorphism `ℳ ≅ 𝒩`: this is the full faithfulness of the glueing equivalence of Stacks 03LY.

## Main definitions

* `AlgebraicGeometry.Space.chartGlueIso`: the glued isomorphism.

## Main results

* `AlgebraicGeometry.Space.chartModuleRestriction_map_chartGlueIso_hom`: it restricts to `α_U`.
* `AlgebraicGeometry.Space.hom_ext_of_chartModuleRestriction`: a morphism of `𝒪_X`-modules is
  determined by its restrictions to the charts.

## References

* [Stacks Project, Tag 03LY](https://stacks.math.columbia.edu/tag/03LY)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : AlgebraicSpaces B S hS} {M N : Modules.{u, u} B S hS X.1 X.2}

/-- **A morphism of `𝒪_X`-modules is determined by its restrictions to the étale charts.** -/
theorem hom_ext_of_chartModuleRestriction {a b : M ⟶ N}
    (h : ∀ U : SmallEtale B S hS X.1,
      (chartModuleRestriction B S hS X U).map a = (chartModuleRestriction B S hS X U).map b) :
    a = b :=
  (chartModuleGlueingFunctor B S hS X).map_injective
    (ChartModuleGlueingData.hom_ext B S hS X fun U => h U)

/-- The morphism of chartwise glueing data given by a compatible family of chart morphisms. -/
def chartGlueingHom
    (α : ∀ U : SmallEtale B S hS X.1,
      (chartModuleRestriction B S hS X U).obj M ⟶ (chartModuleRestriction B S hS X U).obj N)
    (hα : ∀ {V U : SmallEtale B S hS X.1} (f : V ⟶ U),
      (chartModuleInverseImage B S hS X f).map (α U) ≫
          (chartModuleRestrictionTransitions B S hS X N f).hom =
        (chartModuleRestrictionTransitions B S hS X M f).hom ≫ α V) :
    (chartModuleGlueingFunctor B S hS X).obj M ⟶ (chartModuleGlueingFunctor B S hS X).obj N :=
  ChartModuleGlueingData.Hom.mk α hα

/-- **The morphism of `𝒪_X`-modules glued from a compatible family of chart morphisms.** -/
def chartGlueHom
    (α : ∀ U : SmallEtale B S hS X.1,
      (chartModuleRestriction B S hS X U).obj M ⟶ (chartModuleRestriction B S hS X U).obj N)
    (hα : ∀ {V U : SmallEtale B S hS X.1} (f : V ⟶ U),
      (chartModuleInverseImage B S hS X f).map (α U) ≫
          (chartModuleRestrictionTransitions B S hS X N f).hom =
        (chartModuleRestrictionTransitions B S hS X M f).hom ≫ α V) : M ⟶ N :=
  (chartModuleGlueingFunctor B S hS X).preimage (chartGlueingHom α hα)

/-- The glued morphism restricts to the given chart morphisms. -/
theorem chartModuleRestriction_map_chartGlueHom
    (α : ∀ U : SmallEtale B S hS X.1,
      (chartModuleRestriction B S hS X U).obj M ⟶ (chartModuleRestriction B S hS X U).obj N)
    (hα : ∀ {V U : SmallEtale B S hS X.1} (f : V ⟶ U),
      (chartModuleInverseImage B S hS X f).map (α U) ≫
          (chartModuleRestrictionTransitions B S hS X N f).hom =
        (chartModuleRestrictionTransitions B S hS X M f).hom ≫ α V)
    (U : SmallEtale B S hS X.1) :
    (chartModuleRestriction B S hS X U).map (chartGlueHom α hα) = α U :=
  congrArg (fun k => ChartModuleGlueingData.Hom.app k U)
    ((chartModuleGlueingFunctor B S hS X).map_preimage (chartGlueingHom α hα))

/-- **The isomorphism of `𝒪_X`-modules glued from a compatible family of chart isomorphisms**
(Stacks 03LY). -/
def chartGlueIso
    (α : ∀ U : SmallEtale B S hS X.1,
      (chartModuleRestriction B S hS X U).obj M ≅ (chartModuleRestriction B S hS X U).obj N)
    (hα : ∀ {V U : SmallEtale B S hS X.1} (f : V ⟶ U),
      (chartModuleInverseImage B S hS X f).map (α U).hom ≫
          (chartModuleRestrictionTransitions B S hS X N f).hom =
        (chartModuleRestrictionTransitions B S hS X M f).hom ≫ (α V).hom) : M ≅ N :=
  haveI : IsIso (chartGlueingHom (fun U => (α U).hom) hα) :=
    ChartModuleGlueingData.isIso_of_isIso_app B S hS X _ fun U => by
      change IsIso (α U).hom; infer_instance
  haveI : IsIso ((chartModuleGlueingFunctor B S hS X).map
      (chartGlueHom (fun U => (α U).hom) hα)) := by
    rw [chartGlueHom, Functor.map_preimage]; infer_instance
  haveI : IsIso (chartGlueHom (fun U => (α U).hom) hα) :=
    isIso_of_fully_faithful (chartModuleGlueingFunctor B S hS X) _
  asIso (chartGlueHom (fun U => (α U).hom) hα)

/-- The glued isomorphism restricts to the given chart isomorphisms. -/
theorem chartModuleRestriction_map_chartGlueIso_hom
    (α : ∀ U : SmallEtale B S hS X.1,
      (chartModuleRestriction B S hS X U).obj M ≅ (chartModuleRestriction B S hS X U).obj N)
    (hα : ∀ {V U : SmallEtale B S hS X.1} (f : V ⟶ U),
      (chartModuleInverseImage B S hS X f).map (α U).hom ≫
          (chartModuleRestrictionTransitions B S hS X N f).hom =
        (chartModuleRestrictionTransitions B S hS X M f).hom ≫ (α V).hom)
    (U : SmallEtale B S hS X.1) :
    (chartModuleRestriction B S hS X U).map (chartGlueIso α hα).hom = (α U).hom :=
  chartModuleRestriction_map_chartGlueHom (fun U => (α U).hom) hα U

end AlgebraicGeometry.Space

end
