module

public import StacksFrontier.AlgebraicGeometry.Quot.PrestableCurveFamilies
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleSite

/-!
# The étale charts of the total space of a family of curves, over the base

Let `f : X ⟶ S` be a family of curves (Stacks 0D4Z). An étale chart `U` of the algebraic space
`X` is a scheme `U` with an étale morphism `U ⟶ X`; composing with `f` gives a morphism of schemes
`U ⟶ S`. Every property of `f` defined on étale charts (flatness, local finite presentation,
being at-worst-nodal of relative dimension one) is a property of this morphism of schemes.

## Main definitions

* `AlgebraicGeometry.CurveFamily.chartToBase`: the morphism of the site from the scheme of an
  étale chart of the total space to the base.

## Main results

* `AlgebraicGeometry.CurveFamily.holds_chartToBase`: a property of scheme morphisms which `f`
  has on every étale chart holds for `U ⟶ S`.
* `AlgebraicGeometry.CurveFamily.flat_chartToBase`,
  `AlgebraicGeometry.CurveFamily.locallyOfFinitePresentation_chartToBase`,
  `AlgebraicGeometry.CurveFamily.isAtWorstNodal_chartToBase`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.CurveFamily

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase} (X : CurveFamily B hZ)

/-- The structure morphism of the family on presheaves, with target the representable presheaf of
the base. -/
abbrev toBaseHom : X.total.1 ⟶ yoneda.obj X.base :=
  X.toBase.hom

/-- **The morphism of the site from an étale chart of the total space to the base.** It is the
Yoneda preimage of the composite of the chart with the structure morphism of the family. -/
def chartToBase (U : Space.SmallEtale B integerBase hZ X.total.1) : U.obj.left ⟶ X.base :=
  Yoneda.fullyFaithful.preimage (U.obj.hom ≫ X.toBaseHom)

/-- The image of `chartToBase U` under the Yoneda embedding is the composite of the chart
`U ⟶ X` with the structure morphism of the family. -/
theorem yoneda_map_chartToBase (U : Space.SmallEtale B integerBase hZ X.total.1) :
    yoneda.map (X.chartToBase U) = U.obj.hom ≫ X.toBaseHom :=
  Yoneda.fullyFaithful.map_preimage _

/-- A property of scheme morphisms which the structure morphism of the family has on every
étale chart holds for the morphism `U ⟶ S` of every étale chart `U` of the total space. -/
theorem holds_chartToBase {P : MorphismProperty Scheme.{u}}
    (hP : Space.HoldsOnEveryEtaleChart B integerBase hZ P X.toBase.hom)
    (U : Space.SmallEtale B integerBase hZ X.total.1) :
    P ((BigFppfOver.toScheme B integerBase hZ).map (X.chartToBase U)) :=
  hP _ _ U.obj.hom (𝟙 _) (X.chartToBase U) U.property
    (presheaf_id_of_iso B integerBase hZ _
      (fun _ _ g _ => by
        show Etale ((BigFppfOver.toScheme B integerBase hZ).map g)
        infer_instance) _)
    (by rw [yoneda_map_chartToBase]; exact Category.comp_id (U.obj.hom ≫ X.toBaseHom))

/-- For every étale chart `U` of the total space, the morphism `U ⟶ S` is flat. -/
theorem flat_chartToBase (U : Space.SmallEtale B integerBase hZ X.total.1) :
    Flat ((BigFppfOver.toScheme B integerBase hZ).map (X.chartToBase U)) :=
  X.holds_chartToBase X.flat U

/-- For every étale chart `U` of the total space, the morphism `U ⟶ S` is locally of finite
presentation. -/
theorem locallyOfFinitePresentation_chartToBase
    (U : Space.SmallEtale B integerBase hZ X.total.1) :
    LocallyOfFinitePresentation ((BigFppfOver.toScheme B integerBase hZ).map (X.chartToBase U)) :=
  X.holds_chartToBase X.finitePresentation.1 U

/-- For a prestable family of curves and every étale chart `U` of the total space, the morphism
`U ⟶ S` is at-worst-nodal of relative dimension one. -/
theorem isAtWorstNodal_chartToBase (hX : IsPrestableCurveFamily B hZ X)
    (U : Space.SmallEtale B integerBase hZ X.total.1) :
    IsAtWorstNodalOfRelativeDimensionOne
      ((BigFppfOver.toScheme B integerBase hZ).map (X.chartToBase U)) :=
  X.holds_chartToBase hX.1 U

end AlgebraicGeometry.CurveFamily

end
