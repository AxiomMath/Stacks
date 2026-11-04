module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartOpenRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts

/-!
# Morphisms of étale charts are étale

The morphism of schemes `AlgebraicGeometry.Space.chartSchemeMap g` underlying a morphism `g` of
étale charts of a presheaf `F` on the big fppf site is étale (Stacks 03EC read on the small étale
category of `F`).

## Main results

* `AlgebraicGeometry.Space.etale_chartSchemeMap`: the morphism of schemes underlying any morphism
  of étale charts is étale.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **The morphism of schemes underlying *any* morphism of étale charts is étale.**

This is `AlgebraicGeometry.Space.etale_of_etale_charts` read on the category
`AlgebraicGeometry.Space.SmallEtale`: both charts are étale by their defining property and the
triangle over `F` is `AlgebraicGeometry.Space.yoneda_map_toOver_map_comp_hom`.  The ambient
presheaf `F` need not be an algebraic space. -/
theorem etale_chartSchemeMap {U V : SmallEtale B S hS F} (g : V ⟶ U) :
    AlgebraicGeometry.Etale (chartSchemeMap g) :=
  etale_of_etale_charts B S hS V.obj.hom U.obj.hom V.property U.property
    ((SmallEtale.toOver B S hS F).map g) (yoneda_map_toOver_map_comp_hom g)

end AlgebraicGeometry.Space
