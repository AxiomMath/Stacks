module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import StacksFrontier.Cotangent.ChartSiteSmallModel
import StacksCore.Tactic.StacksAttribute

/-!
# Sheaves of modules on the small model of the chart site

Restriction along the equivalence of the site `C_{X/Λ}` of Tag 08VA with its small model is an
equivalence on sheaves of modules over any sheaf of rings, so nothing is lost by working on the
small model.

## Main results

* `AlgebraicGeometry.PolynomialChart.smallChartModulesEquiv`: for a sheaf of rings `R` on the
  chart site, the categories of `R`-modules and of modules over its restriction to the small
  model are equivalent.

## Implementation notes

Both the equivalence and its inverse are dense subsite inclusions for the inherited topology, so
both are continuous and the two restrictions of sheaves of modules are adjoint equivalences of
each other. The comparison maps of the ring sheaves are the identity in one direction — the ring
sheaf of the small model *is* the restriction — and the counit of the equivalence in the other.

## References

* [Stacks Project, Tag 08VA](https://stacks.math.columbia.edu/tag/08VA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace AlgebraicGeometry.PolynomialChart

variable (Λ : Type u) [CommRing Λ] (X : Scheme.{u})
    (structureMap : X ⟶ Spec (CommRingCat.of Λ))

/-- The functor from the chart site to its small model is also a dense subsite inclusion for the
inherited topology, hence continuous: the inherited topology is the one the equivalence
transports. -/
instance isDenseSubsite_smallChartEquiv_inverse :
    (smallChartEquiv Λ X structureMap).inverse.IsDenseSubsite (topology Λ X structureMap)
      (smallChartTopology Λ X structureMap) :=
  inferInstanceAs ((smallChartEquiv Λ X structureMap).symm.functor.IsDenseSubsite
    (topology Λ X structureMap)
    ((smallChartEquiv Λ X structureMap).symm.inverse.inducedTopology
      (topology Λ X structureMap)))

/-- Restriction of sheaves of rings from the chart site to its small model. -/
abbrev restrictRingCatToSmallChart :
    Sheaf (topology Λ X structureMap) RingCat.{v} ⥤
      Sheaf (smallChartTopology Λ X structureMap) RingCat.{v} :=
  (smallChartEquiv Λ X structureMap).functor.sheafPushforwardContinuous RingCat.{v}
    (smallChartTopology Λ X structureMap) (topology Λ X structureMap)

/-- **Sheaves of modules on the chart site and on its small model agree.** For a sheaf of rings
`R` on the site of polynomial charts, restriction along the equivalence with the small model is
an equivalence from the `R`-modules to the modules over the restricted ring sheaf. -/
def smallChartModulesEquiv (R : Sheaf (topology Λ X structureMap) RingCat.{v}) :
    SheafOfModules.{v} R ≌
      SheafOfModules.{v} ((restrictRingCatToSmallChart Λ X structureMap).obj R) := by
  refine SheafOfModules.pushforwardPushforwardEquivalence (smallChartEquiv Λ X structureMap)
    (𝟙 _)
    ⟨Functor.whiskerRight (NatTrans.op (smallChartEquiv Λ X structureMap).counit) R.obj⟩ ?_ ?_
  · change _ = _ ≫ 𝟙 _
    exact (Category.comp_id _).symm
  · apply NatTrans.ext
    funext U
    change 𝟙 _ ≫
      R.obj.map ((smallChartEquiv Λ X structureMap).counit.app
          ((smallChartEquiv Λ X structureMap).functor.obj U.unop)).op ≫
        R.obj.map ((smallChartEquiv Λ X structureMap).functor.map
          ((smallChartEquiv Λ X structureMap).unit.app U.unop)).op = 𝟙 _
    rw [Category.id_comp, ← Functor.map_comp, ← op_comp]
    exact (congrArg (fun a : (smallChartEquiv Λ X structureMap).functor.obj U.unop ⟶
        (smallChartEquiv Λ X structureMap).functor.obj U.unop => R.obj.map a.op)
      ((smallChartEquiv Λ X structureMap).functor_unitIso_comp U.unop)).trans (R.obj.map_id _)

end AlgebraicGeometry.PolynomialChart

end
