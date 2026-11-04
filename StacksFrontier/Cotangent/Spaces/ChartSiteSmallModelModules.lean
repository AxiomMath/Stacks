module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import StacksFrontier.Cotangent.Spaces.ChartSiteSmallModel

/-!
# Sheaves of modules on the small model of the chart site

Restriction along the equivalence of the site `C_{X/Λ}` of Tag 08VK with its small model is an
equivalence on sheaves of modules over any sheaf of rings, so nothing is lost by working on the
small model.

## Main results

* `AlgebraicGeometry.Space.PolynomialChart.smallChartModulesEquiv`: for a sheaf of rings `R` on the
  chart site, the categories of `R`-modules and of modules over its restriction to the small
  model are equivalent.

## Implementation notes

Both the equivalence and its inverse are dense subsite inclusions for the inherited topology, so
both are continuous and the two restrictions of sheaves of modules are adjoint equivalences of
each other. The comparison maps of the ring sheaves are the identity in one direction — the ring
sheaf of the small model *is* the restriction — and the counit of the equivalence in the other.

## References

* [Stacks Project, Tag 08VK](https://stacks.math.columbia.edu/tag/08VK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace AlgebraicGeometry.Space.PolynomialChart

variable (Λ : Type u) [CommRing Λ] (B : BigFppfSite.{u})
  (hS : B.Contains (Spec (CommRingCat.of Λ)))
  (X : (BigFppfOver B (Spec (CommRingCat.of Λ)) hS)ᵒᵖ ⥤ Type u)
  (hX : IsAlgebraicSpace B (Spec (CommRingCat.of Λ)) hS X)

/-- The functor from the chart site to its small model is also a dense subsite inclusion for the
inherited topology, hence continuous: the inherited topology is the one the equivalence
transports. -/
instance isDenseSubsite_smallChartEquiv_inverse :
    (smallChartEquiv Λ B hS X hX).inverse.IsDenseSubsite (topology Λ B hS X hX)
      (smallChartTopology Λ B hS X hX) :=
  show (smallChartEquiv Λ B hS X hX).symm.functor.IsDenseSubsite (topology Λ B hS X hX)
    ((smallChartEquiv Λ B hS X hX).symm.inverse.inducedTopology (topology Λ B hS X hX))
    from inferInstance

/-- Restriction of sheaves of rings from the chart site to its small model. -/
abbrev restrictRingCatToSmallChart :
    Sheaf (topology Λ B hS X hX) RingCat.{v} ⥤
      Sheaf (smallChartTopology Λ B hS X hX) RingCat.{v} :=
  (smallChartEquiv Λ B hS X hX).functor.sheafPushforwardContinuous RingCat.{v}
    (smallChartTopology Λ B hS X hX) (topology Λ B hS X hX)

/-- **Sheaves of modules on the chart site and on its small model agree.** For a sheaf of rings
`R` on the site of polynomial charts, restriction along the equivalence with the small model is
an equivalence from the `R`-modules to the modules over the restricted ring sheaf. -/
def smallChartModulesEquiv (R : Sheaf (topology Λ B hS X hX) RingCat.{v}) :
    SheafOfModules.{v} R ≌
      SheafOfModules.{v} ((restrictRingCatToSmallChart Λ B hS X hX).obj R) := by
  refine SheafOfModules.pushforwardPushforwardEquivalence (smallChartEquiv Λ B hS X hX)
    (𝟙 _)
    ⟨Functor.whiskerRight (NatTrans.op (smallChartEquiv Λ B hS X hX).counit) R.obj⟩ ?_ ?_
  · change _ = _ ≫ 𝟙 _
    exact (Category.comp_id _).symm
  · apply NatTrans.ext
    funext U
    change 𝟙 _ ≫
      R.obj.map ((smallChartEquiv Λ B hS X hX).counit.app
          ((smallChartEquiv Λ B hS X hX).functor.obj U.unop)).op ≫
        R.obj.map ((smallChartEquiv Λ B hS X hX).functor.map
          ((smallChartEquiv Λ B hS X hX).unit.app U.unop)).op = 𝟙 _
    rw [Category.id_comp, ← Functor.map_comp, ← op_comp]
    exact (congrArg (fun a : (smallChartEquiv Λ B hS X hX).functor.obj U.unop ⟶
        (smallChartEquiv Λ B hS X hX).functor.obj U.unop => R.obj.map a.op)
      ((smallChartEquiv Λ B hS X hX).functor_unitIso_comp U.unop)).trans (R.obj.map_id _)

end AlgebraicGeometry.Space.PolynomialChart

end
