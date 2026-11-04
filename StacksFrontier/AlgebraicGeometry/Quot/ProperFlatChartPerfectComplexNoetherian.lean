module

public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatChartStructureComplex
public import StacksFrontier.Deformation.Artin.Obstruction.DerivedCohomologyLinear

/-!
# The perfect complex of Situation 07YX at a chart over a Noetherian ring

For `x` a flat, proper, finitely presented algebraic space `f : X → Spec A` over a Noetherian
ring `A`, there are a perfect complex `K` of `A`-modules and natural isomorphisms
`H^i(K ⊗ᴸ_A −) ≅ Ext^i(L_{X/A}, 𝒪_X ⊗_A −)` for `i = 1, 2`, carrying the boundary map of `K` to
the connecting map of the cotangent `Ext` functors.

## Main results

* `exists_isPerfect_iso_cotangentExt_boundaryMap_of_isNoetherianRing`
  (in `AlgebraicGeometry.Space.ProperFlatLift`): a perfect complex `K` with
  `H^i(K ⊗ᴸ_A −) ≅ Ext^i(L_{X/A}, 𝒪_X ⊗_A −)` for `i = 1, 2`, compatibly with boundary maps.

## References

* [Stacks Project, Tag 08JR](https://stacks.math.columbia.edu/tag/08JR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe t u

namespace AlgebraicGeometry.Space.ProperFlatLift

open Deformation.Artin

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
-- `Deformation.Artin.derivedCohomology` and `Deformation.Artin.boundaryMap` are stated in the
-- model `HasDerivedCategory.standard`.
attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {A : Type u} [CommRing A] {toS : Spec (.of A) ⟶ S} {hA : B.Contains (Spec (.of A))}
  (x : CartesianProperFlatSpaces B S hS)
  (hx : (cartesianProperFlatProjection B S hS).obj x = algebraOver A B S hS toS hA)
  [HasDerivedCategory.{t} (modelModules x.obj.obj.left)]

/-- **The perfect complex of Situation 07YX at a chart.** For `x` a flat, proper,
finitely presented `f : X → Spec A` with `A` Noetherian, there are a perfect complex `K` of
`A`-modules and natural isomorphisms `e_i : H^i(K ⊗ᴸ_A −) ≅ T^i(−) = Ext^i(L_{X/A}, 𝒪_X ⊗_A −)`
for `i = 1, 2` carrying the boundary map of `K` to `chartExtConnecting x hx`. -/
theorem exists_isPerfect_iso_cotangentExt_boundaryMap_of_isNoetherianRing [IsNoetherianRing A] :
    ∃ (K : DerivedCategory (ModuleCat.{u} A))
      (e₁ : derivedCohomology A K 1 ≅
        cotangentExtOne (chartStructureMap x hx) (chartBaseRingHom x hx))
      (e₂ : derivedCohomology A K 2 ≅
        cotangentExtTwo (chartStructureMap x hx) (chartBaseRingHom x hx)),
      StacksDraft.Perfect.IsPerfect K ∧
        ∀ {Sq : ShortComplex (ModuleCat.{u} A)} (hSq : Sq.ShortExact),
          boundaryMap A K hSq ≫ e₂.hom.app Sq.X₁ = e₁.hom.app Sq.X₃ ≫ chartExtConnecting x hx hSq :=
  exists_isPerfect_derivedCohomology_iso_cotangentExt_of_isNoetherianRing x hx
    (derivedCohomology_map_smul_apply A)

end AlgebraicGeometry.Space.ProperFlatLift

end
