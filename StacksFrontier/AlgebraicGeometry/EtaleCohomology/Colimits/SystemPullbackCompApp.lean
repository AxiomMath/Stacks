module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SystemPullbackComparison

/-!
# Components of the comparison of iterated inverse images

The component at a sheaf of the comparison `f⁻¹ g⁻¹ ≅ (f ≫ g)⁻¹` of inverse images on small étale
sites, with its two naturality squares.

## Main definitions

* `smallEtalePullbackAbCompApp`: the isomorphism `f⁻¹(g⁻¹M) ≅ (f ≫ g)⁻¹M` for a sheaf `M`.

## Main results

* `smallEtalePullbackAbCompApp_hom_naturality`: the forward isomorphisms are natural in `M`.
* `smallEtalePullbackAbCompApp_inv_naturality`: the inverse isomorphisms are natural in `M`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

/-! ### Components with iterated inverse images -/

/-- The component at a sheaf `M` of the comparison of inverse images along a named composite, with
its source written as the iterated inverse image `f⁻¹(g⁻¹M)`. -/
def smallEtalePullbackAbCompApp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    (hfg : fg = f ≫ g) (M : Sheaf (smallEtaleTopology Z) Ab.{u + 1}) :
    (smallEtalePullbackAb f).obj ((smallEtalePullbackAb g).obj M) ≅
      (smallEtalePullbackAb fg).obj M :=
  (smallEtalePullbackAbComp' f g fg hfg).app M

/-- For a morphism `φ : M ⟶ N` of sheaves, the components `f⁻¹(g⁻¹M) ≅ fg⁻¹M` and
`f⁻¹(g⁻¹N) ≅ fg⁻¹N` intertwine `f⁻¹(g⁻¹φ)` and `fg⁻¹φ`. -/
theorem smallEtalePullbackAbCompApp_hom_naturality {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ Z) (fg : X ⟶ Z) (hfg : fg = f ≫ g) {M N : Sheaf (smallEtaleTopology Z) Ab.{u + 1}}
    (φ : M ⟶ N) :
    (smallEtalePullbackAb f).map ((smallEtalePullbackAb g).map φ) ≫
        (smallEtalePullbackAbCompApp f g fg hfg N).hom =
      (smallEtalePullbackAbCompApp f g fg hfg M).hom ≫ (smallEtalePullbackAb fg).map φ :=
  (smallEtalePullbackAbComp' f g fg hfg).hom.naturality φ

/-- For a morphism `φ : M ⟶ N` of sheaves, the inverses of the components `f⁻¹(g⁻¹M) ≅ fg⁻¹M`
and `f⁻¹(g⁻¹N) ≅ fg⁻¹N` intertwine `fg⁻¹φ` and `f⁻¹(g⁻¹φ)`. -/
theorem smallEtalePullbackAbCompApp_inv_naturality {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ Z) (fg : X ⟶ Z) (hfg : fg = f ≫ g) {M N : Sheaf (smallEtaleTopology Z) Ab.{u + 1}}
    (φ : M ⟶ N) :
    (smallEtalePullbackAb fg).map φ ≫ (smallEtalePullbackAbCompApp f g fg hfg N).inv =
      (smallEtalePullbackAbCompApp f g fg hfg M).inv ≫
        (smallEtalePullbackAb f).map ((smallEtalePullbackAb g).map φ) :=
  (smallEtalePullbackAbComp' f g fg hfg).inv.naturality φ

end Stacks.EtaleCohomology

end
