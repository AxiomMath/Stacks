module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.SmallEtaleBaseChangePasting
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.AbelianBaseChangeMapFunctoriality

/-!
# The degreewise pasting law for the base change map of abelian small étale sheaves

For two horizontally composable commutative squares of schemes

```
X₂ --v₂--> X₁ --v₁--> X₀
|g₂         |g₁        |g₀
v           v          v
S₂ --u₂--> S₁ --u₁--> S₀
```

on a bounded below complex, the degreewise image of the base change map of the outer rectangle
is the composite of the degreewise images of the base change maps of the two squares, read
through the degreewise composition isomorphisms of the inverse images along the two composite
horizontal legs.

## Main results

* `Stacks.EtaleCohomology.smallEtaleBaseChangeAb_mapPlus_paste_app`: **the degreewise pasting
  law**, for `Stacks.Cohomology.BaseChange.mapPlus`.

## References

* [Stacks Project, Tag 0E47](https://stacks.math.columbia.edu/tag/0E47)
* [Stacks Project, Tag 0F02](https://stacks.math.columbia.edu/tag/0F02)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

section DegreewisePaste

variable {X₀ X₁ X₂ S₀ S₁ S₂ : Scheme.{u}} (g₀ : X₀ ⟶ S₀) (g₁ : X₁ ⟶ S₁) (g₂ : X₂ ⟶ S₂)
  (u₁ : S₁ ⟶ S₀) (u₂ : S₂ ⟶ S₁) (v₁ : X₁ ⟶ X₀) (v₂ : X₂ ⟶ X₁)
  (w₁ : g₁ ≫ u₁ = v₁ ≫ g₀) (w₂ : g₂ ≫ u₂ = v₂ ≫ g₁)

/-- **The degreewise pasting law for the base change map of abelian small étale sheaves.** On
a bounded below complex `K`, the degreewise image of the base change map of the outer
rectangle is the composite of the degreewise images of the base change maps of the two
squares, read through the degreewise composition isomorphisms of the inverse images along the
two composite horizontal legs. -/
theorem smallEtaleBaseChangeAb_mapPlus_paste_app
    (K : HomotopyCategory.Plus (Sheaf (smallEtaleTopology X₀) Ab.{u + 1})) :
    (Stacks.Cohomology.BaseChange.mapPlus
          (smallEtaleBaseChangeAb (u₂ ≫ u₁) g₀ g₂ (v₂ ≫ v₁)
            (smallEtaleRectangle_comm g₀ g₁ g₂ u₁ u₂ v₁ v₂ w₁ w₂))).app K =
      (Functor.mapHomotopyCategoryPlusCompIso
            (smallEtalePullbackAbCompIso u₂ u₁)).inv.app
          ((smallEtalePushforwardAb g₀).mapHomotopyCategoryPlus.obj K) ≫
        (smallEtalePullbackAb u₂).mapHomotopyCategoryPlus.map
            ((Stacks.Cohomology.BaseChange.mapPlus
              (smallEtaleBaseChangeAb u₁ g₀ g₁ v₁ w₁)).app K) ≫
          (Stacks.Cohomology.BaseChange.mapPlus
                (smallEtaleBaseChangeAb u₂ g₁ g₂ v₂ w₂)).app
              ((smallEtalePullbackAb v₁).mapHomotopyCategoryPlus.obj K) ≫
            (smallEtalePushforwardAb g₂).mapHomotopyCategoryPlus.map
              ((Functor.mapHomotopyCategoryPlusCompIso
                (smallEtalePullbackAbCompIso v₂ v₁)).hom.app K) :=
  Stacks.Cohomology.BaseChange.mapPlus_paste_app
    (smallEtalePushforwardAb g₀) (smallEtalePushforwardAb g₁) (smallEtalePushforwardAb g₂)
    (smallEtalePullbackAb u₁) (smallEtalePullbackAb u₂) (smallEtalePullbackAb (u₂ ≫ u₁))
    (smallEtalePullbackAb v₁) (smallEtalePullbackAb v₂) (smallEtalePullbackAb (v₂ ≫ v₁))
    (smallEtalePullbackAbCompIso u₂ u₁) (smallEtalePullbackAbCompIso v₂ v₁) _ _ _
    (smallEtaleBaseChangeAb_paste_app g₀ g₁ g₂ u₁ u₂ v₁ v₂ w₁ w₂) K

end DegreewisePaste

end Stacks.EtaleCohomology

end
