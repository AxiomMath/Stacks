module

public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedStalk.StalkSpellingGermBridge

/-!
# The unit compatibility of the stalk formula

For a morphism of schemes `f : X ⟶ Y` and a point `x` of `X`, the stalk formula
`Stacks.ModuleSkyscraper.pullbackStalkIso` of Tag 0098 is the mate of the germ map
`Stacks.ModuleSkyscraper.pushStalkMap` under `f^* ⊣ f_*` and
`extendScalars (f^♯_x) ⊣ restrictScalars (f^♯_x)`. This file proves the component identity of
this mate correspondence for the units, in two spellings of the stalk ring.

## Main results

* `Stacks.ModuleSkyscraper.map_unit_comp_pushStalkMap`: the stalk at `f x` of the unit
  `N ⟶ f_*(f^*N)` of `f^* ⊣ f_*`, followed by the germ map `(f_*(f^*N))_{f x} ⟶ (f^*N)_x`, is the
  unit of `extendScalars (f^♯_x) ⊣ restrictScalars (f^♯_x)` at `N_{f x}` followed by restriction
  of scalars of the stalk formula of Tag 0098.
* `AlgebraicGeometry.map_unit_comp_restrictScalarsStalkPushforwardMap`: the same for the
  `RingCat`-stalk comparison map read over the local rings.

## References

* [Stacks Project, Tag 0096](https://stacks.math.columbia.edu/tag/0096)
* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open RingedSpaceModuleAdjunction

noncomputable section

universe u

namespace Stacks.ModuleSkyscraper

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)

/-- Taking the stalk at `f x` of the unit `N ⟶ f_*(f^*N)` of `f^* ⊣ f_*` and following it with
the germ map `pushStalkMap` gives the unit
`N_{f x} ⟶ restrictScalars (𝒪_{X,x} ⊗_{𝒪_{Y,f x}} N_{f x})` of
`extendScalars (f^♯_x) ⊣ restrictScalars (f^♯_x)`, followed by restriction of scalars of the
stalk formula of Tag 0098. -/
theorem map_unit_comp_pushStalkMap (N : Y.Modules) :
    (modulesStalkFunctor Y (f x)).map
          ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N) ≫
        (pushStalkMap f x).app ((Scheme.Modules.pullback f).obj N) =
      (ModuleCat.extendRestrictScalarsAdj (f.stalkMap x).hom).unit.app
          ((modulesStalkFunctor Y (f x)).obj N) ≫
        (ModuleCat.restrictScalars.{u, u, u} (f.stalkMap x).hom).map
          ((pullbackStalkIso f x).hom.app N) :=
  unit_mateEquiv (Scheme.Modules.pullbackPushforwardAdjunction f)
    (ModuleCat.extendRestrictScalarsAdj (f.stalkMap x).hom)
    (TwoSquare.mk _ _ _ _ (pullbackStalkIso f x).hom) N

end Stacks.ModuleSkyscraper

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)

/-- The stalk at `f x` of the unit of `f^* ⊣ f_*` followed by the `RingCat`-stalk germ map read
over the local rings is the unit of `extendScalars (f^♯_x) ⊣ restrictScalars (f^♯_x)` followed by
restriction of scalars of the stalk formula of Tag 0098. -/
theorem map_unit_comp_restrictScalarsStalkPushforwardMap (N : Y.Modules) :
    (Stacks.ModuleSkyscraper.modulesStalkFunctor Y (f x)).map
          ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N) ≫
        restrictScalarsStalkPushforwardMap f x ((Scheme.Modules.pullback f).obj N) =
      (ModuleCat.extendRestrictScalarsAdj (f.stalkMap x).hom).unit.app
          ((Stacks.ModuleSkyscraper.modulesStalkFunctor Y (f x)).obj N) ≫
        (ModuleCat.restrictScalars.{u, u, u} (f.stalkMap x).hom).map
          ((Stacks.ModuleSkyscraper.pullbackStalkIso f x).hom.app N) := by
  rw [← pushStalkMap_app_eq_restrictScalarsStalkPushforwardMap]
  exact Stacks.ModuleSkyscraper.map_unit_comp_pushStalkMap f x N

end AlgebraicGeometry

end

end
