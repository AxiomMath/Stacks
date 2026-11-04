module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardBaseScalars
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullback

/-!
# Multiplication by a pulled-back function and the unit of `f^* ⊣ f_*`

For a morphism `f : X ⟶ Y` of algebraic spaces, a morphism `h : Y ⟶ T` to an object of the site
and a function `x` on `T`, the unit `𝓜 ⟶ f_*f^*𝓜` of the adjunction of Stacks 03LU carries
multiplication by `h^♯ x` on `𝓜` to the direct image of multiplication by `(f ≫ h)^♯ x` on
`f^*𝓜`. This is how multiplication by a function of a thickening of the base is compared along a
morphism of thickenings.

## Main results

* `AlgebraicGeometry.Space.modulePullbackAdjunction_unit_comp_map_globalSmul`.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The unit of `f^* ⊣ f_*` carries multiplication by `h^♯ x` to multiplication by
`(f ≫ h)^♯ x`**: the direct image of multiplication by the pulled-back function on `f^*𝓜` is
multiplication by `h^♯ x` on `f_*f^*𝓜`
(`AlgebraicGeometry.Space.modulePushforward_map_globalSmul_pullbackToGlobalFunctions`), and the
unit is linear for the global functions of `Y`. -/
theorem modulePullbackAdjunction_unit_comp_map_globalSmul {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) {T : BigFppfOver B S hS} (h : Y ⟶ schemeSpace T)
    (x : Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)) (M : Modules.{u, u} B S hS Y.1 Y.2) :
    (modulePullbackAdjunction B S hS f).unit.app M ≫
        (modulePushforward B S hS f).map
          (Stacks.Cohomology.SiteModules.globalSmul
            ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))
            (pullbackToGlobalFunctions B S hS X T (f ≫ h) x) ((modulePullback B S hS f).obj M)) =
      Stacks.Cohomology.SiteModules.globalSmul
          ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))
          (pullbackToGlobalFunctions B S hS Y T h x) M ≫
        (modulePullbackAdjunction B S hS f).unit.app M := by
  rw [modulePushforward_map_globalSmul_pullbackToGlobalFunctions]
  exact Stacks.Cohomology.SiteModules.comp_globalSmul _ _ _

end AlgebraicGeometry.Space

end
