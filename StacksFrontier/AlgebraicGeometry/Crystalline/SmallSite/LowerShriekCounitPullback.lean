module

public import StacksFrontier.AlgebraicGeometry.Crystalline.ChangeBaseBigCohomology

/-!
# The pullback of the counit of `i_! ⊣ i^{-1}` along a morphism of crystalline situations

Let `f : X/S ⟶ X'/S'` be a morphism of global crystalline situations and `N` a sheaf of
`𝒪_{X'/S'}`-modules on the big crystalline site `CRIS(X'/S')`.  The module pullback
`f_cris^*` of [Stacks, Tag 07Q9], `...SmallSite.crisModuleInverseImage`, is
`i_{X', !}` followed by restriction along `Cris(X/S) ⥤ CRIS(X/S) ⥤ CRIS(X'/S')`.  So
`f_cris^*(i_{X'}^{-1}N)` maps to `i_X^{-1}f_CRIS^*N` by the counit `i_{X', !}i_{X'}^{-1}N ⟶ N`.
This file defines that map, `lowerShriekCounitPullback`.

## Main definitions

* `Crystalline.GlobalCrystallineSituation.SmallSite.lowerShriekCounitPullback`: the map
  `f_cris^*(i_{X'}^{-1}N) ⟶ i_X^{-1}f_CRIS^*N`.

## References

* [Stacks Project, Tag 07IJ](https://stacks.math.columbia.edu/tag/07IJ)
* [Stacks Project, Tag 07Q9](https://stacks.math.columbia.edu/tag/07Q9)
* [Stacks Project, Tag 07N5](https://stacks.math.columbia.edu/tag/07N5)
-/


@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable {S S' : GlobalCrystallineSituation.{u}} (fS : S.S ⟶ S'.S) (fX : S.X ⟶ S'.X)
  (hf : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap fS = fX ≫ S'.toClosedFiber)

/-- **`f_cris^*(i^{-1}N) ⟶ i^{-1}f_CRIS^*N`**, for a sheaf of `𝒪_{X'/S'}`-modules `N` on the big
crystalline site `CRIS(X'/S')`: the restriction along `Cris(X/S) ⥤ CRIS(X/S) ⥤ CRIS(X'/S')` of
the counit `i_!i^{-1}N ⟶ N` of `...SmallSite.moduleLowerShriekAdjunction`, with `i^{-1}` on both
sides being `...SmallSite.moduleRestrictι`. -/
def lowerShriekCounitPullback (N : BigModuleSheaf S') :
    (crisModuleInverseImage fS fX hf).obj ((moduleRestrictι S').obj N) ⟶
      (moduleRestrictι S).obj ((changeBaseBigModulePullback S S' fS fX hf).obj N) :=
  (crisModulePullback.{u + 1} fS fX hf).map
      ((moduleLowerShriek S').map ((crisRestrictModulesIsoModuleRestrictι S').inv.app N) ≫
        (moduleLowerShriekAdjunction S').counit.app N) ≫
    (crisRestrictModulesIsoModuleRestrictι S).hom.app
      ((changeBaseBigModulePullback S S' fS fX hf).obj N)

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
