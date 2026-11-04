module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartQuasicoherentModuleGlueingEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartModuleGlueingEquivalence
import StacksCore.Tactic.StacksAttribute

/-!
# Quasi-coherent modules are the chartwise quasi-coherent glueing data

Stacks 03LZ is Stacks 03LY cut down to the quasi-coherent objects on both sides.  Stacks 03LY is
an equivalence, `AlgebraicGeometry.Space.chartModuleGlueingEquivalence`, whose functor is the
canonical chartwise description `AlgebraicGeometry.Space.chartModuleGlueingFunctor`; chartwise
quasi-coherence of the glueing datum of a module is quasi-coherence of the module,
`AlgebraicGeometry.Space.inverseImage_isChartwiseQuasicoherent`; and chartwise quasi-coherence is
invariant under isomorphism of glueing data.  So `CategoryTheory.Equivalence.congrFullSubcategory`
cuts Stacks 03LY down to Stacks 03LZ.

## Main results

* `AlgebraicGeometry.Space.quasicoherentChartModuleGlueingEquivalence`: **Stacks 03LZ**, the
  equivalence between quasi-coherent `𝒪_X`-modules on the small étale site of an algebraic space
  `X` and the chartwise quasi-coherent glueing data.
* `AlgebraicGeometry.Space.quasicoherentChartModuleGlueingFunctor_isEquivalence`: that
  equivalence is the canonical chartwise description of quasi-coherent modules,
  `AlgebraicGeometry.Space.quasicoherentChartModuleGlueingFunctor`.

## References

* [Stacks Project, Tag 03LZ](https://stacks.math.columbia.edu/tag/03LZ)
* [Stacks Project, Tag 03LY](https://stacks.math.columbia.edu/tag/03LY)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-- A quasi-coherent `𝒪_X`-module on the small étale site of an algebraic space `X` is the same
thing as a chartwise quasi-coherent glueing datum: a *quasi-coherent* `𝒪_U`-module `F_U` on the
small étale site of every étale scheme chart `U` of `X`, transition isomorphisms
`c_f : f^*F_U ≅ F_V` along the chartwise pullbacks of Stacks 03LU for the morphisms `f : V ⟶ U`
of charts, and the cocycle condition `c_g ∘ g^*c_f = c_{g ≫ f}` — an *equivalence of categories*,
given by sending a quasi-coherent module to the family of its restrictions to the charts.

It is the equivalence `AlgebraicGeometry.Space.chartModuleGlueingEquivalence` of Stacks 03LY,
cut down to the quasi-coherent objects on both sides. -/
@[stacks 03LZ "quasi-coherent modules are the chartwise quasi-coherent glueing data"]
def quasicoherentChartModuleGlueingEquivalence :
    QuasicoherentSheaves.{u, u} B S hS X.1 X.2 ≌ QuasicoherentChartModuleGlueingData B S hS X :=
  (chartModuleGlueingEquivalence B S hS X).congrFullSubcategory
    (inverseImage_isChartwiseQuasicoherent B S hS X)

/-- The functor of `AlgebraicGeometry.Space.quasicoherentChartModuleGlueingEquivalence` is the
canonical chartwise description of quasi-coherent modules: it sends a quasi-coherent
`𝒪_X`-module to the family of its restrictions to the étale scheme charts. -/
theorem quasicoherentChartModuleGlueingEquivalence_functor :
    (quasicoherentChartModuleGlueingEquivalence B S hS X).functor =
      quasicoherentChartModuleGlueingFunctor B S hS X := rfl

/-- The canonical chartwise description of quasi-coherent `𝒪_X`-modules
`AlgebraicGeometry.Space.quasicoherentChartModuleGlueingFunctor` — restriction to the étale
scheme charts — is an equivalence onto the chartwise quasi-coherent glueing data. -/
@[stacks 03LZ "the canonical chartwise description of quasi-coherent modules is an equivalence"]
instance quasicoherentChartModuleGlueingFunctor_isEquivalence :
    (quasicoherentChartModuleGlueingFunctor B S hS X).IsEquivalence :=
  (quasicoherentChartModuleGlueingEquivalence B S hS X).isEquivalence_functor

end AlgebraicGeometry.Space

end
