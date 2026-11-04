module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraPullbackUnitSectionMul
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalAlgebra
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSectionChartValue

/-!
# The chart sections of an inverse image of a sheaf of graded algebras multiply

Let `k : Z ⟶ X` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf site
`B`, let `𝒜` be a sheaf of graded `𝒪_X`-algebras on the small étale site of `X` and let `d` be a
commutative diagram of étale scheme charts over `k`, a chart `d.U` of `Z` above a chart `d.V` of
`X`.  A section `s` of `𝒜_n` over `d.V` has a canonical image in `k^*𝒜_n` over `d.U`,
`AlgebraicGeometry.Space.modulePullbackChartSection`.  These images multiply as the original
sections do, the product on the right being that of the inverse image `k^*𝒜` of sheaves of
graded algebras.

For the conormal algebra `𝒞_{Z/X,*} = k^*(⨁ 𝓘ⁿ)` of Stacks 09RN this says that the class map
`𝓘ⁿ(d.V) ⟶ 𝒞_{Z/X,n}(d.U)` is multiplicative.

## Main results

* `AlgebraicGeometry.Space.moduleChartProjection_app_hom_app`: the chart projection of the direct
  image is natural in the sheaf of sets.
* `AlgebraicGeometry.Space.modulePullbackChartSection_mul`: **the chart sections of an inverse
  image of a sheaf of graded algebras multiply as the original sections do.**

## References

* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 09RN](https://stacks.math.columbia.edu/tag/09RN)
* [Stacks Project, Tag 0FQX](https://stacks.math.columbia.edu/tag/0FQX)
-/

@[expose] public section

open CategoryTheory Opposite
open Stacks.Sheaves.GradedAlgebraPullback (toposPullbackGradedAlgebra)

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Z : AlgebraicSpaces B S hS}

/-- **The chart projection of the direct image is natural in the sheaf of sets**, read on a
section. -/
theorem moduleChartProjection_app_hom_app (k : Z ⟶ X) (V : SmallEtale B S hS X.1)
    (a : StructuredArrow (op (chartBaseChange B S hS k V)) (comparisonFunctor B S hS Z).op)
    {F F' : Sheaf (SmallEtale.topology B S hS Z.1) (Type u)} (h : F ⟶ F')
    (x : ((smallEtaleDirectImage B S hS k).obj F).obj.obj (op V)) :
    (moduleChartProjection B S hS k V a).app F'
        (((smallEtaleDirectImage B S hS k).map h).hom.app (op V) x) =
      h.hom.app a.right ((moduleChartProjection B S hS k V a).app F x) := by
  have h := ConcreteCategory.congr_hom ((moduleChartProjection B S hS k V a).naturality h) x
  exact h

/-- **The chart sections of an inverse image of a sheaf of graded algebras multiply as the
original sections do.**  Over a commutative diagram `d` of étale scheme charts over `k`, the
chart section of a product of homogeneous sections of `𝒜` over `d.V` is the product, in the
inverse image `k^*𝒜`, of the chart sections of the two factors. -/
theorem modulePullbackChartSection_mul (k : Z ⟶ X)
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X))
    (d : ChartDiagram B S hS Z.1 X.1 k.hom) (i j : ℤ)
    (s : (A.piece i).val.obj (op d.V)) (t : (A.piece j).val.obj (op d.V)) :
    modulePullbackChartSection B S hS k (A.piece (i + j)) d ((A.mul i j).app (op d.V) s t) =
      ((toposPullbackGradedAlgebra (smallEtaleRingedToposModulesHom B S hS k) A).mul i j).app
        (op d.U) (modulePullbackChartSection B S hS k (A.piece i) d s)
        (modulePullbackChartSection B S hS k (A.piece j) d t) :=
  Stacks.Sheaves.GradedAlgebraEssentiallySmall.natural_family_pullbackUnit_mul
    (smallEtaleRingedToposHom B S hS k) (op d.V) (op d.U)
    (fun F => (moduleChartProjection B S hS k d.V (indexOfChartDiagram B S hS k d)).app F)
    (fun g x => moduleChartProjection_app_hom_app B S hS k d.V _ g x) A i j s t

end AlgebraicGeometry.Space

end
