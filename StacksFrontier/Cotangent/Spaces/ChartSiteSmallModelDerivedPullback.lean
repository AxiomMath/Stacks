module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.CoefficientChange
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.ResolutionsOnARingedSite
public import StacksFrontier.Cotangent.Spaces.ChartSiteDifferentials
public import StacksFrontier.Cotangent.Spaces.ChartSiteSmallModel

/-!
# K-flat resolutions and the derived horizontal pullback on the chart site

On the small model of the site of polynomial charts the whole diagram of Tag 08VK lives in the
single universe `u + 1`: the site, its morphisms and the sections of its sheaves of rings. The
K-flat resolutions of Tag 06YS and the derived pullback of Tag 06YY are therefore available
there, and the horizontal arrow `i` of the diagram — the identity on underlying topoi with
structure map `i♯ : 𝒪 ⟶ π⁻¹𝒪_X` — has a total left derived module pullback `Li^*`.

## Main definitions

* `AlgebraicGeometry.Space.PolynomialChart.smallAffineSheaf` and
  `AlgebraicGeometry.Space.PolynomialChart.smallChartStructureSheaf`: the sheaves of rings `𝒪` and
  `π⁻¹𝒪_X` of Tag 08VK read on the small model.
* `AlgebraicGeometry.Space.PolynomialChart.smallEvaluation`: `i♯` read on the small model.
* `AlgebraicGeometry.Space.PolynomialChart.derivedSmallHorizontalPullback`: `Li^*`.

## Main results

* `AlgebraicGeometry.Space.PolynomialChart.exists_kFlatResolution_smallAffineSheaf`: **Tag 06YS for
  the chart site**, on the small model: every complex of `𝒪`-modules admits a termwise
  surjective quasi-isomorphism from a K-flat complex with flat terms.
* `AlgebraicGeometry.Space.PolynomialChart.hasLeftDerivedFunctor_smallEvaluation`: the total left
  derived functor of the module pullback along `i` exists.

## Implementation notes

The coefficient universe is `u + 1`, the universe of the objects of the chart site, in which
the ringed topoi of Tag 08VK are formed. Tag 06YS and the derived pullback of Tag 06YY are
stated for a site whose objects, morphisms and ring sections share one universe, which no
presentation of the chart site itself satisfies: its objects lie in `Type (u + 1)` and its
morphisms in `Type u`.

The pullback of sheaves of modules along `i` is extension of scalars along `i♯`, because `i` is
the identity on underlying topoi; `AlgebraicGeometry.RingedToposSiteHom.coefficientChange` is
that morphism of ringed topoi and
`AlgebraicGeometry.RingedToposSiteHom.pullbackTopos_coefficientChange` identifies its module
pullback. So the derived functor below is the derived pullback of Tag 06YY along `i`, with no
hypothesis beyond the data of the diagram.

## References

* [Stacks Project, Tag 08VK](https://stacks.math.columbia.edu/tag/08VK)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

universe u

namespace AlgebraicGeometry.Space.PolynomialChart

attribute [local instance] HasDerivedCategory.standard

variable (Λ : Type u) [CommRing Λ] (B : BigFppfSite.{u})
  (hS : B.Contains (Spec (CommRingCat.of Λ)))
  (X : (BigFppfOver B (Spec (CommRingCat.of Λ)) hS)ᵒᵖ ⥤ Type u)
  (hX : IsAlgebraicSpace B (Spec (CommRingCat.of Λ)) hS X)

/-! ### The sheaves of rings of the diagram, read on the small model -/

/-- Restriction of sheaves of commutative rings from the chart site to the small model. It is
an equivalence, being `smallChartSheafEquiv` at `CommRingCat`. -/
abbrev restrictRingsToSmallChart :
    Sheaf (topology Λ B hS X hX) CommRingCat.{u + 1} ⥤
      Sheaf (smallChartTopology Λ B hS X hX) CommRingCat.{u + 1} :=
  (smallChartFunctor Λ B hS X hX).sheafPushforwardContinuous CommRingCat.{u + 1}
    (smallChartTopology Λ B hS X hX) (topology Λ B hS X hX)

/-- The sheaf of affine functions `𝒪` of Tag 08VK, read on the small model. -/
abbrev smallAffineSheaf : Sheaf (smallChartTopology Λ B hS X hX) CommRingCat.{u + 1} :=
  (restrictRingsToSmallChart Λ B hS X hX).obj (liftedAffineSheaf Λ B hS X hX)

/-- The sheaf of rings `π⁻¹𝒪_X` of Tag 08VK, read on the small model. -/
abbrev smallChartStructureSheaf :
    Sheaf (smallChartTopology Λ B hS X hX) CommRingCat.{u + 1} :=
  (restrictRingsToSmallChart Λ B hS X hX).obj
    (chartStructureSheaf Λ B hS X hX)

/-- `i♯ : 𝒪 ⟶ π⁻¹𝒪_X` on the chart site: the structure map of the horizontal arrow of the
diagram of Tag 08VK, read through the identification `i⁻¹𝒪 ≅ 𝒪`. -/
def evaluationRingMap :
    liftedAffineSheaf Λ B hS X hX ⟶ chartStructureSheaf Λ B hS X hX :=
  (liftedIdentityRingIso Λ B hS X hX).inv ≫
    liftedHorizontalMapInverse Λ B hS X hX

/-- `i♯ : 𝒪 ⟶ π⁻¹𝒪_X`, read on the small model. -/
def smallEvaluation :
    smallAffineSheaf Λ B hS X hX ⟶ smallChartStructureSheaf Λ B hS X hX :=
  (restrictRingsToSmallChart Λ B hS X hX).map (evaluationRingMap Λ B hS X hX)

/-! ### K-flat resolutions -/

/-- **Tag 06YS on the site of polynomial charts.** Every complex of `𝒪`-modules on the small
model of the chart site admits a termwise surjective quasi-isomorphism from a K-flat complex
whose terms are flat. -/
theorem exists_kFlatResolution_smallAffineSheaf
    (G : CochainComplex (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallAffineSheaf Λ B hS X hX))) ℤ) :
    ∃ (K : CochainComplex (SheafOfModules.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallAffineSheaf Λ B hS X hX))) ℤ)
      (f : K ⟶ G),
      @CochainComplex.KFlatBifunctor.KFlat
          (SheafOfModules.{u + 1}
            (Stacks.SheafOfModules.Tensor.ringSheaf (smallAffineSheaf Λ B hS X hX)))
          (SheafOfModules.{u + 1}
            (Stacks.SheafOfModules.Tensor.ringSheaf (smallAffineSheaf Λ B hS X hX)))
          (SheafOfModules.{u + 1}
            (Stacks.SheafOfModules.Tensor.ringSheaf (smallAffineSheaf Λ B hS X hX)))
          inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u + 1, u + 1, u + 1, u + 1}
            (smallAffineSheaf Λ B hS X hX))
          (Stacks.SheafOfModules.Tensor.sheafTensor_additive.{u + 1, u + 1, u + 1, u + 1, u + 1}
            (smallAffineSheaf Λ B hS X hX))
          (Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive.{u + 1, u + 1, u + 1, u + 1, u + 1}
            (smallAffineSheaf Λ B hS X hX))
          (Stacks.SheafOfModules.Tensor.hasMapBifunctor_sheafTensor.{u + 1, u + 1, u + 1}
            (smallAffineSheaf Λ B hS X hX)) K ∧
        (∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u + 1, u + 1, u + 1, u + 1}
          (O := smallAffineSheaf Λ B hS X hX) (K.X i)) ∧
        QuasiIso f ∧ ∀ i : ℤ, Epi (f.f i) :=
  Stacks.SheafOfModules.KFlatResolution.exists_kFlatResolution
    (smallAffineSheaf Λ B hS X hX) G

/-! ### The derived pullback along the horizontal arrow -/

/-- The ringed topos `(Sh(C_{X/Λ}), 𝒪)` of Tag 08VK, on the small model: a ringed topos with
its site, its morphisms and its ring sections all in the universe `u + 1`. -/
abbrev smallAffineRingedTopos : RingedTopos.{u + 1, u + 1, u + 1} :=
  Stacks.Cohomology.ringedTopos (smallChartTopology Λ B hS X hX)
    (smallAffineSheaf Λ B hS X hX)

/-- The horizontal arrow `i : (Sh(C_{X/Λ}), π⁻¹𝒪_X) ⟶ (Sh(C_{X/Λ}), 𝒪)` of Tag 08VK, on the
small model: change of coefficient rings along `i♯`. -/
abbrev smallHorizontal :
    RingedToposSiteHom
      (Stacks.Cohomology.ringedTopos (smallChartTopology Λ B hS X hX)
        (smallChartStructureSheaf Λ B hS X hX))
      (smallAffineRingedTopos Λ B hS X hX) :=
  RingedToposSiteHom.coefficientChange (smallChartTopology Λ B hS X hX)
    (smallEvaluation Λ B hS X hX)

/-- **The total left derived functor of the module pullback along `i` exists.** -/
theorem hasLeftDerivedFunctor_smallEvaluation :
    (pullbackOnHomotopy (smallHorizontal Λ B hS X hX)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u + 1}
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallAffineRingedTopos Λ B hS X hX).O))
        (ComplexShape.up ℤ)) :=
  Stacks.Cohomology.hasLeftDerivedFunctor_pullbackOnHomotopy_coefficientChange
    (smallEvaluation Λ B hS X hX)

/-- `Li^* : D(𝒪) ⥤ D(π⁻¹𝒪_X)`, the derived pullback of sheaves of modules along the horizontal
arrow of the diagram of Tag 08VK, on the small model of the chart site. -/
abbrev derivedSmallHorizontalPullback :
    DerivedCategory (SheafOfModules.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallAffineRingedTopos Λ B hS X hX).O)) ⥤
      DerivedCategory (SheafOfModules.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (Stacks.Cohomology.ringedTopos (smallChartTopology Λ B hS X hX)
            (smallChartStructureSheaf Λ B hS X hX)).O)) :=
  Stacks.Cohomology.derivedCoefficientChange.{u + 1} (smallEvaluation Λ B hS X hX)

end AlgebraicGeometry.Space.PolynomialChart

end
