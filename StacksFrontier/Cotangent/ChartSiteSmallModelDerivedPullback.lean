module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.CoefficientChange
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.ResolutionsOnARingedSite
public import StacksFrontier.Cotangent.ChartSiteSmallModel
import StacksCore.Tactic.StacksAttribute

/-!
# K-flat resolutions and the derived horizontal pullback on the chart site

On the small model of the site of polynomial charts the whole diagram of Tag 08VA lives in the
single universe `u + 1`: the site, its morphisms and the sections of its sheaves of rings. The
K-flat resolutions of Tag 06YS and the derived pullback of Tag 06YY are therefore available
there, and the horizontal arrow `i` of the diagram — the identity on underlying topoi with
structure map `i♯ : 𝒪 ⟶ π⁻¹𝒪_X` — has a total left derived module pullback `Li^*`.

## Main definitions

* `AlgebraicGeometry.PolynomialChart.smallAffineSheaf` and
  `AlgebraicGeometry.PolynomialChart.smallChartStructureSheaf`: the sheaves of rings `𝒪` and
  `π⁻¹𝒪_X` of Tag 08VA read on the small model.
* `AlgebraicGeometry.PolynomialChart.smallEvaluation`: `i♯` read on the small model.
* `AlgebraicGeometry.PolynomialChart.derivedSmallHorizontalPullback`: `Li^*`.

## Main results

* `AlgebraicGeometry.PolynomialChart.exists_kFlatResolution_smallAffineSheaf`: **Tag 06YS for
  the chart site**, on the small model: every complex of `𝒪`-modules admits a termwise
  surjective quasi-isomorphism from a K-flat complex with flat terms.
* `AlgebraicGeometry.PolynomialChart.hasLeftDerivedFunctor_smallEvaluation`: the total left
  derived functor of the module pullback along `i` exists.

## Implementation notes

The coefficient universe of Tag 08VA is `max w (u + 1)` for a free `w`; it is specialized here
to `w = u + 1`, which is the smallest value and the only one that meets the universe of the
site. Tag 06YS and the derived pullback of Tag 06YY are stated for a site whose objects,
morphisms and ring sections share one universe, which no presentation of the chart site itself
satisfies: its objects lie in `Type (u + 1)` and its morphisms in `Type u`.

The pullback of sheaves of modules along `i` is extension of scalars along `i♯`, because `i` is
the identity on underlying topoi; `AlgebraicGeometry.RingedToposSiteHom.coefficientChange` is
that morphism of ringed topoi and
`AlgebraicGeometry.RingedToposSiteHom.pullbackTopos_coefficientChange` identifies its module
pullback. So the derived functor below is the derived pullback of Tag 06YY along `i`, with no
hypothesis beyond the data of the diagram.

## References

* [Stacks Project, Tag 08VA](https://stacks.math.columbia.edu/tag/08VA)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

universe u

namespace AlgebraicGeometry.PolynomialChart

attribute [local instance] HasDerivedCategory.standard

variable (Λ : Type u) [CommRing Λ] (X : Scheme.{u})
    (structureMap : X ⟶ Spec (CommRingCat.of Λ))

/-! ### The sheaves of rings of the diagram, read on the small model -/

/-- Restriction of sheaves of commutative rings from the chart site to the small model. It is
an equivalence, being `smallChartSheafEquiv` at `CommRingCat`. -/
abbrev restrictRingsToSmallChart :
    Sheaf (topology Λ X structureMap) CommRingCat.{u + 1} ⥤
      Sheaf (smallChartTopology Λ X structureMap) CommRingCat.{u + 1} :=
  (smallChartFunctor Λ X structureMap).sheafPushforwardContinuous CommRingCat.{u + 1}
    (smallChartTopology Λ X structureMap) (topology Λ X structureMap)

/-- The sheaf of affine functions `𝒪` of Tag 08VA, read on the small model. -/
abbrev smallAffineSheaf : Sheaf (smallChartTopology Λ X structureMap) CommRingCat.{u + 1} :=
  (restrictRingsToSmallChart Λ X structureMap).obj (affineSheaf.{u, u + 1} Λ X structureMap)

/-- The sheaf of rings `π⁻¹𝒪_X` of Tag 08VA, read on the small model. -/
abbrev smallChartStructureSheaf :
    Sheaf (smallChartTopology Λ X structureMap) CommRingCat.{u + 1} :=
  (restrictRingsToSmallChart Λ X structureMap).obj
    (chartStructureSheaf.{u, u + 1} Λ X structureMap)

/-- `i♯ : 𝒪 ⟶ π⁻¹𝒪_X` on the chart site: the structure map of the horizontal arrow of the
diagram of Tag 08VA, read through the identification `i⁻¹𝒪 ≅ 𝒪`. -/
def evaluationRingMap :
    affineSheaf.{u, u + 1} Λ X structureMap ⟶ chartStructureSheaf.{u, u + 1} Λ X structureMap :=
  (identityRingIso.{u, u + 1} Λ X structureMap).inv ≫
    horizontalMapInverse.{u, u + 1} Λ X structureMap

/-- `i♯ : 𝒪 ⟶ π⁻¹𝒪_X`, read on the small model. -/
def smallEvaluation :
    smallAffineSheaf Λ X structureMap ⟶ smallChartStructureSheaf Λ X structureMap :=
  (restrictRingsToSmallChart Λ X structureMap).map (evaluationRingMap Λ X structureMap)

/-! ### K-flat resolutions -/

/-- **Tag 06YS on the site of polynomial charts.** Every complex of `𝒪`-modules on the small
model of the chart site admits a termwise surjective quasi-isomorphism from a K-flat complex
whose terms are flat. -/
theorem exists_kFlatResolution_smallAffineSheaf
    (G : CochainComplex (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallAffineSheaf Λ X structureMap))) ℤ) :
    ∃ (K : CochainComplex (SheafOfModules.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallAffineSheaf Λ X structureMap))) ℤ)
      (f : K ⟶ G),
      @CochainComplex.KFlatBifunctor.KFlat
          (SheafOfModules.{u + 1}
            (Stacks.SheafOfModules.Tensor.ringSheaf (smallAffineSheaf Λ X structureMap)))
          (SheafOfModules.{u + 1}
            (Stacks.SheafOfModules.Tensor.ringSheaf (smallAffineSheaf Λ X structureMap)))
          (SheafOfModules.{u + 1}
            (Stacks.SheafOfModules.Tensor.ringSheaf (smallAffineSheaf Λ X structureMap)))
          inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u + 1, u + 1, u + 1, u + 1}
            (smallAffineSheaf Λ X structureMap))
          (Stacks.SheafOfModules.Tensor.sheafTensor_additive.{u + 1, u + 1, u + 1, u + 1, u + 1}
            (smallAffineSheaf Λ X structureMap))
          (Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive.{u + 1, u + 1, u + 1, u + 1, u + 1}
            (smallAffineSheaf Λ X structureMap))
          (Stacks.SheafOfModules.Tensor.hasMapBifunctor_sheafTensor.{u + 1, u + 1, u + 1}
            (smallAffineSheaf Λ X structureMap)) K ∧
        (∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u + 1, u + 1, u + 1, u + 1}
          (O := smallAffineSheaf Λ X structureMap) (K.X i)) ∧
        QuasiIso f ∧ ∀ i : ℤ, Epi (f.f i) :=
  Stacks.SheafOfModules.KFlatResolution.exists_kFlatResolution
    (smallAffineSheaf Λ X structureMap) G

/-! ### The derived pullback along the horizontal arrow -/

/-- The ringed topos `(Sh(C_{X/Λ}), 𝒪)` of Tag 08VA, on the small model: a ringed topos with
its site, its morphisms and its ring sections all in the universe `u + 1`. -/
abbrev smallAffineRingedTopos : RingedTopos.{u + 1, u + 1, u + 1} :=
  Stacks.Cohomology.ringedTopos (smallChartTopology Λ X structureMap)
    (smallAffineSheaf Λ X structureMap)

/-- The horizontal arrow `i : (Sh(C_{X/Λ}), π⁻¹𝒪_X) ⟶ (Sh(C_{X/Λ}), 𝒪)` of Tag 08VA, on the
small model: change of coefficient rings along `i♯`. -/
abbrev smallHorizontal :
    RingedToposSiteHom
      (Stacks.Cohomology.ringedTopos (smallChartTopology Λ X structureMap)
        (smallChartStructureSheaf Λ X structureMap))
      (smallAffineRingedTopos Λ X structureMap) :=
  RingedToposSiteHom.coefficientChange (smallChartTopology Λ X structureMap)
    (smallEvaluation Λ X structureMap)

/-- **The total left derived functor of the module pullback along `i` exists.** -/
theorem hasLeftDerivedFunctor_smallEvaluation :
    (pullbackOnHomotopy (smallHorizontal Λ X structureMap)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u + 1}
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallAffineRingedTopos Λ X structureMap).O))
        (ComplexShape.up ℤ)) :=
  Stacks.Cohomology.hasLeftDerivedFunctor_pullbackOnHomotopy_coefficientChange
    (smallEvaluation Λ X structureMap)

/-- `Li^* : D(𝒪) ⥤ D(π⁻¹𝒪_X)`, the derived pullback of sheaves of modules along the horizontal
arrow of the diagram of Tag 08VA, on the small model of the chart site. -/
abbrev derivedSmallHorizontalPullback :
    DerivedCategory (SheafOfModules.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallAffineRingedTopos Λ X structureMap).O)) ⥤
      DerivedCategory (SheafOfModules.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (Stacks.Cohomology.ringedTopos (smallChartTopology Λ X structureMap)
            (smallChartStructureSheaf Λ X structureMap)).O)) :=
  Stacks.Cohomology.derivedCoefficientChange.{u + 1} (smallEvaluation Λ X structureMap)

end AlgebraicGeometry.PolynomialChart

end
