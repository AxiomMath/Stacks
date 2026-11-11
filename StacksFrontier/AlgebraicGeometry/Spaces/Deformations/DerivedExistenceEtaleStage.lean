module

public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.DerivedExistenceSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ConditionComparisons
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteEtaleAtlasQuasiSeparated

/-!
# An étale test space in Situation 0DIK and its infinitesimal stages

In Situation [Stacks, Tag 0DIK] let `j : U ⟶ X` be an étale morphism of algebraic spaces and let
`Uₙ = Xₙ ×_X U` be its `n`-th infinitesimal stage. Then `Uₙ` is also the fibre product
`U ×_{Spec A} Spec Aₙ` and is étale over `Xₙ`, and `U` is flat over `Spec A`, and of finite
presentation over `Spec A` when it is quasi-compact and quasi-separated.

## Main definitions

* `SeparatedDerivedExistenceSystem.etaleStage`: the space `Uₙ = Xₙ ×_X U`.
* `SeparatedDerivedExistenceSystem.etaleStageToStage`,
  `SeparatedDerivedExistenceSystem.etaleStageToSpace`,
  `SeparatedDerivedExistenceSystem.etaleStageBaseProjection`: its projections to `Xₙ`, to `U` and to
  `Spec Aₙ`.

## Main results

* `SeparatedDerivedExistenceSystem.isPullback_etaleStage`: `Uₙ` is the fibre product `Xₙ ×_X U`.
* `SeparatedDerivedExistenceSystem.isPullback_etaleStage_base`: `Uₙ` is also the fibre product
  `U ×_{Spec A} Spec Aₙ`.
* `SeparatedDerivedExistenceSystem.isEtale_etaleStageToStage`: `Uₙ ⟶ Xₙ` is étale.
* `SeparatedDerivedExistenceSystem.isFlat_structure_of_isEtale` and
  `SeparatedDerivedExistenceSystem.isFinitePresentation_structure_of_isEtale`: `U` is flat over
  `Spec A`,
  and of finite presentation over `Spec A` when it is quasi-compact and quasi-separated.

## References

* [Stacks Project, Tag 0DIP](https://stacks.math.columbia.edu/tag/0DIP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.GrothendieckExistence (limitBase baseAt)

universe u

namespace AlgebraicGeometry.Space

namespace SeparatedDerivedExistenceSystem

variable (D : SeparatedDerivedExistenceSystem.{u})
  {U : AlgebraicSpaces D.B (limitBase D.system) D.containsLimitBase} (j : U ⟶ D.X.left)

/-- The `n`-th infinitesimal stage `Uₙ = Xₙ ×_X U` of a space `U` over `X`. -/
abbrev etaleStage (n : ℕ) : AlgebraicSpaces D.B (limitBase D.system) D.containsLimitBase :=
  AlgebraicSpaces.fiberProduct D.B (limitBase D.system) D.containsLimitBase
    (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n) j

/-- The projection `Uₙ ⟶ Xₙ`. -/
abbrev etaleStageToStage (n : ℕ) :
    D.etaleStage j n ⟶ spaceAt D.system D.B D.containsLimitBase D.containsBaseAt D.X n :=
  ObjectProperty.homMk (@pullback.fst _ _ _ _ _
    (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n).hom j.hom
    ((inferInstance : HasPullbacks
      ((BigFppfOver D.B (limitBase D.system) D.containsLimitBase)ᵒᵖ ⥤ Type u)).has_limit _))

/-- The projection `Uₙ ⟶ U`. -/
abbrev etaleStageToSpace (n : ℕ) : D.etaleStage j n ⟶ U :=
  ObjectProperty.homMk (@pullback.snd _ _ _ _ _
    (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n).hom j.hom
    ((inferInstance : HasPullbacks
      ((BigFppfOver D.B (limitBase D.system) D.containsLimitBase)ᵒᵖ ⥤ Type u)).has_limit _))

/-- The structure morphism `Uₙ ⟶ Spec Aₙ`, through `Xₙ`. -/
abbrev etaleStageBaseProjection (n : ℕ) :
    D.etaleStage j n ⟶
      schemeSpace (baseObjectAt D.system D.B D.containsLimitBase D.containsBaseAt n) :=
  D.etaleStageToStage j n ≫
    spaceBaseProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n

/-- `Uₙ` is the fibre product `Xₙ ×_X U`. -/
theorem isPullback_etaleStage (n : ℕ) :
    IsPullback (D.etaleStageToStage j n) (D.etaleStageToSpace j n)
      (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n) j :=
  AlgebraicSpaces.isPullback_fiberProduct D.B (limitBase D.system) D.containsLimitBase _ j

/-- `Uₙ` is the fibre product `U ×_{Spec A} Spec Aₙ`. -/
theorem isPullback_etaleStage_base (n : ℕ) :
    IsPullback (D.etaleStageToSpace j n) (D.etaleStageBaseProjection j n) (j ≫ D.X.hom)
      (baseSpaceProjection D.system D.B D.containsLimitBase D.containsBaseAt n) :=
  (IsPullback.paste_horiz (D.isPullback_etaleStage j n)
    (isPullback_spaceAt D.system D.B D.containsLimitBase D.containsBaseAt D.X n)).flip

variable {j}

/-- If `j : U ⟶ X` is étale, then so is `Uₙ ⟶ Xₙ`. -/
theorem isEtale_etaleStageToStage
    (hj : IsEtale D.B (limitBase D.system) D.containsLimitBase j.hom) (n : ℕ) :
    IsEtale D.B (limitBase D.system) D.containsLimitBase (D.etaleStageToStage j n).hom :=
  isEtale_of_isPullback D.B (limitBase D.system) D.containsLimitBase _ _ _ _
    (D.isPullback_etaleStage j n).flip hj

/-- If `U` is étale over `X`, then `U` is flat over `Spec A`. -/
theorem isFlat_structure_of_isEtale
    (hj : IsEtale D.B (limitBase D.system) D.containsLimitBase j.hom) :
    IsFlat D.B (limitBase D.system) D.containsLimitBase (j ≫ D.X.hom).hom :=
  isFlat_comp D.B (limitBase D.system) D.containsLimitBase U.2 D.X.left.2
    (schemeSpace (limitBaseObject D.system D.B D.containsLimitBase)).2 j.hom D.X.hom.hom
    (isFlat_of_isEtale D.B (limitBase D.system) D.containsLimitBase hj) D.flat

/-- If `U` is étale over `X`, then `U` is locally of finite presentation over `Spec A`. -/
theorem isLocallyOfFinitePresentation_structure_of_isEtale
    (hj : IsEtale D.B (limitBase D.system) D.containsLimitBase j.hom) :
    IsLocallyOfFinitePresentation D.B (limitBase D.system) D.containsLimitBase
      (j ≫ D.X.hom).hom :=
  isLocallyOfFinitePresentation_comp D.B (limitBase D.system) D.containsLimitBase U.2
    D.X.left.2 (schemeSpace (limitBaseObject D.system D.B D.containsLimitBase)).2 j.hom D.X.hom.hom
    (isLocallyOfFinitePresentation_of_isEtale D.B (limitBase D.system) D.containsLimitBase hj)
    D.finitePresentation.1

/-- The base `Spec A`, read as an algebraic space, is quasi-separated. -/
theorem isAbsolutelyQuasiSeparated_limitBase :
    IsAbsolutelyQuasiSeparated D.B (limitBase D.system) D.containsLimitBase
      (BigFppfSite.contains_terminal D.B)
      (schemeSpace (limitBaseObject D.system D.B D.containsLimitBase)).1 :=
  have : IsAffine ((BigFppfOver.toScheme D.B (limitBase D.system) D.containsLimitBase).obj
      (limitBaseObject D.system D.B D.containsLimitBase)) :=
    inferInstanceAs (IsAffine (limitBase D.system))
  isAbsolutelyQuasiSeparated_of_isQuasiSeparatedScheme D.B (limitBase D.system)
    D.containsLimitBase _ (BigFppfSite.contains_terminal D.B)
    ⟨_, inferInstance, ⟨Functor.RepresentableBy.yoneda _⟩⟩

/-- A quasi-compact quasi-separated `U` étale over `X` is of finite presentation over `Spec A`. -/
theorem isFinitePresentation_structure_of_isEtale
    (hj : IsEtale D.B (limitBase D.system) D.containsLimitBase j.hom)
    (hUqc : IsQuasiCompactSpace D.B (limitBase D.system) D.containsLimitBase U.1)
    (hUqs : IsAbsolutelyQuasiSeparated D.B (limitBase D.system) D.containsLimitBase
      (BigFppfSite.contains_terminal D.B) U.1) :
    IsFinitePresentation D.B (limitBase D.system) D.containsLimitBase (j ≫ D.X.hom).hom :=
  ⟨D.isLocallyOfFinitePresentation_structure_of_isEtale hj,
    isQuasiCompact_of_isQuasiCompactSpace D.B (limitBase D.system) D.containsLimitBase
      (BigFppfSite.contains_terminal D.B)
      (schemeSpace (limitBaseObject D.system D.B D.containsLimitBase)).2
      D.isAbsolutelyQuasiSeparated_limitBase hUqc _,
    isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source D.B (limitBase D.system)
      D.containsLimitBase (BigFppfSite.contains_terminal D.B) U.2 hUqs _⟩

end SeparatedDerivedExistenceSystem

end AlgebraicGeometry.Space

end
