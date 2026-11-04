module

public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyRelativeDualizingSheafConstructionPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeModuleSystem.PullbackGlobal

/-!
# The relative dualizing sheaf of a prestable family of curves

Let `f : X ⟶ S` be a prestable family of curves (Stacks 0E6T). The module `ω_{X/S}` glued from
the relative dualizing sheaves of the étale charts of `X`
(`AlgebraicGeometry.CurveFamily.gluedRelativeDualizingSheaf`) is a relative dualizing sheaf in the
sense of `AlgebraicGeometry.CurveFamily.IsRelativeDualizingSheaf` (Stacks 0E6P, 0E6Q, 0E6R): it is
invertible, its formation commutes with base change along morphisms of families
(`AlgebraicGeometry.CurveFamily.relativeDualizingSheafPullbackIso`), and on the fibre over a
field-valued point it is the dualizing sheaf of the fibre (Stacks 0BS2).

The transitions of chart squares whose gap map is étale over the identity of the base are taken as
the hypothesis `hEt`, as in
`StacksFrontier/AlgebraicGeometry/Quot/CurveFamilyRelativeDualizingSheafConstruction.lean`.

## Main definitions

* `AlgebraicGeometry.CurveFamily.relativeDualizingSheafPullbackIso`: `φ^*ω_{X/S} ≅ ω_{X'/S'}` for
  a morphism of nodal families `φ : F' ⟶ F`.

## Main results

* `AlgebraicGeometry.CurveFamily.isRelativeDualizingSheaf_relativeDualizingSheaf`: **`ω_{X/S}` is
  a relative dualizing sheaf of a prestable family.**
* `AlgebraicGeometry.CurveFamily.exists_isRelativeDualizingSheaf`: every prestable family has a
  relative dualizing sheaf.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.CurveFamily

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- **The formation of the relative dualizing sheaf commutes with base change**: for a morphism
of nodal families of curves `φ : F' ⟶ F`, the pullback of `ω_{X/S}` along the morphism of total
spaces is `ω_{X'/S'}`. It is glued from the comparisons of the relative dualizing sheaves of the
charts on the chart squares of the morphism of total spaces. -/
def relativeDualizingSheafPullbackIso {F' F : CurveFamily B hZ} (φ : F' ⟶ F)
    (hF : Space.IsAtWorstNodalOfRelativeDimensionOne B integerBase hZ F.toBase.hom)
    (hF' : Space.IsAtWorstNodalOfRelativeDimensionOne B integerBase hZ F'.toBase.hom)
    (hEt : ∀ {Y T X' : Scheme.{u}} {fY : Y ⟶ T} {f' : X' ⟶ T} [Flat fY]
      [LocallyOfFinitePresentation fY] [Flat f'] [LocallyOfFinitePresentation f'] (e : X' ⟶ Y)
      [Etale e] (comm : e ≫ fY = f' ≫ 𝟙 T), Scheme.Hom.HasRelDualizingTransition e (𝟙 T) comm) :
    (Space.modulePullback B integerBase hZ φ.totalMap).obj (F.gluedRelativeDualizingSheaf hF hEt) ≅
      F'.gluedRelativeDualizingSheaf hF' hEt :=
  (F.dualizingSystem hF hEt).modulePullbackGlueIso φ.totalMap (F'.dualizingSystem hF' hEt)
    (φ.dualizingComparison hF hEt) (φ.comparisonCompatTarget_dualizingComparison hF hF' hEt)
    (φ.comparisonCompatSource_dualizingComparison hF hF' hEt)

/-- **The relative dualizing sheaf of a prestable family of curves** (Stacks 0E6P, 0E6Q, 0E6R):
`ω_{X/S}` is invertible, and on the fibre over every field-valued point of the base it is the
dualizing sheaf of the fibre. The fibre is the total space of the fibre family, a base change of
the family; the pullback of `ω_{X/S}` to it is the relative dualizing sheaf of the fibre family
(`AlgebraicGeometry.CurveFamily.relativeDualizingSheafPullbackIso`), which on the identity chart
of the fibre is its dualizing sheaf. -/
theorem isRelativeDualizingSheaf_relativeDualizingSheaf (X : CurveFamily B hZ)
    (hX : IsPrestableCurveFamily B hZ X)
    (hEt : ∀ {Y T X' : Scheme.{u}} {fY : Y ⟶ T} {f' : X' ⟶ T} [Flat fY]
      [LocallyOfFinitePresentation fY] [Flat f'] [LocallyOfFinitePresentation f'] (e : X' ⟶ Y)
      [Etale e] (comm : e ≫ fY = f' ≫ 𝟙 T), Scheme.Hom.HasRelDualizingTransition e (𝟙 T) comm) :
    X.IsRelativeDualizingSheaf B hZ (X.gluedRelativeDualizingSheaf hX.1 hEt) := by
  refine ⟨X.isInvertible_relativeDualizingSheaf hX.1 hEt, fun p V v q hsq => ?_⟩
  have hproper := X.isProper_fibre hsq
  refine ⟨hproper, ?_⟩
  have hFib := isAtWorstNodal_of_hom (X.fibreFamilyHom hsq) hX.1
  exact X.nonempty_baseChangeModule_iso_of_fibrePullbackIso hsq hFib hEt _
    (relativeDualizingSheafPullbackIso (X.fibreFamilyHom hsq) hX.1 hFib hEt)

/-- **Every prestable family of curves has a relative dualizing sheaf** (Stacks 0E6R), given the
transitions of chart squares whose gap map is étale over the identity of the base. -/
theorem exists_isRelativeDualizingSheaf
    (hEt : ∀ {Y T X' : Scheme.{u}} {fY : Y ⟶ T} {f' : X' ⟶ T} [Flat fY]
      [LocallyOfFinitePresentation fY] [Flat f'] [LocallyOfFinitePresentation f'] (e : X' ⟶ Y)
      [Etale e] (comm : e ≫ fY = f' ≫ 𝟙 T), Scheme.Hom.HasRelDualizingTransition e (𝟙 T) comm) :
    ∀ X : CurveFamily B hZ, IsPrestableCurveFamily B hZ X →
      ∃ ω, X.IsRelativeDualizingSheaf B hZ ω :=
  fun X hX => ⟨_, X.isRelativeDualizingSheaf_relativeDualizingSheaf hX hEt⟩

end AlgebraicGeometry.CurveFamily

end
