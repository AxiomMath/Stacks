module

public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyRelativeDualizingSheafConstructionMain
public import StacksFrontier.AlgebraicGeometry.Duality.CurveFamilyDualizing.TransitionEtale

/-!
# The relative dualizing sheaf of a prestable family of curves (towards Stacks 0E6P, 0E6Q, 0E6R)

Let `f : X ⟶ S` be a family of curves (Stacks 0D4Z) which is at-worst-nodal of relative dimension
one — for instance a prestable family (Stacks 0E6T). This file assembles the unconditional
construction of its relative dualizing sheaf `ω_{X/S}`:

* on every étale chart `U` of the algebraic space `X` the chosen relative dualizing complex
  `ω^•_{U/S}` of the flat morphism `U ⟶ S` (Stacks 0E2T, 0E2X) is `ω_{U/S}[1]` with `ω_{U/S}`
  invertible (Stacks 0E6P, 0E6R on the chart);
* the canonical identifications of the `ω^•_{U/S}` along the chart squares (Stacks 0E2W, 0E2Y,
  and their étale analogue `AlgebraicGeometry.Scheme.Hom.hasRelDualizingTransition_of_etale`)
  satisfy the cocycle condition, so the `ω_{U/S}` glue to an invertible module `ω_{X/S}` on the
  small étale site of `X`;
* its formation commutes with every morphism of families of curves (a base change), and on the
  fibre over a field-valued point it is the dualizing sheaf of Stacks 0BS2 (through Stacks 0E2Z).

## Main definitions

* `AlgebraicGeometry.CurveFamily.relativeDualizingSheafOfNodal`: `ω_{X/S}`.
* `AlgebraicGeometry.CurveFamily.Hom.relativeDualizingSheafOfNodalPullbackIso`: for a morphism
  of families `φ : F' ⟶ F`, the isomorphism `φ^*ω_{F} ≅ ω_{F'}`.

## Main results

* `AlgebraicGeometry.CurveFamily.isRelativeDualizingSheaf_relativeDualizingSheafOfNodal`: for a
  prestable family, `ω_{X/S}` satisfies `AlgebraicGeometry.CurveFamily.IsRelativeDualizingSheaf`.
* `AlgebraicGeometry.CurveFamily.exists_isRelativeDualizingSheaf_of_isPrestable`: every prestable
  family of curves has a relative dualizing sheaf.

## References

* [Stacks Project, Tag 0E6P](https://stacks.math.columbia.edu/tag/0E6P)
* [Stacks Project, Tag 0E6Q](https://stacks.math.columbia.edu/tag/0E6Q)
* [Stacks Project, Tag 0E6R](https://stacks.math.columbia.edu/tag/0E6R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.CurveFamily

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- The étale-transition input of the construction, which holds unconditionally
(`AlgebraicGeometry.Scheme.Hom.hasRelDualizingTransition_of_etale`). -/
theorem hasRelDualizingTransition_etale {Y T X' : Scheme.{u}} {fY : Y ⟶ T} {f' : X' ⟶ T}
    [Flat fY] [LocallyOfFinitePresentation fY] [Flat f'] [LocallyOfFinitePresentation f']
    (e : X' ⟶ Y) [Etale e] (comm : e ≫ fY = f' ≫ 𝟙 T) :
    Scheme.Hom.HasRelDualizingTransition e (𝟙 T) comm :=
  Scheme.Hom.hasRelDualizingTransition_of_etale e comm

/-- **The relative dualizing sheaf `ω_{X/S}` of a family of curves which is at-worst-nodal of
relative dimension one** (Stacks 0E6Q), glued from the relative dualizing sheaves of the étale
charts of the total space. -/
def relativeDualizingSheafOfNodal (F : CurveFamily B hZ)
    (hF : Space.IsAtWorstNodalOfRelativeDimensionOne B integerBase hZ F.toBase.hom) :
    Space.Modules.{u, u} B integerBase hZ F.total.1 F.total.2 :=
  F.gluedRelativeDualizingSheaf hF hasRelDualizingTransition_etale

/-- **The formation of `ω_{X/S}` commutes with base change** (Stacks 0E6R): for a morphism of
families of curves `φ : F' ⟶ F`, a cartesian square, `φ^*ω_{F} ≅ ω_{F'}`. -/
def Hom.relativeDualizingSheafOfNodalPullbackIso {F' F : CurveFamily B hZ} (φ : F' ⟶ F)
    (hF : Space.IsAtWorstNodalOfRelativeDimensionOne B integerBase hZ F.toBase.hom)
    (hF' : Space.IsAtWorstNodalOfRelativeDimensionOne B integerBase hZ F'.toBase.hom) :
    (Space.modulePullback B integerBase hZ φ.totalMap).obj (F.relativeDualizingSheafOfNodal hF) ≅
      F'.relativeDualizingSheafOfNodal hF' :=
  relativeDualizingSheafPullbackIso φ hF hF' hasRelDualizingTransition_etale

/-- **`ω_{X/S}` is invertible** on the small étale site of the total space (Stacks 0E6R). -/
theorem isInvertible_relativeDualizingSheafOfNodal (F : CurveFamily B hZ)
    (hF : Space.IsAtWorstNodalOfRelativeDimensionOne B integerBase hZ F.toBase.hom) :
    Stacks.SheafOfModules.IsInvertible (Space.structurePresheaf B integerBase hZ F.total.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (Space.smallEtaleRingedSite B integerBase hZ F.total.1 F.total.2).O)).property
      (F.relativeDualizingSheafOfNodal hF) :=
  F.isInvertible_relativeDualizingSheaf hF hasRelDualizingTransition_etale

/-- **The relative dualizing sheaf of a prestable family of curves** (Stacks 0E6P, 0E6Q, 0E6R):
`ω_{X/S}` is invertible and on the fibre over every field-valued point it is the dualizing sheaf
of Stacks 0BS2. -/
theorem isRelativeDualizingSheaf_relativeDualizingSheafOfNodal (X : CurveFamily B hZ)
    (hX : IsPrestableCurveFamily B hZ X) :
    X.IsRelativeDualizingSheaf B hZ (X.relativeDualizingSheafOfNodal hX.1) :=
  X.isRelativeDualizingSheaf_relativeDualizingSheaf hX hasRelDualizingTransition_etale

/-- **Every prestable family of curves has a relative dualizing sheaf** (Stacks 0E6P, 0E6Q,
0E6R). -/
theorem exists_isRelativeDualizingSheaf_of_isPrestable :
    ∀ X : CurveFamily B hZ, IsPrestableCurveFamily B hZ X →
      ∃ ω, X.IsRelativeDualizingSheaf B hZ ω :=
  fun X hX => ⟨_, X.isRelativeDualizingSheaf_relativeDualizingSheafOfNodal hX⟩

end AlgebraicGeometry.CurveFamily

end
