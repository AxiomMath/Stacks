module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleRankOne.SiteConverse
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDirectImageEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.LaurentAlgebraQuasicoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.MultiplicativeTorsorOfInvertible
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleLocallyRinged

/-!
# Stacks 08AI for the projection of the multiplicative torsor

In Situation 0EDT let `X/B` be good, let `ℒ` be an invertible `𝒪_X`-module and let
`q : T = \underline{Spec}_X(⨁_{n ∈ ℤ} ℒ^{⊗ n}) ⟶ X` be the projection of its multiplicative
torsor.

## Main results

* `AlgebraicGeometry.Space.affineDirectImageEquivalence_multiplicativeTorsorProjection`:
  **Stacks 08AI holds for `q`**, with
  `AlgebraicGeometry.Space.multiplicativeTorsorDirectImageEquivalence` the equivalence
  `QCoh(𝒪_T) ≌ QCoh(q_*𝒪_T)` itself.

## References

* [Stacks Project, Tag 08AI](https://stacks.math.columbia.edu/tag/08AI)
* [Stacks Project, Tag 0EQG](https://stacks.math.columbia.edu/tag/0EQG)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (p : X ⟶ D.space) (hp : D.IsGood p)
    (L : Modules.{u, u} D.site D.base D.base_mem X hp.1)
    (hL : IsInvertibleSheaf D p hp L)

variable (E : AffineAlgebraAntiEquivalence D.site D.base D.base_mem)

/-- **Stacks 08AI holds for the projection `q : T ⟶ X` of the multiplicative torsor of `ℒ`**:
direct image over `q_*𝒪_T` carries the quasi-coherent `𝒪_T`-modules to the quasi-coherent
`q_*𝒪_T`-modules and is an equivalence onto them. -/
theorem affineDirectImageEquivalence_multiplicativeTorsorProjection :
    AffineDirectImageEquivalence D.site D.base D.base_mem
      (multiplicativeTorsorProjection D p hp L hL E
        (isQuasicoherent_laurentAlgebraSheaf D p hp L hL)) :=
  affineDirectImageEquivalence_of_isAffineHom D.site D.base D.base_mem _
    (isAffineHom_multiplicativeTorsorProjection D p hp L hL E)

/-- **The equivalence `QCoh(𝒪_T) ≌ QCoh(q_*𝒪_T)` of Stacks 08AI at the projection
`q : T ⟶ X`** of the multiplicative torsor of `ℒ`, with functor `ℱ ↦ q_*ℱ`.  Its coefficient
ring on the right is `q_*𝒪_T`, which
`AlgebraicGeometry.Space.relativeSpecPushforwardIso` identifies with `⨁_{n ∈ ℤ} ℒ^{⊗ n}`. -/
def multiplicativeTorsorDirectImageEquivalence :
    QuasicoherentSheaves.{u, u} D.site D.base D.base_mem
        (multiplicativeTorsorSpace D p hp L hL E
          (isQuasicoherent_laurentAlgebraSheaf D p hp L hL)).1
        (multiplicativeTorsorSpace D p hp L hL E
          (isQuasicoherent_laurentAlgebraSheaf D p hp L hL)).2 ≌
      (SheafOfModules.isQuasicoherentOnSite (affineDirectImageAlgebra D.site D.base D.base_mem
        (multiplicativeTorsorProjection D p hp L hL E
          (isQuasicoherent_laurentAlgebraSheaf D p hp L hL)))).FullSubcategory :=
  affineQuasicoherentDirectImageEquivalence D.site D.base D.base_mem _
    (isAffineHom_multiplicativeTorsorProjection D p hp L hL E)

end AlgebraicGeometry.Space

end
