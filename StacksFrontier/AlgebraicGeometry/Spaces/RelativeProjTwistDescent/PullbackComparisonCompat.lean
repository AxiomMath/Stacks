module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.PullbackChartMul
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.TwistAlgebraMul
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.TwistAlgebraUnit

/-!
# Comparisons of quasi-coherent modules carrying multiplications and units

For a morphism `y : V ⟶ U` of the big fppf site and identifications
`Θ : y^*M ≅ M'` of quasi-coherent modules on the schemes of `V` and `U`, this file names the
propositions that `Θ` carries a multiplication `M_i ⊗ M_j ⟶ M_k`, pulled back along `y` and read
through Stacks 01CD, to a multiplication of the `M'`, and a morphism `𝒪 ⟶ M`, pulled back and
read through Stacks 03LU, to a morphism `𝒪 ⟶ M'`.  These are the scheme-level inputs of the
multiplicativity of the isomorphism `θ` of Stacks 085C
(`StacksFrontier/AlgebraicGeometry/Spaces/RelativeProjTwistDescent/BaseChangeThetaGraded.lean`).

## Main definitions

* `AlgebraicGeometry.Space.QuasicoherentPullbackMulCompat`: `Θ` carries a multiplication to a
  multiplication.
* `AlgebraicGeometry.Space.QuasicoherentPullbackUnitCompat`: `Θ` carries a unit to a unit.

## Implementation notes

The propositions are one-field structures (so that their statements are not abstracted into
auxiliary lemmas, as the body of a definition is), stated in a module with the imports of
`StacksFrontier/AlgebraicGeometry/Spaces/RelativeProjTwistDescent/PointTwistGraded.lean`, so that
the
instances of the categories of quasi-coherent modules in their statements are found exactly as in
the comparisons of twists of Tag 01O3 there
(`AlgebraicGeometry.Space.RelativeProjSituation.baseChangeTwistPieceComparison_mul`), which then
prove them as stated.

## References

* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 085C](https://stacks.math.columbia.edu/tag/085C)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A comparison `Θ` of quasi-coherent modules on schemes along `y` carries the multiplication `m`,
pulled back along `y` and read through Stacks 01CD, to the multiplication `m'`. -/
structure QuasicoherentPullbackMulCompat {V U : BigFppfOver B S hS} (y : V ⟶ U)
    {M N K : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory}
    {M' N' K' : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj V).ringCatSheaf).FullSubcategory}
    (m : quasicoherentTensorObj B S hS U M N ⟶ K) (ΘM : quasicoherentPullbackObj B S hS y M ≅ M')
    (ΘN : quasicoherentPullbackObj B S hS y N ≅ N') (ΘK : quasicoherentPullbackObj B S hS y K ≅ K')
    (m' : quasicoherentTensorObj B S hS V M' N' ⟶ K') : Prop where
  /-- The square of multiplications commutes. -/
  eq : (quasicoherentPullbackTensorIso B S hS y M N).inv ≫
      quasicoherentPullbackMap B S hS y m ≫ ΘK.hom =
    quasicoherentTensorHom B S hS V ΘM.hom ΘN.hom ≫ m'

/-- A comparison `Θ` of quasi-coherent modules on schemes along `y` carries `ν : 𝒪 ⟶ K`, pulled
back along `y` and read through Stacks 03LU, to `ν' : 𝒪 ⟶ K'`. -/
structure QuasicoherentPullbackUnitCompat {V U : BigFppfOver B S hS} (y : V ⟶ U)
    {K : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory}
    {K' : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj V).ringCatSheaf).FullSubcategory}
    (ν : quasicoherentUnitObj B S hS U ⟶ K) (ΘK : quasicoherentPullbackObj B S hS y K ≅ K')
    (ν' : quasicoherentUnitObj B S hS V ⟶ K') : Prop where
  /-- The triangle of units commutes. -/
  eq : (quasicoherentPullbackUnitIso B S hS y).inv ≫ quasicoherentPullbackMap B S hS y ν ≫ ΘK.hom =
    ν'

end AlgebraicGeometry.Space

end
