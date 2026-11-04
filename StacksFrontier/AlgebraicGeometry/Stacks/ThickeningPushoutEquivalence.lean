module

public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningPushoutLocalChart
public import StacksFrontier.AlgebraicGeometry.Stacks.RimSchlessingerOfThickeningPushout
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SchemeAmbient

/-!
# Algebraic stacks and pushouts along thickenings (Stacks 07WN, 07WQ)

Let `𝒵` be an algebraic stack over `S`, and let `Y' = Y ⨿_X X'` be the pushout of a thickening
`X ⟶ X'` and an affine morphism `X ⟶ Y` of schemes over `S`. The functor of fibre categories
`𝒵_{Y'} ⟶ 𝒵_Y ×_{𝒵_X} 𝒵_{X'}` is an equivalence (Stacks 07WN); hence `𝒵` satisfies the
Rim–Schlessinger condition (RS) (Stacks 07WQ).

## References

* [Stacks Project, Tag 07WN](https://stacks.math.columbia.edu/tag/07WN)
* [Stacks Project, Tag 07WQ](https://stacks.math.columbia.edu/tag/07WQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack.ThickeningPushout

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Stacks 07WN, from the representability of the ambient space of a thickening of a scheme. -/
theorem fiberSquareComparison_isEquivalence_of_thickeningRepresentable.{w'}
    (hrep : Space.C1573.ThickeningRepresentableProperty B S hS)
    (𝒵 : BasedCategory.{u, u + 1} (BigFppfOver B S hS))
    (h𝒵 : IsAlgebraicStack.{u, w'} B S hS 𝒵)
    {X X' Y Y' : BigFppfOver B S hS} (i : X ⟶ X') (f : X ⟶ Y) (a : X' ⟶ Y') (b : Y ⟶ Y')
    (w : i ≫ a = f ≫ b)
    (hi : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map i))
    [IsAffineHom ((BigFppfOver.toScheme B S hS).map f)]
    (hsq : IsPushout ((BigFppfOver.toScheme B S hS).map i)
      ((BigFppfOver.toScheme B S hS).map f) ((BigFppfOver.toScheme B S hS).map a)
      ((BigFppfOver.toScheme B S hS).map b)) :
    letI : 𝒵.p.IsFibered := (Classical.choose h𝒵).isFibered
    (Deformation.Artin.fiberSquareComparison 𝒵.p 𝒵.p.chosenPullbacks f i b a
      w.symm).IsEquivalence :=
  fiberSquareComparison_isEquivalence_of_schemeChartLift
    (Space.C1573.schemeChartLiftProperty_of_thickeningRepresentable B S hS hrep) 𝒵 h𝒵 i f a b w hi
    hsq

/-- Stacks 07WQ, from the representability of the ambient space of a thickening of a scheme. -/
theorem satisfiesRS_of_thickeningRepresentable.{w'}
    (hrep : Space.C1573.ThickeningRepresentableProperty B S hS)
    (𝒵 : BasedCategory.{u, u + 1} (BigFppfOver B S hS))
    (h𝒵 : IsAlgebraicStack.{u, w'} B S hS 𝒵) :
    Deformation.Artin.SatisfiesRS B S hS 𝒵.p (Classical.choose h𝒵) :=
  Deformation.Artin.satisfiesRS_of_forall_isEquivalence 𝒵.p (Classical.choose h𝒵)
    (fun i j i' j' w hi hj hpo =>
      have := hj
      fiberSquareComparison_isEquivalence_of_thickeningRepresentable hrep 𝒵 h𝒵 i j i' j' w hi hpo)


/-- Let `Y' = Y ⨿_X X'` be the pushout of a thickening `i : X ⟶ X'` and an affine morphism
`f : X ⟶ Y` of schemes over `S`, and let `𝒵` be an algebraic stack over `S`. The functor of fibre
categories `𝒵_{Y'} ⟶ 𝒵_Y ×_{𝒵_X} 𝒵_{X'}` is an equivalence. -/
@[stacks 07WN]
theorem fiberSquareComparison_isEquivalence.{w'}
    (𝒵 : BasedCategory.{u, u + 1} (BigFppfOver B S hS))
    (h𝒵 : IsAlgebraicStack.{u, w'} B S hS 𝒵)
    {X X' Y Y' : BigFppfOver B S hS} (i : X ⟶ X') (f : X ⟶ Y) (a : X' ⟶ Y') (b : Y ⟶ Y')
    (w : i ≫ a = f ≫ b)
    (hi : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map i))
    [IsAffineHom ((BigFppfOver.toScheme B S hS).map f)]
    (hsq : IsPushout ((BigFppfOver.toScheme B S hS).map i)
      ((BigFppfOver.toScheme B S hS).map f) ((BigFppfOver.toScheme B S hS).map a)
      ((BigFppfOver.toScheme B S hS).map b)) :
    letI : 𝒵.p.IsFibered := (Classical.choose h𝒵).isFibered
    (Deformation.Artin.fiberSquareComparison 𝒵.p 𝒵.p.chosenPullbacks f i b a
      w.symm).IsEquivalence :=
  fiberSquareComparison_isEquivalence_of_thickeningRepresentable
    (fun i hi hX => Space.isRepresentable_of_isThickeningHom_of_isRepresentable B S hS i hi hX)
    𝒵 h𝒵 i f a b w hi hsq

/-- **Stacks 07WQ.** An algebraic stack satisfies the Rim–Schlessinger condition (RS). The
source states this over a locally Noetherian base; the hypothesis is not needed, since the proof
is Stacks 07WN, which holds over any base. -/
@[stacks 07WQ]
theorem satisfiesRS.{w'} (𝒵 : BasedCategory.{u, u + 1} (BigFppfOver B S hS))
    (h𝒵 : IsAlgebraicStack.{u, w'} B S hS 𝒵) :
    Deformation.Artin.SatisfiesRS B S hS 𝒵.p (Classical.choose h𝒵) :=
  satisfiesRS_of_thickeningRepresentable
    (fun i hi hX => Space.isRepresentable_of_isThickeningHom_of_isRepresentable B S hS i hi hX)
    𝒵 h𝒵

end AlgebraicGeometry.Stack.ThickeningPushout

end
