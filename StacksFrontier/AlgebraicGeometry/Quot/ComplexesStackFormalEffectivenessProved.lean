module

public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackAlgebraicStackProved

/-!
# Strong formal effectiveness of `Complexes_{X/S}`

Let `S` be a locally Noetherian scheme and `f : X ⟶ S` a proper, flat morphism of finite
presentation from an algebraic space (Situation 0DLE with `B = S`). Then
`p : Complexes_{X/S} ⟶ (Sch/S)_fppf` satisfies strong formal effectiveness in the sense of
Stacks 0CXT: every system `(ξ_n)` of objects over a tower `Spec R_n` of `Λ`-algebras, with
surjective transition maps whose kernels are locally nilpotent, is effective over
`Spec (lim R_n)`.

## Main results

* `AlgebraicGeometry.Space.ComplexesSituation.isStronglyFormallyEffective_complexes_proved`:
  `Complexes_{X/S} ⟶ (Sch/S)_fppf` is strongly formally effective.

## Implementation notes

`B = S` is the hypothesis that the target `Y` of the situation is a terminal algebraic space over
`S`.

## References

* [Stacks Project, Tag 0DLM](https://stacks.math.columbia.edu/tag/0DLM)
* [Stacks Project, Tag 0CXT](https://stacks.math.columbia.edu/tag/0CXT)
* [Stacks Project, Tag 0DIQ](https://stacks.math.columbia.edu/tag/0DIQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Deformation.Artin

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace AlgebraicGeometry.Space.ComplexesSituation

attribute [local instance] AlgebraicGeometry.Space.instModulesHasDerivedCategory complexesCategory

variable {B : BigFppfSite.{u}}

/-- `Complexes_{X/S}` is strongly formally effective: in a `ComplexesSituation` whose target `Y`
of `f : X ⟶ Y` is terminal over `S`, with `S` locally Noetherian, the functor
`p : Complexes_{X/S} ⟶ (Sch/S)_fppf` is strongly formally effective. -/
@[stacks 0DLM]
theorem isStronglyFormallyEffective_complexes_proved {S : Scheme.{u}} {hS : B.Contains S}
    (D : ComplexesSituation B S hS) [_root_.AlgebraicGeometry.IsLocallyNoetherian S]
    (hY : IsTerminal D.Y) :
    IsStronglyFormallyEffective B S hS (complexesFunctor D)
      (complexesFunctor_isFiberedInGroupoids D) :=
  D.isStronglyFormallyEffective_complexes_of_specLimitTower
    (fun L K hK φ hφ => L.exists_restriction_proved K hK φ hφ) hY

end AlgebraicGeometry.Space.ComplexesSituation

end
