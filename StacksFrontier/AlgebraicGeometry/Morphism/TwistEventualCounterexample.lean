module

public import StacksFrontier.AlgebraicGeometry.Morphism.TwistEventual
public import StacksFrontier.AlgebraicGeometry.ProjTwistCompare.NotIsoExampleScheme

/-!
# The maps on twists of Tag 07ZI need not be isomorphisms

Assertion (3) of Stacks Tag 07ZI says that, when `A_d → B_d` is surjective for `d ≫ 0`, the maps
`θ_n : r_ψ^* 𝒪_X(n) ⟶ 𝒪_Y(n)` are surjective "but not isomorphisms in general (even if
`A → B` is surjective)". The surjectivity half is part of
`Stacks.AlgebraicGeometry.Tag07ZGTwistStatement.domain_closedImmersion_twistEpi_of_eventually_epi`.
This file states the second half as an existence statement: there is a scheme `S` and a map
`ψ : A ⟶ B` of quasi-coherent graded `𝒪_S`-algebras which is surjective in every degree, so in
particular satisfies the hypothesis of Tag 07ZI, for which `θ_1` is not an isomorphism.

The witness is the example of
`StacksFrontier.AlgebraicGeometry.ProjTwistCompare.NotIsoExampleScheme` over `S = Spec R` for
`R = ULift ℤ`: `A = R[x, y]/(x²)` with `deg x = 1`, `deg y = 2`, and `B = A/(x)`.

## Main results

* `Stacks.AlgebraicGeometry.Tag07ZGTwistCounterexample.exists_epi_not_isIso_relativeTwistMap`:
  **the second half of Tag 07ZI (3).**

## References

* [Stacks Project, Tag 07ZI](https://stacks.math.columbia.edu/tag/07ZI)
* [Stacks Project, Tag 07ZG](https://stacks.math.columbia.edu/tag/07ZG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjMapDomain
open Stacks.AlgebraicGeometry.Tag07ZGTwist

namespace Stacks.AlgebraicGeometry.Tag07ZGTwistCounterexample

universe u

/-- **[Stacks, Tag 07ZI] (3), second half.** The maps `θ_n : r_ψ^* 𝒪_X(n) ⟶ 𝒪_Y(n)` of Tag 07ZG
are not isomorphisms in general, even if `A → B` is surjective: there are a scheme `S`,
quasi-coherent graded `𝒪_S`-algebras `A` and `B` and a homomorphism `ψ : A ⟶ B` such that every
`ψ_n : A_n ⟶ B_n` is an epimorphism (so the hypothesis of Tag 07ZI holds in every degree), every
`θ_n` is an epimorphism, as the first half of assertion (3) says, and `θ_1` is not an
isomorphism.

The witness is `S = Spec R` for `R = ULift ℤ`, `A = R[x, y]/(x²)` with `deg x = 1`, `deg y = 2`,
`B = A/(x)` and `ψ` the quotient map:
`Stacks.AlgebraicGeometry.ProjTwistCompare.NotIsoExample.epi_sheafHom_app`,
`Stacks.AlgebraicGeometry.Tag07ZGTwist.epi_relativeTwistMap_of_eventually_epi` and
`Stacks.AlgebraicGeometry.ProjTwistCompare.NotIsoExample.not_isIso_relativeTwistMap`. -/
@[stacks 07ZI "(3), second half: the maps θ are surjective but not isomorphisms in general, even
if A → B is surjective — a map ψ of quasi-coherent graded algebras surjective in every degree with
θ₁ not an isomorphism (A = R[x,y]/(x²), deg x = 1, deg y = 2, B = A/(x), on Spec R)"]
theorem exists_epi_not_isIso_relativeTwistMap :
    ∃ (S : Scheme.{u}) (A B : SheafGradedAlgebra S) (ψ : SheafGradedAlgebraHom A B),
      (∀ n : ℤ, Epi (ψ.app n)) ∧ (∀ n : ℤ, Epi (relativeTwistMap ψ n)) ∧
        ¬ IsIso (relativeTwistMap ψ ((1 : ℕ) : ℤ)) :=
  ⟨_, _, _, ProjTwistCompare.NotIsoExample.sheafHom (ULift.{u} ℤ),
    ProjTwistCompare.NotIsoExample.epi_sheafHom_app (ULift.{u} ℤ),
    epi_relativeTwistMap_of_eventually_epi _
      (Filter.Eventually.of_forall fun d =>
        ProjTwistCompare.NotIsoExample.epi_sheafHom_app (ULift.{u} ℤ) (d : ℤ)),
    ProjTwistCompare.NotIsoExample.not_isIso_relativeTwistMap (ULift.{u} ℤ)⟩

end Stacks.AlgebraicGeometry.Tag07ZGTwistCounterexample

end
