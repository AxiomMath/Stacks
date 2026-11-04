module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Localization.BaseChange
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Properties.Regular
public import StacksFrontier.AlgebraicGeometry.Properties.RegularCharacterization
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.ImpliedProperties.LocalDomain
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.ImpliedProperties.RegularSpaceAlterationLocalDomain
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsAlgebra
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralAlteration
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralSpaceProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Normal
public import StacksFrontier.RingTheory.AdicCompletion.Normal
public import StacksFrontier.RingTheory.IntegrallyClosed.Defs
public import StacksFrontier.RingTheory.IntegrallyClosed.Stability
public import StacksFrontier.RingTheory.RegularRing.Defs
public import StacksFrontier.RingTheory.RegularRing.FaithfullyFlatDescent

/-!
# Consequences of a regular algebraic space alteration of a local Noetherian domain

Let `(A, 𝔪, κ)` be a Noetherian local domain and suppose that `Spec A` admits an alteration
`f : X ⟶ Spec A` whose source is a *regular algebraic space*. Then

1. `A` is regular after inverting one nonzero element;
2. the integral closure `B` of `A` in its fraction field is a finite `A`-module;
3. the `𝔪`-adic completion of `B` is a normal ring — equivalently, the completions of `B` at
   its maximal ideals are normal domains;
4. the generic formal fibre `Aˆ ⊗_A Frac(A)` of `A` is regular.

This is the algebraic-space form of the four implied properties; the scheme form, with the same
four conclusions, is in
`StacksFrontier/AlgebraicGeometry/ResolutionOfSurfaces/ImpliedProperties/LocalDomain.lean`.

Write `C = Γ(X, 𝒪_X)` for the ring of compatible families of regular functions on the étale
charts of `X`. Part (1) is the dense regular open of a regular alteration, cut down to a
nonempty basic open `D(a)` of `Spec A` with `Γ(D(a)) = A_a`. For part (2) the integral closure
`B` of `A` in `Frac(A)` is finite because the normalization of `Spec A` is finite
([Stacks, Tag 0BHT]). Part (3) is the two-step comparison `B ⊆ C` of [Stacks, Tag 0BGH], once
normality of `Cˆ` is known. Part (4) inverts `A ∖ {0}` in the completed base change of an affine
étale chart of `X` through the generic point and descends regularity along the faithfully flat
`Frac(A)`-algebra `Frac(A) ⊗_A Γ(V, 𝒪_V)`.

## Main results

* `AlgebraicGeometry.Space.exists_isRegularRing_localizationAway_of_regular_spaceAlteration` —
  part (1).
* `AlgebraicGeometry.Space.module_finite_integralClosure_of_regular_spaceAlteration` — part (2).
* `AlgebraicGeometry.Space.isNormalRing_adicCompletion_integralClosure_of_regular_spaceAlteration`
  — part (3).
* `AlgebraicGeometry.Space.isRegularRing_genericFormalFibre_of_regular_spaceAlteration` —
  part (4).

## Implementation notes

The four parts are aliases of the declarations, proved at the source's hypotheses, of the
module `RegularSpaceAlterationLocalDomain` in this directory, whose module documentation
describes the proofs.

An algebraic space is a presheaf on the big fppf site over `Spec A` together with
`AlgebraicGeometry.IsAlgebraicSpace`; its regularity is the étale-local property
`AlgebraicGeometry.Space.HasEtaleLocalProperty` at `AlgebraicGeometry.IsRegular`, there being no
separate predicate for it, and the alteration is `AlgebraicGeometry.Space.IsAlteration`, which
carries algebraicity and integrality of source and target as conjuncts. The target is `Spec A`
read as the terminal object `Over.mk (𝟙 (B.obj hA))` of that category.

The integral closure of the source is `integralClosure A (FractionRing A)`, and the completion
of part (3) is taken along `(IsLocalRing.maximalIdeal A).map (algebraMap A _)`, matching the
shape in which [Stacks, Tag 0BGH] is stated. Normality of a ring is `IsNormalRing`, the
prime-by-prime form of [Stacks, Tag 00GV], which for a finite algebra over a Noetherian local
ring is exactly normality of the completions at the maximal ideals. The generic formal fibre is
`AdicCompletion 𝔪 A ⊗[A] FractionRing A`: that tensor product is the localization of `Aˆ` at the
image of `A ∖ {0}`, which is the ring of the fibre of `Spec Aˆ ⟶ Spec A` over the generic point.

## References

* [Stacks Project, Tag 0BHU](https://stacks.math.columbia.edu/tag/0BHU)
* [Stacks Project, Tag 0BHT](https://stacks.math.columbia.edu/tag/0BHT)
* [Stacks Project, Tag 0BGH](https://stacks.math.columbia.edu/tag/0BGH)
* [Stacks Project, Tag 0BGT](https://stacks.math.columbia.edu/tag/0BGT)
* [Stacks Project, Tag 0BH3](https://stacks.math.columbia.edu/tag/0BH3)
* [Stacks Project, Tag 0BHQ](https://stacks.math.columbia.edu/tag/0BHQ)
* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
* [Stacks Project, Tag 07NG](https://stacks.math.columbia.edu/tag/07NG)
* [Stacks Project, Tag 08AR](https://stacks.math.columbia.edu/tag/08AR)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open scoped TensorProduct nonZeroDivisors

universe u

/-! ### Ring-theoretic preliminaries -/

/-- The `J`-adic completion of a commutative ring along an ideal of itself: the `J`-adic
completion of `C` as a module over `C`. -/
public abbrev selfAdicCompletion (C : Type*) [CommRing C] (J : Ideal C) : Type _ :=
  AdicCompletion J C




/-- **Normality of the completion of the integral closure from normality of the completion of a
finite integrally closed extension.** For `A` a Noetherian local domain and `C` a finite
integrally closed domain extension of `A`, the integral closure `B` of `A` in `Frac(A)` embeds
into `C` as a finite `A`-algebra and is a normal domain, so [Stacks, Tag 0BGH] carries normality
of the completion of `C` to normality of the completion of `B`. -/
private theorem isNormalRing_adicCompletion_integralClosure_of_finite
    (A : Type u) (C : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    [CommRing C] [IsDomain C] [Algebra A C] [IsIntegrallyClosed C] [Module.Finite A C]
    (hAC : Function.Injective (algebraMap A C))
    (hC : IsNormalRing (selfAdicCompletion C
      ((IsLocalRing.maximalIdeal A).map (algebraMap A C)))) :
    IsNormalRing (selfAdicCompletion ↥(integralClosure A (FractionRing A))
      ((IsLocalRing.maximalIdeal A).map
        (algebraMap A ↥(integralClosure A (FractionRing A))))) := by
  have : Algebra.IsIntegral A C := Algebra.IsIntegral.of_finite A C
  have : IsNormalDomain ↥(integralClosure A (FractionRing A)) :=
    integralClosure_isNormalDomain (R := A) (S := FractionRing A) ⟨inferInstance, inferInstance⟩
  have hBnormal : IsNormalRing ↥(integralClosure A (FractionRing A)) :=
    IsNormalRing.of_isIntegrallyClosed _
  let φ : ↥(integralClosure A (FractionRing A)) →ₐ[A] C :=
    integralClosureToIntegrallyClosed (K := FractionRing A) hAC
  let : Algebra ↥(integralClosure A (FractionRing A)) C := φ.toAlgebra
  have : IsScalarTower A ↥(integralClosure A (FractionRing A)) C :=
    IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  have hinj := integralClosureToIntegrallyClosed_injective (K := FractionRing A) hAC
  have : Module.Finite A ↥(integralClosure A (FractionRing A)) :=
    Module.Finite.of_injective φ.toLinearMap hinj
  exact isNormalRing_adicCompletion_of_finite_injective A
    ↥(integralClosure A (FractionRing A)) C hinj hBnormal hC



namespace AlgebraicGeometry

/-! ### Scheme-theoretic preliminaries -/



namespace Space

/-! ### The global functions of a regular algebraic space alteration -/

/-- The global functions of an alteration of `Spec A` by a regular algebraic space form a normal
domain: the space is normal by [Stacks, Tag 0BGT] and integral by definition of an alteration,
and [Stacks, Tag 0BH3] applies. -/
public alias isNormalDomain_globalFunctions_of_regular_spaceAlteration :=
  isNormalDomain_globalFunctions_of_isAlteration_of_isRegular

/-! ### The implied properties -/

/-- **A Noetherian local domain admitting an alteration by a regular algebraic space is regular
after inverting one nonzero element.** The dense regular open of [Stacks, Tag 0BHT] at the
representable target `Spec A` contains a nonempty basic open `D(a)` of `Spec A`, and
`Γ(D(a)) = A_a`. -/
@[stacks 0BHU "clause (1), regular after inverting one element"]
public alias exists_isRegularRing_localizationAway_of_regular_spaceAlteration :=
  exists_isRegularRing_localizationAway_of_isAlteration_of_isRegular

/-- **The integral closure of a Noetherian local domain admitting an alteration by a regular
algebraic space is a finite module over it.** The normalization of `Spec A` is finite by
[Stacks, Tag 0BHT], and it is the spectrum of the integral closure of `A` in `Frac(A)`
([Stacks, Tag 035P]). -/
@[stacks 0BHU "clause (2), finite integral closure"]
public alias module_finite_integralClosure_of_regular_spaceAlteration :=
  module_finite_integralClosure_of_isAlteration_of_isRegular

/-- **The completion of the integral closure is normal.** With `C = Γ(X, 𝒪_X)` and `B` the
integral closure of `A` in `Frac(A)`, the inclusion `B ⊆ C` is a map of finite `A`-algebras and
`B` is a normal domain, so [Stacks, Tag 0BGH] reduces normality of `Bˆ` to normality of
`Cˆ = Aˆ ⊗_A C`, which is the global functions of the regular base change `X ×_{Spec A} Spec Aˆ`
([Stacks, Tag 073K], [Stacks, Tag 0BHQ]). Normality here is `IsNormalRing`, which for a finite
algebra over a Noetherian local ring is normality of the completions at the maximal ideals. -/
@[stacks 0BHU "clause (3), normal completion of the integral closure"]
public alias isNormalRing_adicCompletion_integralClosure_of_regular_spaceAlteration :=
  isNormalRing_adicCompletion_integralClosure_of_isAlteration_of_isRegular

/-- **The generic formal fibre of a Noetherian local domain admitting an alteration by a regular
algebraic space is regular.** For an affine étale chart `V` of `X` through the generic point the
ring `Aˆ ⊗_A Γ(V, 𝒪_V)` is regular by [Stacks, Tag 0BHQ], and the generic formal fibre is
recovered by inverting `A ∖ {0}` and descending along the faithfully flat `Frac(A)`-algebra
`Frac(A) ⊗_A Γ(V, 𝒪_V)` by [Stacks, Tag 07NG]. -/
@[stacks 0BHU "clause (4), regular generic formal fibre"]
public alias isRegularRing_genericFormalFibre_of_regular_spaceAlteration :=
  isRegularRing_genericFormalFibre_of_isAlteration_of_isRegular

end Space

end AlgebraicGeometry

end
