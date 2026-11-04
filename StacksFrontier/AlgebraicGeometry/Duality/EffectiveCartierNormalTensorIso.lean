module

public import StacksFrontier.AlgebraicGeometry.Duality.EffectiveCartierIdealDualTensor
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.TensorHomTorAmplitudeComparison
import StacksCore.Tactic.StacksAttribute

/-!
# The normal-sheaf formula for derived sheaf Hom along an effective Cartier divisor

Let `X` be a scheme, `D ⊆ X` an effective Cartier divisor with closed immersion `i : D ⟶ X` and
normal sheaf `𝒩`. [Stacks, Tag 0AA4](https://stacks.math.columbia.edu/tag/0AA4) asserts that the
canonical map (48.14.1.1) of [Stacks, Tag 0B4C], combined with the isomorphism
`R ℰom(𝒪_D, 𝒪_X) ≅ 𝒩[-1]` of [Stacks, Tag 0B4B], defines an isomorphism

`Li^*K ⊗^L_{𝒪_D} 𝒩[-1] ⟶ R ℰom(𝒪_D, K)`

functorial in `K` in `D(𝒪_X)`, where `R ℰom(𝒪_D, -)` is the right adjoint of derived pushforward
of [Stacks, Tag 0A76]. **This file proves it**, with no hypothesis beyond those of the source, as
`Stacks.Divisors.normalTensorDerivedSheafHomIso`: an isomorphism of functors
`D(𝒪_X) ⥤ D(𝒪_D)` whose component at `K` is the composite
`Stacks.Divisors.normalTensorDerivedSheafHomMap` that the source forms.

## Main results

* `Stacks.Divisors.isPerfect_pushforwardDerivedStructureSheaf`: `Ri_* 𝒪_D` is a perfect object
  of `D(𝒪_X)`.
* `Stacks.Divisors.isIso_derivedPullbackTensorSheafHomMap`: the map of [Stacks, Tag 0B4C] is an
  isomorphism for every `K`.
* `Stacks.Divisors.isIso_normalTensorDerivedSheafHomMap` and
  `Stacks.Divisors.normalTensorDerivedSheafHomMap_natural`: the map of [Stacks, Tag 0AA4] is an
  isomorphism, natural in `K`.
* `Stacks.Divisors.normalTensorDerivedSheafHomIso`: **[Stacks, Tag 0AA4]**, the isomorphism of
  functors with those components.

## The proof

The source applies `i_*`, where by [Stacks, Tag 0B55] the left-hand side becomes
`K ⊗^L (i_* 𝒩)[-1]` and by [Stacks, Tag 08DQ] the right-hand side becomes
`R ℰom_{𝒪_X}(i_* 𝒪_D, 𝒪_X) ⊗^L K`, `i_* 𝒪_D` being perfect. Here the same computation is made
once for every closed quotient morphism, in
`StacksFrontier/AlgebraicGeometry/Duality/RightAdjointLemmas/TensorHomTorAmplitudeComparison.lean`:
the map of [Stacks, Tag 0B4C] is that of [Stacks, Tag 0E2N] at the structure sheaf between two
constraints of [Stacks, Tag 0FPT], and after `Ri_*` that map is the diagonal of
[Stacks, Tag 0BYS] at the source `Ri_* 𝒪_D`, which is invertible at a perfect source
([Stacks, Tag 0ATN] part (1), the clause of [Stacks, Tag 08DQ] the source uses). What is
particular to an effective Cartier divisor is only that `Ri_* 𝒪_D` is perfect: its class is that
of the two-term complex `(ℐ_D ⟶ 𝒪_X)` of invertible modules
(`Stacks.Divisors.isPerfect_singleFunctor_idealShortComplex_X₃`). Combined with the
isomorphism assertion of [Stacks, Tag 0B4B],
`Stacks.Divisors.isIso_normalSheafShiftToDerivedSheafHomExactSupport`, this gives the tag.

## References

* [Stacks Project, Tag 0AA4](https://stacks.math.columbia.edu/tag/0AA4)
* [Stacks Project, Tag 0B4B](https://stacks.math.columbia.edu/tag/0B4B)
* [Stacks Project, Tag 0B4C](https://stacks.math.columbia.edu/tag/0B4C)
* [Stacks Project, Tag 0B55](https://stacks.math.columbia.edu/tag/0B55)
* [Stacks Project, Tag 08DQ](https://stacks.math.columbia.edu/tag/08DQ)
* [Stacks Project, Tag 0ATN](https://stacks.math.columbia.edu/tag/0ATN)
* [Stacks Project, Tag 0BYS](https://stacks.math.columbia.edu/tag/0BYS)
* [Stacks Project, Tag 0E2N](https://stacks.math.columbia.edu/tag/0E2N)
* [Stacks Project, Tag 0A76](https://stacks.math.columbia.edu/tag/0A76)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory RingedSpaceModuleAdjunction

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace Stacks.Divisors

variable {X : Scheme.{u}} (D : X.IdealSheafData) [IsEffectiveCartierDivisor D]

/-- **`Ri_* 𝒪_D` is a perfect object of `D(𝒪_X)`**, for an effective Cartier divisor `D ⊆ X`.

Derived pushforward along the closed immersion is degreewise pushforward, so `Ri_* 𝒪_D` is the
class of `(i_* 𝒪_D)[0]`, which is perfect by
`Stacks.Divisors.isPerfect_singleFunctor_idealShortComplex_X₃`. -/
theorem isPerfect_pushforwardDerivedStructureSheaf :
    (Stacks.Duality.TensorHomTorAmplitude.ambientRingedSite (closedQuotient D)).IsPerfect
      (Stacks.Duality.TensorHomTorAmplitude.pushforwardDerivedStructureSheaf
        (closedQuotient D)) := by
  obtain ⟨E, hE, ⟨f⟩⟩ := isPerfect_singleFunctor_idealShortComplex_X₃ D
  exact ⟨E, hE, ⟨f ≪≫ (DerivedCategory.singleFunctorIsoCompQ _ 0).app _ ≪≫
    DerivedCategory.Q.mapIso
      (((modulePushforward (closedQuotient D).i).mapCochainComplexSingleFunctor 0).app
        (SheafOfModules.unit (structureSheafRing D.subscheme.toRingedSpace))).symm ≪≫
    ((modulePushforward (closedQuotient D).i).mapDerivedCategoryFactors.app
      (RingedSite.structureSheafComplex
        (Stacks.SheafOfModules.ringedSite (closedQuotient D).Z.sheaf))).symm⟩⟩

/-- **The map of [Stacks, Tag 0B4C] along an effective Cartier divisor is an isomorphism**, for
every `K` in `D(𝒪_X)`:

`Li^*K ⊗^L_{𝒪_D} R ℰom(𝒪_D, 𝒪_X) ⟶ R ℰom(𝒪_D, K)`.

This is
`…ClosedQuotientMorphismOfRingedSpaces.isIso_derivedPullbackTensorSheafHomMap_of_isPerfect`,
`Ri_* 𝒪_D` being perfect by `Stacks.Divisors.isPerfect_pushforwardDerivedStructureSheaf`. -/
theorem isIso_derivedPullbackTensorSheafHomMap (K : DerivedCategory X.Modules) :
    IsIso ((closedQuotient D).derivedPullbackTensorSheafHomMap K) :=
  (closedQuotient D).isIso_derivedPullbackTensorSheafHomMap_of_isPerfect
    (isPerfect_pushforwardDerivedStructureSheaf D) K

/-- **The map of [Stacks, Tag 0AA4] is an isomorphism**, for every `K` in `D(𝒪_X)`: it is the
comparison morphism of [Stacks, Tag 0B4B] tensored with `Li^*K`, an isomorphism by
`Stacks.Divisors.isIso_normalSheafShiftToDerivedSheafHomExactSupport`, followed by the map of
[Stacks, Tag 0B4C], an isomorphism by `Stacks.Divisors.isIso_derivedPullbackTensorSheafHomMap`. -/
theorem isIso_normalTensorDerivedSheafHomMap (K : DerivedCategory X.Modules) :
    IsIso (normalTensorDerivedSheafHomMap D K) :=
  @IsIso.comp_isIso _ _ _ _ _ _ _
    (Iso.isIso_hom (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
        (closedQuotient D).Z.sheaf).obj
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          (closedQuotient D).i).obj K)).mapIso
      (@asIso _ _ _ _ (normalSheafShiftToDerivedSheafHomExactSupport D)
        (isIso_normalSheafShiftToDerivedSheafHomExactSupport D))))
    (isIso_derivedPullbackTensorSheafHomMap D K)

/-- **The map of [Stacks, Tag 0AA4] is natural in `K`.** The tensor product with the comparison
morphism of [Stacks, Tag 0B4B] is a morphism of functors, and the map of [Stacks, Tag 0B4C] is
natural by `…ClosedQuotientMorphismOfRingedSpaces.derivedPullbackTensorSheafHomMap_natural`. -/
theorem normalTensorDerivedSheafHomMap_natural {K L : DerivedCategory X.Modules} (k : K ⟶ L) :
    (normalTensorDerivedPullback D).map k ≫ normalTensorDerivedSheafHomMap D L =
      normalTensorDerivedSheafHomMap D K ≫ (closedQuotient D).derivedSheafHomExactSupport.map k :=
  ((((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
        (closedQuotient D).Z.sheaf).flip.map
      (normalSheafShiftToDerivedSheafHomExactSupport D)).naturality_assoc
    ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (closedQuotient D).i).map k) _).trans
    (congrArg (fun t => _ ≫ t)
      ((closedQuotient D).derivedPullbackTensorSheafHomMap_natural k))).trans
    (Category.assoc _ _ _).symm

/-- **[Stacks, Tag 0AA4].** Let `X` be a scheme and `D ⊆ X` an effective Cartier divisor, with
closed immersion `i : D ⟶ X` and normal sheaf `𝒩`. Then the map (48.14.1.1) of
[Stacks, Tag 0B4C] combined with the isomorphism `R ℰom(𝒪_D, 𝒪_X) ≅ 𝒩[-1]` of
[Stacks, Tag 0B4B] defines an isomorphism

`Li^*K ⊗^L_{𝒪_D} 𝒩[-1] ⟶ R ℰom(𝒪_D, K)`

functorial in `K` in `D(𝒪_X)`.

The isomorphism of functors `D(𝒪_X) ⥤ D(𝒪_D)` below has as component at `K` exactly the
composite `Stacks.Divisors.normalTensorDerivedSheafHomMap` the source forms
(`Stacks.Divisors.normalTensorDerivedSheafHomIso_hom_app`): the comparison morphism
`𝒩[-1] ⟶ R ℰom(𝒪_D, 𝒪_X)` of [Stacks, Tag 0B4B] tensored with `Li^*K`, followed by the map of
[Stacks, Tag 0B4C]. Here `𝒩` is the normal sheaf `Stacks.Divisors.normalSheaf` of the closed
immersion, `R ℰom(𝒪_D, -)` is the right adjoint of derived pushforward of [Stacks, Tag 0A76],
and `Li^*` and `⊗^L` are the derived pullback and derived tensor product of the library. -/
@[stacks 0AA4]
def normalTensorDerivedSheafHomIso :
    normalTensorDerivedPullback D ≅ (closedQuotient D).derivedSheafHomExactSupport :=
  NatIso.ofComponents
    (fun K => @asIso _ _ _ _ (normalTensorDerivedSheafHomMap D K)
      (isIso_normalTensorDerivedSheafHomMap D K))
    (normalTensorDerivedSheafHomMap_natural D)

/-- The components of the isomorphism of [Stacks, Tag 0AA4] are the canonical maps the source
forms. -/
@[simp]
theorem normalTensorDerivedSheafHomIso_hom_app (K : DerivedCategory X.Modules) :
    (normalTensorDerivedSheafHomIso D).hom.app K = normalTensorDerivedSheafHomMap D K :=
  rfl

end Stacks.Divisors

end
